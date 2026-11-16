import Langlands.Geometry.Building.QuasiSplitValuedRankOneCoordinatesStatement
import Langlands.Geometry.Building.KPLocalCoordinateCharacterCongruence
import Langlands.Geometry.Building.KPLocalTorusRootCommutatorStatement
import Langlands.Geometry.Building.IntegerRootReflections
import Langlands.GroupScheme.Rational.RootFactorizationFromExistence
import Langlands.GroupScheme.Examples.SU3RootScalingCommutator
import Langlands.GroupScheme.Examples.SU3RootParametersTowerValuation

/-! # Positive-depth torus commutators from valued rank-one coordinates

The positive-depth torus action on root-group filtrations over `K = F^ur`
(`KPLocalTorusRootCommutatorStatement`) follows from the existence of valued rank-one
coordinates (`QuasiSplitValuedRankOneCoordinatesStatement`).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false

/-! ### Commutators in an apartment, from scaling coordinates -/

namespace Langlands.Geometry.Building

/-- Moving a real shift across an inequality in `WithTop ℝ`. -/
theorem coe_le_add_coe_iff_coe_sub_le (a c : ℝ) (X : WithTop ℝ) :
    (a : WithTop ℝ) ≤ X + (c : WithTop ℝ) ↔ ((a - c : ℝ) : WithTop ℝ) ≤ X := by
  induction X using WithTop.recTopCoe with
  | top => simp
  | coe x =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
    constructor <;> intro h <;> linarith

/-- A valuation with `r ≤ w(χ - 1)` for some `r ≥ 0` is nonnegative at `χ`. -/
theorem addValuation_nonneg_of_coe_le_sub_one {L : Type*} [Field L]
    (w : AddValuation L (WithTop ℝ)) {χ : L} {r : ℝ} (hr0 : 0 ≤ r)
    (hχ : (r : WithTop ℝ) ≤ w (χ - 1)) : (0 : WithTop ℝ) ≤ w χ := by
  have h := w.map_add (χ - 1) 1
  rw [sub_add_cancel, w.map_one] at h
  exact le_trans (le_min (le_trans (WithTop.coe_nonneg.mpr hr0) hχ) le_rfl) h

namespace KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- Two points of the apartment differ by a translation of `V(S)`. -/
theorem exists_val_eq_add_eval (x y : D.Apartment) :
    ∃ v : V S, ∀ (a : characterLattice S) (g : rationalPoints G),
      x.val a g = y.val a g + ((eval S a v : ℝ) : WithTop ℝ) := by
  obtain ⟨v, hv⟩ := D.equipollent_of_mem y.mem x.mem
  exact ⟨v, fun a g => by rw [hv, RootFunctionFamily.vadd_apply]⟩

/-- Field coordinates `e : E → U_b(k)` on which `z` acts by multiplication by `χ`, with
`x_b(e(τ)) = w(τ) + β`: for `r ≤ w(χ - 1)` the commutator of `z` with `U_{b,x,s}` lies in
`U_{b,x,r+s}`. -/
theorem commutator_mem_filtration_of_fieldScaling {E : Type*} [Field E]
    (w : AddValuation E (WithTop ℝ)) {b : characterLattice S}
    (e : Multiplicative E ≃* rootGroupPoints i b) (x : D.Apartment) (β : ℝ)
    (hval : ∀ τ : E, x.val b (e (Multiplicative.ofAdd τ) : rationalPoints G) =
      w τ + (β : WithTop ℝ))
    {z : rationalPoints G} {χ : E} {r s : ℝ} (hχ : (r : WithTop ℝ) ≤ w (χ - 1))
    (hconj : ∀ τ : E, z * (e (Multiplicative.ofAdd τ) : rationalPoints G) * z⁻¹ =
      (e (Multiplicative.ofAdd (χ * τ)) : rationalPoints G))
    {u : rationalPoints G} (hu : u ∈ D.filtration x b s) :
    z * u * z⁻¹ * u⁻¹ ∈ D.filtration x b (r + s) := by
  obtain ⟨hu1, hu2⟩ := KPApartmentData.mem_filtration.mp hu
  obtain ⟨τ, rfl⟩ : ∃ τ : E, (e (Multiplicative.ofAdd τ) : rationalPoints G) = u :=
    ⟨Multiplicative.toAdd (e.symm ⟨u, hu1⟩), by simp⟩
  have hm : Multiplicative.ofAdd (χ * τ) * (Multiplicative.ofAdd τ)⁻¹ =
      Multiplicative.ofAdd ((χ - 1) * τ) := by
    rw [← ofAdd_neg, ← ofAdd_add, sub_mul, one_mul, sub_eq_add_neg]
  rw [hconj, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← map_inv, ← map_mul, hm]
  refine KPApartmentData.mem_filtration.mpr ⟨Subtype.prop _, ?_⟩
  rw [hval] at hu2 ⊢
  rw [w.map_mul, WithTop.coe_add, add_assoc]
  exact add_le_add hχ hu2

open SU3Root in
/-- Unitary coordinates `e : Parameters c → U_b(k)` on which `z` acts by `scale χ`, whose
central part is `U_{2b}(k)`, with `x_b(e(p)) = depthA(p) + β` and
`x_{2b}(e(q)) = w(q.second) + 2β` on central `q`: for `r ≤ w(χ - 1)` the commutator of
`z` with `U_{b,x,s}` lies in the block `U_{b,x,r+s} U_{2b,x,r+s}`. -/
theorem commutator_mem_filtrationBlock_of_unitaryScaling {L : Type*} [Field L]
    {c : RingInvolution L} (w : AddValuation L (WithTop ℝ))
    (hinv : ∀ y : L, w (c.bar y) = w y) {b : characterLattice S}
    (h2 : 2 • b ∈ relativeRoots i) (e : Parameters c ≃* rootGroupPoints i b)
    (hdouble : ∀ g : rationalPoints G, g ∈ rootGroupPoints i (2 • b) ↔
      ∃ p ∈ Parameters.central c, (e p : rationalPoints G) = g)
    (x : D.Apartment) (β : ℝ)
    (hval : ∀ p : Parameters c, x.val b (e p : rationalPoints G) =
      Parameters.depthA w p + (β : WithTop ℝ))
    (hval2 : ∀ p ∈ Parameters.central c, x.val (2 • b) (e p : rationalPoints G) =
      w p.second + ((2 * β : ℝ) : WithTop ℝ))
    {z : rationalPoints G} {χ : L} {r s : ℝ} (hs0 : 0 ≤ s)
    (hχ : (r : WithTop ℝ) ≤ w (χ - 1))
    (hconj : ∀ p : Parameters c, z * (e p : rationalPoints G) * z⁻¹ =
      (e (Parameters.scale χ p) : rationalPoints G))
    {u : rationalPoints G} (hu : u ∈ D.filtration x b s) :
    z * u * z⁻¹ * u⁻¹ ∈ D.filtrationBlock x (fun _ => r + s) b := by
  obtain ⟨hu1, hu2⟩ := KPApartmentData.mem_filtration.mp hu
  obtain ⟨p, rfl⟩ : ∃ p : Parameters c, (e p : rationalPoints G) = u :=
    ⟨e.symm ⟨u, hu1⟩, by simp⟩
  rw [hval, coe_le_add_coe_iff_coe_sub_le] at hu2
  obtain ⟨q, hq, y, hy, heq⟩ := Parameters.scale_mul_inv_mem_filtration_product w hinv χ p r
    (s - β) hχ ((Parameters.mem_filtration_iff_depth w hinv _ p).mpr hu2)
  have hy' := (Parameters.mem_centralFiltration w hinv _ y).mp hy
  have hcentral : y ∈ Parameters.central c := (Parameters.mem_central y).mpr hy'.1
  have hsub : e (Parameters.scale χ p) * (e p)⁻¹ = e q * e y := by
    rw [← map_inv, ← map_mul e (Parameters.scale χ p), heq, map_mul]
  have hsplit : z * (e p : rationalPoints G) * z⁻¹ * (e p : rationalPoints G)⁻¹ =
      (e q : rationalPoints G) * (e y : rationalPoints G) := by
    rw [hconj]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val hsub
  have h1 : (e q : rationalPoints G) ∈ D.filtration x b (r + s) := by
    refine KPApartmentData.mem_filtration.mpr ⟨Subtype.prop _, ?_⟩
    rw [hval, coe_le_add_coe_iff_coe_sub_le]
    have hq' := (Parameters.mem_filtration_iff_depth w hinv _ q).mp hq
    rwa [add_sub_assoc]
  have h2' : (e y : rationalPoints G) ∈ D.doubleFiltration x b (r + s) := by
    rw [D.doubleFiltration_of_mem x b _ h2]
    refine KPApartmentData.mem_filtration.mpr ⟨(hdouble _).mpr ⟨y, hcentral, rfl⟩, ?_⟩
    rw [hval2 y hcentral, coe_le_add_coe_iff_coe_sub_le]
    exact le_trans (WithTop.coe_le_coe.mpr (by linarith)) hy'.2
  rw [hsplit]
  exact D.mem_filtrationBlock.mpr ⟨_, h1, _, h2', rfl⟩

open SU3Root in
/-- Unitary coordinates as above, on the double root: the commutator of `z` with
`U_{2b,x,s}` lies in the block of `2b` at depth `r + s`. -/
theorem commutator_mem_filtrationBlock_double_of_unitaryScaling {L : Type*} [Field L]
    {c : RingInvolution L} (w : AddValuation L (WithTop ℝ))
    (hinv : ∀ y : L, w (c.bar y) = w y) {b : characterLattice S}
    (e : Parameters c ≃* rootGroupPoints i b)
    (hdouble : ∀ g : rationalPoints G, g ∈ rootGroupPoints i (2 • b) ↔
      ∃ p ∈ Parameters.central c, (e p : rationalPoints G) = g)
    (x : D.Apartment) (shift : ℝ)
    (hval2 : ∀ p ∈ Parameters.central c, x.val (2 • b) (e p : rationalPoints G) =
      w p.second + (shift : WithTop ℝ))
    {z : rationalPoints G} {χ : L} {r s : ℝ} (hr0 : 0 ≤ r)
    (hχ : (r : WithTop ℝ) ≤ w (χ - 1))
    (hconj : ∀ p : Parameters c, z * (e p : rationalPoints G) * z⁻¹ =
      (e (Parameters.scale χ p) : rationalPoints G))
    {u : rationalPoints G} (hu : u ∈ D.filtration x (2 • b) s) :
    z * u * z⁻¹ * u⁻¹ ∈ D.filtrationBlock x (fun _ => r + s) (2 • b) := by
  obtain ⟨hu1, hu2⟩ := KPApartmentData.mem_filtration.mp hu
  obtain ⟨q, hqc, rfl⟩ := (hdouble u).mp hu1
  rw [hval2 q hqc, coe_le_add_coe_iff_coe_sub_le] at hu2
  have hq' : Parameters.scale χ q * q⁻¹ ∈ Parameters.centralFiltration w hinv (r + (s - shift)) :=
    Parameters.scale_mul_inv_mem_centralFiltration w hinv χ q r (s - shift)
      (addValuation_nonneg_of_coe_le_sub_one w hr0 hχ) hχ
      ((Parameters.mem_centralFiltration w hinv _ q).mpr ⟨(Parameters.mem_central q).mp hqc, hu2⟩)
  have hq'' := (Parameters.mem_centralFiltration w hinv _ _).mp hq'
  have hc : Parameters.scale χ q * q⁻¹ ∈ Parameters.central c :=
    (Parameters.mem_central _).mpr hq''.1
  have hcomm : z * (e q : rationalPoints G) * z⁻¹ * (e q : rationalPoints G)⁻¹ =
      (e (Parameters.scale χ q * q⁻¹) : rationalPoints G) := by
    rw [hconj, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have h1 : (e (Parameters.scale χ q * q⁻¹) : rationalPoints G) ∈
      D.filtration x (2 • b) (r + s) := by
    refine KPApartmentData.mem_filtration.mpr ⟨(hdouble _).mpr ⟨_, hc, rfl⟩, ?_⟩
    rw [hval2 _ hc, coe_le_add_coe_iff_coe_sub_le, add_sub_assoc]
    exact hq''.2
  rw [hcomm]
  exact D.mem_filtrationBlock.mpr ⟨_, h1, 1, Subgroup.one_mem _, mul_one _⟩

end KPApartmentData

/-! ### The case analysis over `K = F^ur` -/

namespace KPLocalTorusRootCommutator

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
  (B : MaximalUnramified.BuildingData F H)

/-- Every relative root is an indivisible root or twice an indivisible root. -/
theorem exists_indivisible_eq_or_double {a : characterLattice B.S}
    (ha : a ∈ relativeRoots B.i) :
    ∃ b ∈ RelativeRoot.indivisibleRoots B.i,
      a = b ∨ (a = 2 • b ∧ 2 • b ∈ relativeRoots B.i) := by
  let _ := B.isConnectedReductive.smooth
  have hS : IsSplitTorus B.S.toGrp := B.isMaximalSplitTorus.isSplitSubtorus.1
  have hmult : ∀ {c : characterLattice B.S} {n : ℕ}, n • c ∈ relativeRoots B.i →
      n = 1 ∨ n = 2 :=
    fun hn => B.hasOppositeFactorPairs.eq_one_or_two_of_nsmul_mem B.i hS hn
  by_cases hind : a ∈ RelativeRoot.indivisibleRoots B.i
  · exact ⟨a, hind, Or.inl rfl⟩
  have hdiv : ∃ b ∈ relativeRoots B.i, ∃ m : ℕ, 1 < m ∧ m • b = a := by
    by_contra hne
    push Not at hne
    exact hind (show a ∈ relativeRoots B.i ∧
      ∀ b ∈ relativeRoots B.i, ∀ m : ℕ, 1 < m → m • b ≠ a from ⟨ha, hne⟩)
  obtain ⟨b, hb, m, hm, hmb⟩ := hdiv
  have hm2 : m = 2 := by
    rcases hmult (show m • b ∈ relativeRoots B.i by rw [hmb]; exact ha) with h | h
    · omega
    · exact h
  subst hm2
  refine ⟨b, (show b ∈ relativeRoots B.i ∧
      ∀ b' ∈ relativeRoots B.i, ∀ m : ℕ, 1 < m → m • b' ≠ b from ⟨hb, ?_⟩),
    Or.inr ⟨hmb.symm, by rw [hmb]; exact ha⟩⟩
  intro b' _ m' hm' hmb'
  rcases hmult (show (m' * 2) • b' ∈ relativeRoots B.i by
    rw [mul_nsmul, hmb', hmb]; exact ha) with h | h <;> omega

variable {B} {hZ : IsTorus B.centralizer.Z}

/-- The case of a nonmultipliable indivisible root, from valued SL2 coordinates. -/
theorem commutator_mem_filtration_sl2 {b : characterLattice B.S}
    (C : ValuedSL2RootCoordinates B hZ b) (x : B.Apartment) {r s : ℝ≥0}
    {t : rationalPoints (B.centralizerTorus hZ).toGrp}
    (ht : t ∈ localGeometricCharacterCongruence F (B.centralizerTorus hZ) r)
    {u : rationalPoints H} (hu : u ∈ B.filtration x b s) :
    rationalPoints.map B.centralizer.j t * u * (rationalPoints.map B.centralizer.j t)⁻¹ *
        u⁻¹ ∈ B.filtration x b ((r + s : ℝ≥0) : ℝ) := by
  obtain ⟨v, hv⟩ := B.apartment.exists_val_eq_add_eval x C.origin
  rw [NNReal.coe_add]
  exact B.apartment.commutator_mem_filtration_of_fieldScaling
    (FieldTheory.henselianSeparableAddValuation (MaximalUnramified.valuation F)
      (MaximalUnramified.valuationSubring_isHenselian F) C.extension)
    C.positive.equiv x (eval B.S b v) (fun τ => by rw [hv, C.depth_positive])
    ((LocalField.mem_addValuationUnitFiltration _ _ _).mp
      (coordinateCharacter_mem_unitFiltration F (B.centralizerTorus hZ)
        (MaximalUnramified.valuationSubring_isHenselian F) ht C.positive.character)).2
    (C.positive.conjugation t) hu

/-- The case of a multipliable indivisible root, from valued SU3 coordinates. -/
theorem commutator_mem_filtrationBlock_su3 {b : characterLattice B.S}
    (C : ValuedSU3RootCoordinates B hZ b) (h2 : 2 • b ∈ relativeRoots B.i)
    (x : B.Apartment) {r s : ℝ≥0}
    {t : rationalPoints (B.centralizerTorus hZ).toGrp}
    (ht : t ∈ localGeometricCharacterCongruence F (B.centralizerTorus hZ) r)
    {u : rationalPoints H} (hu : u ∈ B.filtration x b s) :
    rationalPoints.map B.centralizer.j t * u * (rationalPoints.map B.centralizer.j t)⁻¹ *
        u⁻¹ ∈ B.apartment.filtrationBlock x (fun _ => ((r + s : ℝ≥0) : ℝ)) b := by
  obtain ⟨v, hv⟩ := B.apartment.exists_val_eq_add_eval x C.origin
  rw [NNReal.coe_add]
  exact B.apartment.commutator_mem_filtrationBlock_of_unitaryScaling
    (FieldTheory.henselianSeparableAddValuation (MaximalUnramified.valuation F)
      (MaximalUnramified.valuationSubring_isHenselian F) C.extension)
    (SU3Root.henselianSeparableAddValuation_quadratic_bar (UnramifiedClosure F) C.base
      C.extension (MaximalUnramified.valuation F)
      (MaximalUnramified.valuationSubring_isHenselian F))
    h2 C.positive.equiv C.positive.double x (eval B.S b v)
    (fun p => by rw [hv, C.depth_positive, SU3Root.towerDepth])
    (fun p hp => by
      rw [hv, C.depth_double_positive ⟨p, hp⟩, SU3Root.towerCentralDepth,
        SU3Root.Parameters.depthDouble, eval_nsmul_char, Nat.cast_ofNat])
    s.2
    ((LocalField.mem_addValuationUnitFiltration _ _ _).mp
      (coordinateCharacter_mem_unitFiltration F (B.centralizerTorus hZ)
        (MaximalUnramified.valuationSubring_isHenselian F) ht C.positive.character)).2
    (C.positive.conjugation t) hu

/-- The case of a divisible root `2b`, from valued SU3 coordinates of `b`. -/
theorem commutator_mem_filtrationBlock_double {b : characterLattice B.S}
    (C : ValuedSU3RootCoordinates B hZ b) (x : B.Apartment) {r s : ℝ≥0}
    {t : rationalPoints (B.centralizerTorus hZ).toGrp}
    (ht : t ∈ localGeometricCharacterCongruence F (B.centralizerTorus hZ) r)
    {u : rationalPoints H} (hu : u ∈ B.filtration x (2 • b) s) :
    rationalPoints.map B.centralizer.j t * u * (rationalPoints.map B.centralizer.j t)⁻¹ *
        u⁻¹ ∈ B.apartment.filtrationBlock x (fun _ => ((r + s : ℝ≥0) : ℝ)) (2 • b) := by
  obtain ⟨v, hv⟩ := B.apartment.exists_val_eq_add_eval x C.origin
  rw [NNReal.coe_add]
  exact B.apartment.commutator_mem_filtrationBlock_double_of_unitaryScaling
    (FieldTheory.henselianSeparableAddValuation (MaximalUnramified.valuation F)
      (MaximalUnramified.valuationSubring_isHenselian F) C.extension)
    (SU3Root.henselianSeparableAddValuation_quadratic_bar (UnramifiedClosure F) C.base
      C.extension (MaximalUnramified.valuation F)
      (MaximalUnramified.valuationSubring_isHenselian F))
    C.positive.equiv C.positive.double x (eval B.S (2 • b) v)
    (fun p hp => by
      rw [hv, C.depth_double_positive ⟨p, hp⟩, SU3Root.towerCentralDepth,
        SU3Root.Parameters.depthDouble])
    r.2
    ((LocalField.mem_addValuationUnitFiltration _ _ _).mp
      (coordinateCharacter_mem_unitFiltration F (B.centralizerTorus hZ)
        (MaximalUnramified.valuationSubring_isHenselian F) ht C.positive.character)).2
    (C.positive.conjugation t) hu

end KPLocalTorusRootCommutator

open KPLocalTorusRootCommutator in
/-- Valued rank-one coordinates give the positive-depth torus action on root-group
filtrations over `K = F^ur`. -/
theorem kpLocalTorusRootCommutator_of_valuedRankOneCoordinates
    (hC : QuasiSplitValuedRankOneCoordinatesStatement.{u}) :
    KPLocalTorusRootCommutatorStatement.{u} := by
  intro F _ _ _ _ H _ B hZ x a r s _ t ht u hu
  obtain ⟨b, hb, hab | ⟨hab, h2⟩⟩ := exists_indivisible_eq_or_double B a.2
  · rw [hab] at hu ⊢
    by_cases h2 : 2 • b ∈ relativeRoots B.i
    · obtain ⟨C⟩ := (hC F H B hZ b hb).2 h2
      exact commutator_mem_filtrationBlock_su3 C h2 x ht hu
    · obtain ⟨C⟩ := (hC F H B hZ b hb).1 h2
      exact B.apartment.mem_filtrationBlock.mpr
        ⟨_, commutator_mem_filtration_sl2 C x ht hu, 1, Subgroup.one_mem _, mul_one _⟩
  · rw [hab] at hu ⊢
    obtain ⟨C⟩ := (hC F H B hZ b hb).2 h2
    exact commutator_mem_filtrationBlock_double C x ht hu

end Langlands.Geometry.Building

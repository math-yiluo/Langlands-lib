import Langlands.Geometry.Building.CentralizerNormValuation
import Langlands.FieldTheory.HenselianSeparableIntegerAddValuation

/-! # Full V6 from root-coordinate equivariance

Let `v` be an integer-valued valuation of `k`. An additive valuation `w` of a finite extension
`E / k` is norm-calibrated for `v` if `w(x) = ord_v(N_{E/k} x) / [E : k]` for every unit `x`.
Suppose that on the actual rational root-group points `U_a(k)` a coordinate `c : G(k) → E`
satisfies `w(c(u)) = m • φ_a(u)` for a positive integer `m`, and that the actual centralizer
acts on it through a character `β` of `Z_E` whose restriction to `S_E` is the base change of
`m • a`: `c(z⁻¹ u z) = β(z_E)⁻¹ c(u)`. Then `φ_a` satisfies the axiom V 6 on `Z(k)` with the
integer centralizer translation. Bundling such data for every relative root gives
`IsCentralizerCompatible`, and for one valuation of an apartment class the full
`IsOmegaCompatible`. Over a henselian base, the chosen invariant prolongation of `v` to a finite
Galois extension, and the induced valuation of a finite separable extension, are
norm-calibrated.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.BruhatTits
  Langlands.Plancherel.TorusNormKernel

namespace Langlands.Geometry.Building.IntegerValuation

variable {k : Type u} [Field k] (v : Valuation k (WithZero (Multiplicative ℤ)))

section Calibration

variable {E : Type u} [Field E] [Algebra k E] [FiniteDimensional k E]

/-- An additive valuation of `E` is norm-calibrated for `v` when its value at every unit is the
order of the field norm divided by the degree `[E : k]`. -/
def IsNormCalibrated (w : AddValuation E (WithTop ℝ)) : Prop :=
  ∀ x : Eˣ, w (x : E) =
    ((order v (Units.map (Algebra.norm k : E →* k) x) / Module.finrank k E : ℝ) : WithTop ℝ)

variable {v}

omit [FiniteDimensional k E] in
/-- A norm-calibrated valuation computes the degree-normalized norm order of character values. -/
theorem IsNormCalibrated.apply_rationalCharacterEval {w : AddValuation E (WithTop ℝ)}
    (hw : IsNormCalibrated v w) {Z : GroupScheme (Spec (CommRingCat.of k))} [IsAffine Z.X.left]
    (α : rationalCharacters (GaloisPointComparison.baseChanged k E Z)) (z : rationalPoints Z) :
    w (rationalCharacterEval α (GaloisPointComparison.rationalExtend k E Z z) : E) =
      (characterNormOrder v α z : WithTop ℝ) :=
  hw _

omit [FiniteDimensional k E] in
/-- A norm-calibrated valuation of an inverse unit is the negative normalized norm order. -/
theorem IsNormCalibrated.apply_inv {w : AddValuation E (WithTop ℝ)} (hw : IsNormCalibrated v w)
    (x : Eˣ) : w ((x⁻¹ : Eˣ) : E) = ((-(order v (Units.map (Algebra.norm k : E →* k) x) /
      Module.finrank k E) : ℝ) : WithTop ℝ) := by
  rw [hw, map_inv]
  congr 2
  simp [order, neg_div]

end Calibration

variable {v} in
/-- Over a henselian base, the chosen invariant prolongation of `v` to a finite Galois extension
is norm-calibrated. -/
theorem isNormCalibrated_henselianIntegerAddValuation
    (hH : HenselianLocalRing v.valuationSubring) (E : Type u) [Field E] [Algebra k E]
    [IsGalois k E] [FiniteDimensional k E] :
    IsNormCalibrated v (FieldTheory.henselianIntegerAddValuation v hH E) := by
  intro x
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp
    ((FieldTheory.henselianIntegerAddValuation v hH E).ne_top_iff.mpr x.ne_zero)
  have hn := FieldTheory.henselianIntegerAddValuation_norm v hH E (x : E)
  rw [FieldTheory.henselianIntegerAddValuation_base v hH E
    (Algebra.norm_ne_zero_iff.mpr x.ne_zero), ← hr, ← WithTop.coe_nsmul, WithTop.coe_inj,
    nsmul_eq_mul] at hn
  rw [← hr, WithTop.coe_inj, eq_div_iff (Nat.cast_ne_zero.mpr
    (ne_of_gt (Module.finrank_pos (R := k) (M := E)))), order, orderUnits_toAdd,
    Units.coe_map, hn, mul_comm]

variable {v} in
/-- Over a henselian base, the induced normalized valuation of a finite separable extension is
norm-calibrated. -/
theorem isNormCalibrated_henselianSeparableAddValuation
    (hH : HenselianLocalRing v.valuationSubring) (E : Type u) [Field E] [Algebra k E]
    [Algebra.IsSeparable k E] [FiniteDimensional k E] :
    IsNormCalibrated v (FieldTheory.henselianSeparableAddValuation v hH E) := by
  intro x
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp
    ((FieldTheory.henselianSeparableAddValuation v hH E).ne_top_iff.mpr x.ne_zero)
  have hn := FieldTheory.henselianSeparableAddValuation_norm v hH E (x : E)
  rw [FieldTheory.henselianSeparableAddValuation_base v hH E
    (Algebra.norm_ne_zero_iff.mpr x.ne_zero), ← hr, ← WithTop.coe_nsmul, WithTop.coe_inj,
    nsmul_eq_mul] at hn
  rw [← hr, WithTop.coe_inj, eq_div_iff (Nat.cast_ne_zero.mpr
    (ne_of_gt (Module.finrank_pos (R := k) (M := E)))), order, orderUnits_toAdd,
    Units.coe_map, hn, mul_comm]

/-- Multiplication by a positive natural number is injective on `WithTop ℝ`. -/
theorem nsmul_withTop_injective {m : ℕ} (hm : 0 < m) :
    Function.Injective fun x : WithTop ℝ => m • x := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have htop : ∀ x : WithTop ℝ, (n + 1) • x = ⊤ ↔ x = ⊤ := by
    intro x
    constructor
    · intro hx
      induction x using WithTop.recTopCoe with
      | top => rfl
      | coe b => exact absurd hx (by rw [← WithTop.coe_nsmul]; exact WithTop.coe_ne_top)
    · rintro rfl
      rw [succ_nsmul, WithTop.add_top]
  intro x y hxy
  simp only at hxy
  induction x using WithTop.recTopCoe with
  | top => exact ((htop y).mp (hxy.symm.trans ((htop ⊤).mpr rfl))).symm
  | coe a =>
    induction y using WithTop.recTopCoe with
    | top => exact absurd ((htop _).mp (hxy.trans ((htop ⊤).mpr rfl))) WithTop.coe_ne_top
    | coe b =>
      rw [← WithTop.coe_nsmul, ← WithTop.coe_nsmul, WithTop.coe_inj, nsmul_eq_mul,
        nsmul_eq_mul] at hxy
      rw [WithTop.coe_inj]
      exact mul_left_cancel₀ (by positivity) hxy

section Compatibility

variable {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G Z : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [IsAffine S.toGrp.X.left]
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] {j : Z ⟶ G} {s : S.toGrp ⟶ Z}

omit [IsAffineHom G.X.hom] in
/-- **Per-root V 6 from coordinate equivariance.** -/
theorem conj_eq_of_coordinate [IsAffine Z.X.left] (hj : (torusCentralizer i).IsRepresentedBy j)
    (h : Function.Bijective (Cartan.restrictionEvaluation s))
    (φ : RootFunctionFamily S G) (a : characterLattice S)
    {E : Type u} [Field E] [Algebra k E] [FiniteDimensional k E]
    {w : AddValuation E (WithTop ℝ)} (hw : IsNormCalibrated v w)
    (c : rationalPoints G → E) {m : ℕ} (hm : 0 < m)
    {β : rationalCharacters (GaloisPointComparison.baseChanged k E Z)}
    (hβ : characterRestrict ((GroupScheme.baseChange (baseMap k E)).map s) β =
      rationalCharacters.baseChange (baseMap k E)
        ((rationalCharacters.equivCharacterLattice S).symm (m • a)))
    (hval : ∀ u ∈ rootGroupPoints i a, w (c u) = m • φ a u)
    (hconj : ∀ z : rationalPoints Z, ∀ u ∈ rootGroupPoints i a,
      c ((rationalPoints.map j z)⁻¹ * u * rationalPoints.map j z) =
        (((rationalCharacterEval β (GaloisPointComparison.rationalExtend k E Z z))⁻¹ : Eˣ) : E) *
          c u)
    (z : rationalPoints Z) {u : rationalPoints G} (hu : u ∈ rootGroupPoints i a) :
    φ a ((rationalPoints.map j z)⁻¹ * u * rationalPoints.map j z) =
      φ a u + ((eval S a (centralizerTranslation v s h z).toAdd : ℝ) : WithTop ℝ) := by
  have hmem : (rationalPoints.map j z)⁻¹ * u * rationalPoints.map j z ∈ rootGroupPoints i a := by
    have hc := conj_mem_rootGroupPoints (centralizerToNormalizer i j hj z⁻¹) hu
    rwa [weylAction_centralizerToNormalizer hj, LinearEquiv.coe_one, id,
      coe_centralizerToNormalizer, map_inv, inv_inv] at hc
  have hβz := characterNormOrder_eq_eval v s h hβ z
  rw [eval_nsmul_char] at hβz
  apply nsmul_withTop_injective hm
  simp only
  rw [← hval _ hmem, hconj z u hu, AddValuation.map_mul, hw.apply_inv, hval u hu,
    centralizerTranslation_toAdd, map_neg, nsmul_add, ← WithTop.coe_nsmul, add_comm]
  congr 2
  change -(characterNormOrder v β z) = _
  rw [hβz, nsmul_eq_mul]
  ring

omit [IsAffineHom G.X.hom] [IsAffine S.toGrp.X.left] in
/-- Equivariant coordinate data on the actual root group `U_a(k)`: a finite extension `E / k`
with a norm-calibrated valuation `w`, a coordinate `c : G(k) → E` and a positive integer `m`
with `w(c(u)) = m • φ_a(u)` on `U_a(k)`, and a character `β` of `Z_E` whose restriction to `S_E`
is the base change of `m • a`, through which the actual centralizer acts on the coordinate:
`c(z⁻¹ u z) = β(z_E)⁻¹ c(u)`. -/
structure RootCoordinateEquivariance (i : S.toGrp ⟶ G) (j : Z ⟶ G) (s : S.toGrp ⟶ Z)
    (φ : RootFunctionFamily S G) (a : characterLattice S) : Type (u + 1) where
  /-- The coefficient field of the coordinate. -/
  E : Type u
  [field : Field E]
  [algebra : Algebra k E]
  [finiteDimensional : FiniteDimensional k E]
  /-- The norm-calibrated additive valuation of `E`. -/
  w : AddValuation E (WithTop ℝ)
  isNormCalibrated : IsNormCalibrated v w
  /-- The coordinate on rational points. -/
  coord : rationalPoints G → E
  /-- The multiplicity of the root valuation in the coordinate valuation. -/
  m : ℕ
  pos : 0 < m
  /-- The character of `Z_E` through which the centralizer acts on the coordinate. -/
  character : rationalCharacters (GaloisPointComparison.baseChanged k E Z)
  restrict_eq : characterRestrict ((GroupScheme.baseChange (baseMap k E)).map s) character =
    rationalCharacters.baseChange (baseMap k E)
      ((rationalCharacters.equivCharacterLattice S).symm (m • a))
  value : ∀ u ∈ rootGroupPoints i a, w (coord u) = m • φ a u
  conj : ∀ z : rationalPoints Z, ∀ u ∈ rootGroupPoints i a,
    coord ((rationalPoints.map j z)⁻¹ * u * rationalPoints.map j z) =
      (((rationalCharacterEval character (GaloisPointComparison.rationalExtend k E Z z))⁻¹ :
        Eˣ) : E) * coord u

attribute [instance] RootCoordinateEquivariance.field RootCoordinateEquivariance.algebra
  RootCoordinateEquivariance.finiteDimensional

variable {v}

omit [IsAffineHom G.X.hom] in
/-- V 6 for one root from its equivariant coordinate data. -/
theorem RootCoordinateEquivariance.conj_eq [IsAffine Z.X.left]
    (hj : (torusCentralizer i).IsRepresentedBy j)
    (h : Function.Bijective (Cartan.restrictionEvaluation s)) {φ : RootFunctionFamily S G}
    {a : characterLattice S} (R : RootCoordinateEquivariance v i j s φ a) (z : rationalPoints Z)
    {u : rationalPoints G} (hu : u ∈ rootGroupPoints i a) :
    φ a ((rationalPoints.map j z)⁻¹ * u * rationalPoints.map j z) =
      φ a u + ((eval S a (centralizerTranslation v s h z).toAdd : ℝ) : WithTop ℝ) :=
  conj_eq_of_coordinate v hj h φ a R.isNormCalibrated R.coord R.pos R.restrict_eq R.value R.conj
    z hu

omit [IsAffineHom G.X.hom] [IsAffine S.toGrp.X.left] in
/-- Equivariant coordinate data from an actual parametrization `e : E ≃ U_a(k)` of the root group
by the additive group of `E`, with `φ_a(e(x)) = w(x)` and centralizer conjugation acting by the
scalar `β(z_E)⁻¹`; the multiplicity is `m = 1`. -/
def RootCoordinateEquivariance.ofMulEquiv {φ : RootFunctionFamily S G}
    {a : characterLattice S} {E : Type u} [Field E] [Algebra k E] [FiniteDimensional k E]
    {w : AddValuation E (WithTop ℝ)} (hw : IsNormCalibrated v w)
    (e : Multiplicative E ≃* rootGroupPoints i a)
    (β : rationalCharacters (GaloisPointComparison.baseChanged k E Z))
    (hβ : characterRestrict ((GroupScheme.baseChange (baseMap k E)).map s) β =
      rationalCharacters.baseChange (baseMap k E)
        ((rationalCharacters.equivCharacterLattice S).symm a))
    (hφ : ∀ x : E, φ a (e (Multiplicative.ofAdd x)) = w x)
    (hconj : ∀ (z : rationalPoints Z) (x : E),
      (rationalPoints.map j z)⁻¹ * (e (Multiplicative.ofAdd x) : rationalPoints G) *
          rationalPoints.map j z =
        (e (Multiplicative.ofAdd ((((rationalCharacterEval β
          (GaloisPointComparison.rationalExtend k E Z z))⁻¹ : Eˣ) : E) * x)) :
            rationalPoints G)) :
    RootCoordinateEquivariance v i j s φ a := by
  classical
  let c : rationalPoints G → E := fun u =>
    if hu : u ∈ rootGroupPoints i a then (e.symm ⟨u, hu⟩).toAdd else 0
  have hc : ∀ x : E, c (e (Multiplicative.ofAdd x)) = x := by
    intro x
    simp only [c, dite_eq_left (e (Multiplicative.ofAdd x)).property, Subtype.coe_eta,
      MulEquiv.symm_apply_apply, toAdd_ofAdd]
  have hsurj : ∀ u ∈ rootGroupPoints i a,
      (e (Multiplicative.ofAdd (c u)) : rationalPoints G) = u := by
    intro u hu
    simp only [c, dite_eq_left hu, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  exact
    { E := E
      w := w
      isNormCalibrated := hw
      coord := c
      m := 1
      pos := Nat.one_pos
      character := β
      restrict_eq := by rw [one_nsmul]; exact hβ
      value := by
        intro u hu
        rw [one_nsmul, ← hφ, hsurj u hu]
      conj := by
        intro z u hu
        rw [← hsurj u hu, hconj, hc, hc] }

omit [IsAffineHom G.X.hom] in
variable (v) in
/-- **Per-root V 6 from a finite family of coordinates.** If `m • φ_a` is the minimum of the
values of finitely many coordinates, each scaled by the centralizer through a character of `Z_E`
restricting to the base change of `m • a`, then `φ_a` satisfies V 6 at the root `a`. -/
theorem conj_eq_of_coordinateFamily [IsAffine Z.X.left]
    (hj : (torusCentralizer i).IsRepresentedBy j)
    (h : Function.Bijective (Cartan.restrictionEvaluation s))
    (φ : RootFunctionFamily S G) (a : characterLattice S)
    {E : Type u} [Field E] [Algebra k E] [FiniteDimensional k E]
    {w : AddValuation E (WithTop ℝ)} (hw : IsNormCalibrated v w)
    {J : Type u} [Fintype J] [Nonempty J] (c : J → rationalPoints G → E) {m : ℕ} (hm : 0 < m)
    {β : J → rationalCharacters (GaloisPointComparison.baseChanged k E Z)}
    (hβ : ∀ l, characterRestrict ((GroupScheme.baseChange (baseMap k E)).map s) (β l) =
      rationalCharacters.baseChange (baseMap k E)
        ((rationalCharacters.equivCharacterLattice S).symm (m • a)))
    (hval : ∀ u ∈ rootGroupPoints i a,
      m • φ a u = Finset.univ.inf' Finset.univ_nonempty fun l => w (c l u))
    (hconj : ∀ (z : rationalPoints Z) (l : J), ∀ u ∈ rootGroupPoints i a,
      c l ((rationalPoints.map j z)⁻¹ * u * rationalPoints.map j z) =
        (((rationalCharacterEval (β l) (GaloisPointComparison.rationalExtend k E Z z))⁻¹ :
          Eˣ) : E) * c l u)
    (z : rationalPoints Z) {u : rationalPoints G} (hu : u ∈ rootGroupPoints i a) :
    φ a ((rationalPoints.map j z)⁻¹ * u * rationalPoints.map j z) =
      φ a u + ((eval S a (centralizerTranslation v s h z).toAdd : ℝ) : WithTop ℝ) := by
  have hmem : (rationalPoints.map j z)⁻¹ * u * rationalPoints.map j z ∈ rootGroupPoints i a := by
    have hc := conj_mem_rootGroupPoints (centralizerToNormalizer i j hj z⁻¹) hu
    rwa [weylAction_centralizerToNormalizer hj, LinearEquiv.coe_one, id,
      coe_centralizerToNormalizer, map_inv, inv_inv] at hc
  let C : WithTop ℝ := m • ((eval S a (centralizerTranslation v s h z).toAdd : ℝ) : WithTop ℝ)
  have hl : ∀ l, w (c l ((rationalPoints.map j z)⁻¹ * u * rationalPoints.map j z)) =
      w (c l u) + C := by
    intro l
    have hβz := characterNormOrder_eq_eval v s h (hβ l) z
    rw [eval_nsmul_char] at hβz
    rw [hconj z l u hu, AddValuation.map_mul, hw.apply_inv, add_comm]
    simp only [C, centralizerTranslation_toAdd, map_neg, ← WithTop.coe_nsmul]
    congr 2
    change -(characterNormOrder v (β l) z) = _
    rw [hβz, nsmul_eq_mul]
    ring
  apply nsmul_withTop_injective hm
  simp only
  rw [hval _ hmem, nsmul_add, hval u hu]
  simp_rw [hl]
  exact (map_finset_inf' (OrderHom.mk (· + C) fun _ _ hxy => add_le_add hxy le_rfl)
    Finset.univ_nonempty fun l => w (c l u)).symm

omit [IsAffineHom G.X.hom] [IsAffine S.toGrp.X.left] in
variable (v) in
/-- Equivariant coordinate families on the actual root group `U_a(k)`: a finite extension
`E / k` with a norm-calibrated valuation `w`, a nonempty finite family of coordinates
`c_l : G(k) → E` and a positive integer `m` with `m • φ_a(u) = min_l w(c_l(u))` on `U_a(k)`, and
characters `β_l` of `Z_E` whose restrictions to `S_E` are the base change of `m • a`, through
which the actual centralizer acts on the coordinates: `c_l(z⁻¹ u z) = β_l(z_E)⁻¹ c_l(u)`. -/
structure RootCoordinateFamilyEquivariance (i : S.toGrp ⟶ G) (j : Z ⟶ G) (s : S.toGrp ⟶ Z)
    (φ : RootFunctionFamily S G) (a : characterLattice S) : Type (u + 1) where
  /-- The coefficient field of the coordinates. -/
  E : Type u
  [field : Field E]
  [algebra : Algebra k E]
  [finiteDimensional : FiniteDimensional k E]
  /-- The norm-calibrated additive valuation of `E`. -/
  w : AddValuation E (WithTop ℝ)
  isNormCalibrated : IsNormCalibrated v w
  /-- The index type of the coordinates. -/
  J : Type u
  [fintype : Fintype J]
  [nonempty : Nonempty J]
  /-- The coordinates on rational points. -/
  coord : J → rationalPoints G → E
  /-- The multiplicity of the root valuation in the coordinate valuations. -/
  m : ℕ
  pos : 0 < m
  /-- The characters of `Z_E` through which the centralizer acts on the coordinates. -/
  character : J → rationalCharacters (GaloisPointComparison.baseChanged k E Z)
  restrict_eq : ∀ l, characterRestrict ((GroupScheme.baseChange (baseMap k E)).map s)
    (character l) = rationalCharacters.baseChange (baseMap k E)
      ((rationalCharacters.equivCharacterLattice S).symm (m • a))
  value : ∀ u ∈ rootGroupPoints i a,
    m • φ a u = Finset.univ.inf' Finset.univ_nonempty fun l => w (coord l u)
  conj : ∀ (z : rationalPoints Z) (l : J), ∀ u ∈ rootGroupPoints i a,
    coord l ((rationalPoints.map j z)⁻¹ * u * rationalPoints.map j z) =
      (((rationalCharacterEval (character l)
        (GaloisPointComparison.rationalExtend k E Z z))⁻¹ : Eˣ) : E) * coord l u

attribute [instance] RootCoordinateFamilyEquivariance.field
  RootCoordinateFamilyEquivariance.algebra RootCoordinateFamilyEquivariance.finiteDimensional
  RootCoordinateFamilyEquivariance.fintype RootCoordinateFamilyEquivariance.nonempty

omit [IsAffineHom G.X.hom] in
/-- V 6 for one root from an equivariant coordinate family. -/
theorem RootCoordinateFamilyEquivariance.conj_eq [IsAffine Z.X.left]
    (hj : (torusCentralizer i).IsRepresentedBy j)
    (h : Function.Bijective (Cartan.restrictionEvaluation s)) {φ : RootFunctionFamily S G}
    {a : characterLattice S} (R : RootCoordinateFamilyEquivariance v i j s φ a)
    (z : rationalPoints Z) {u : rationalPoints G} (hu : u ∈ rootGroupPoints i a) :
    φ a ((rationalPoints.map j z)⁻¹ * u * rationalPoints.map j z) =
      φ a u + ((eval S a (centralizerTranslation v s h z).toAdd : ℝ) : WithTop ℝ) :=
  conj_eq_of_coordinateFamily v hj h φ a R.isNormCalibrated R.coord R.pos R.restrict_eq R.value
    R.conj z hu

omit [IsAffineHom G.X.hom] [IsAffine S.toGrp.X.left] in
/-- A single equivariant coordinate is a one-member coordinate family. -/
def RootCoordinateEquivariance.toFamily {φ : RootFunctionFamily S G} {a : characterLattice S}
    (R : RootCoordinateEquivariance v i j s φ a) : RootCoordinateFamilyEquivariance v i j s φ a where
  E := R.E
  w := R.w
  isNormCalibrated := R.isNormCalibrated
  J := PUnit
  coord := fun _ => R.coord
  m := R.m
  pos := R.pos
  character := fun _ => R.character
  restrict_eq := fun _ => R.restrict_eq
  value := by
    intro u hu
    rw [Finset.inf'_const, R.value u hu]
  conj := fun z _ u hu => R.conj z u hu

/-- **Full V 6 from root coordinate families.** An equivariant coordinate family on every
relative root group gives the integer centralizer compatibility of `φ`. -/
theorem isCentralizerCompatible_of_rootCoordinateFamilies [IsAffine Z.X.left]
    (hj : (torusCentralizer i).IsRepresentedBy j)
    (h : Function.Bijective (Cartan.restrictionEvaluation s)) {φ : RootFunctionFamily S G}
    (hc : ∀ a ∈ relativeRoots i, Nonempty (RootCoordinateFamilyEquivariance v i j s φ a)) :
    IsCentralizerCompatible v i j s h φ :=
  fun a ha z _ hu => (hc a ha).some.conj_eq hj h z hu

/-- **Full V 6 from root coordinates.** Equivariant coordinate data on every relative root
group gives the integer centralizer compatibility of `φ`. -/
theorem isCentralizerCompatible_of_rootCoordinates [IsAffine Z.X.left]
    (hj : (torusCentralizer i).IsRepresentedBy j)
    (h : Function.Bijective (Cartan.restrictionEvaluation s)) {φ : RootFunctionFamily S G}
    (hc : ∀ a ∈ relativeRoots i, Nonempty (RootCoordinateEquivariance v i j s φ a)) :
    IsCentralizerCompatible v i j s h φ :=
  fun a ha z _ hu => (hc a ha).some.conj_eq hj h z hu

end Compatibility

section Apartment

variable {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [IsAffine S.toGrp.X.left]
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]

variable {v} in
/-- **Omega compatibility from root coordinates.** If one member of the apartment class has
equivariant coordinate data on every relative root group for the actual centralizer, the whole
class is Omega-compatible. -/
theorem isOmegaCompatible_of_rootCoordinates {D : KPApartmentData i (order v)}
    {C : CentralizerDatum i} {φ : RootFunctionFamily S G} (hφ : φ ∈ D.carrier)
    (hc : ∀ a ∈ relativeRoots i, Nonempty (RootCoordinateEquivariance v i C.j C.s φ a)) :
    IsOmegaCompatible v D C := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsClosedImmersion C.j.hom.hom.left := C.isClosedSubgroup
  have : IsAffine C.Z.X.left := isAffine_of_isAffineHom C.j.hom.hom.left
  exact (isOmegaCompatible_iff_of_mem hφ).mpr
    (isCentralizerCompatible_of_rootCoordinates C.isRepresentedBy C.bijective hc)

variable {v} in
/-- **Omega compatibility from root coordinate families.** If one member of the apartment class
has an equivariant coordinate family on every relative root group for the actual centralizer, the
whole class is Omega-compatible. -/
theorem isOmegaCompatible_of_rootCoordinateFamilies {D : KPApartmentData i (order v)}
    {C : CentralizerDatum i} {φ : RootFunctionFamily S G} (hφ : φ ∈ D.carrier)
    (hc : ∀ a ∈ relativeRoots i,
      Nonempty (RootCoordinateFamilyEquivariance v i C.j C.s φ a)) :
    IsOmegaCompatible v D C := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsClosedImmersion C.j.hom.hom.left := C.isClosedSubgroup
  have : IsAffine C.Z.X.left := isAffine_of_isAffineHom C.j.hom.hom.left
  exact (isOmegaCompatible_iff_of_mem hφ).mpr
    (isCentralizerCompatible_of_rootCoordinateFamilies C.isRepresentedBy C.bijective hc)

end Apartment

end Langlands.Geometry.Building.IntegerValuation

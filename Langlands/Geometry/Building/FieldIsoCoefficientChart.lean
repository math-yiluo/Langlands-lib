import Langlands.Geometry.Building.KPApartmentCoefficientChart
import Langlands.Geometry.Building.IntegerCentralizerFieldRestriction
import Langlands.Geometry.Building.IntegerValuationBuildingBasedTransport
import Langlands.Geometry.Building.CentralizerDatumBaseChange
import Langlands.Geometry.Building.IntegerOmegaApartmentUniqueness
import Langlands.Geometry.Building.KPZeroNormKernel
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.ScalarExtensionNaturality
import Langlands.GroupScheme.Rational.RingEquivBaseChange
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.Rational.MaximalSplitTorusFieldIso
import Langlands.GroupScheme.Rational.NormalizerGaloisAction
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent
import Langlands.GroupScheme.IntegralModel.UnramifiedBuildingSemilinearAction
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.Geometry.Building.MaximalUnramifiedUniformizer
import Langlands.Geometry.Building.UnramifiedOmegaGaloisStable
import Langlands.LocalField.ValuativeInfinite

/-! # Apartment charts along a field extension -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

section TorusValues

variable {k : Type u} [Field k] {S S' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Transporting a character along an isomorphism of tori. -/
theorem torusCharacterValue_congr (e : S ≅ S') (χ : characterLattice S)
    (t : rationalPoints S.toGrp) :
    torusCharacterValue (characterLattice.congr e χ)
        (rationalPoints.map (CommGroupScheme.groupHom e.hom) t) =
      torusCharacterValue χ t := by
  rw [characterLattice.congr_apply]
  unfold torusCharacterValue
  rw [← rationalCharacterEval_characterRestrict]
  change rationalCharacterEval _ (rationalPoints.map (CommGroupScheme.groupHom e.inv)
    (rationalPoints.map (CommGroupScheme.groupHom e.hom) t)) = _
  congr 1
  simp only [rationalPoints.map_apply, Category.assoc]
  change t ≫ (CommGroupScheme.groupHom (e.hom ≫ e.inv)).hom.hom = t
  rw [Iso.hom_inv_id]
  exact Category.comp_id t

variable {K : Type u} [Field K] [Algebra k K]

/-- Character values commute with scalar extension. -/
theorem torusCharacterValue_baseChange (χ : characterLattice S) (t : rationalPoints S.toGrp) :
    torusCharacterValue (characterLattice.baseChange (algebraBaseMap k K) S χ)
        (rationalExtend k K S.toGrp t) =
      Units.map (algebraMap k K).toMonoidHom (torusCharacterValue χ t) := by
  unfold torusCharacterValue
  have hχ : (rationalCharacters.equivCharacterLattice
        ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj S)).symm
        (characterLattice.baseChange (algebraBaseMap k K) S χ) =
      rationalCharacters.baseChange (algebraBaseMap k K)
        ((rationalCharacters.equivCharacterLattice S).symm χ) := by
    change rationalCharacters.baseChange (algebraBaseMap k K)
      ((rationalCharacters.equivCharacterLattice S).symm χ) = _
    rfl
  rw [hχ]
  exact rationalCharacterEval_extend k K S.toGrp _ t

end TorusValues

namespace IntegerValuationBuildingData

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {v : Valuation k (WithZero (Multiplicative ℤ))} {w : Valuation K (WithZero (Multiplicative ℤ))}
  {G₁ : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G₁.X.hom]
  {G₂ : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G₂.X.hom]
  (B₁ : IntegerValuationBuildingData v G₁) (B₂ : IntegerValuationBuildingData w G₂)

local notation "b" => algebraBaseMap k K

/-- A chart from the apartment of `B₂` over `K` to the apartment of `B₁` over `k`, along a
map `Φ : G₁(k) → G₂(K)`: `(a x)_χ(u) = x_{β χ}(Φ u)`, `Φ` carries `i₁(t)` to `i₂(τ t)`, and
`β` matches characters through `τ` and `k → K`. -/
structure FieldChart (Φ : rationalPoints G₁ → rationalPoints G₂) where
  /-- The relabelling of characters. -/
  β : characterLattice B₁.S ≃ characterLattice B₂.S
  /-- The bijection of torus points. -/
  τ : rationalPoints B₁.S.toGrp ≃ rationalPoints B₂.S.toGrp
  /-- The map of apartment points. -/
  a : B₂.Apartment → B₁.Apartment
  /-- The transport formula. -/
  a_val : ∀ (x : B₂.Apartment) (χ : characterLattice B₁.S) (u : rationalPoints G₁),
    (a x).val χ u = x.val (β χ) (Φ u)
  /-- `Φ` carries the torus points through `τ`. -/
  torus : ∀ t : rationalPoints B₁.S.toGrp,
    Φ (rationalPoints.map B₁.i t) = rationalPoints.map B₂.i (τ t)
  /-- The character relation. -/
  char : ∀ (χ : characterLattice B₁.S) (t : rationalPoints B₁.S.toGrp),
    torusCharacterValue (β χ) (τ t) =
      Units.map (algebraMap k K).toMonoidHom (torusCharacterValue χ t)

private instance baseChangedAffine : IsAffineHom (baseChanged k K G₁).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G₁.X.hom (baseMap k K))
  infer_instance

/-- **Field-isomorphism charts.** If `k → K` is bijective and preserves the integer orders,
the order of `v` is not identically zero, and the base change of the torus of `B₁` is
maximal split, then for every `f_G : G₁ ×_k K ≅ G₂` there is `g ∈ G₂(K)` and a chart from the
apartment of `B₂` to that of `B₁` along `u ↦ g Φ₀(u) g⁻¹`, where `Φ₀(u) = f_G(u_K)`. The map
`Φ₀` is a parameter, so that callers can supply it in their own form. -/
theorem exists_fieldChart (fG : baseChanged k K G₁ ≅ G₂)
    (Φ₀ : rationalPoints G₁ → rationalPoints G₂)
    (hΦ₀ : ∀ u, rationalPoints.map fG.hom (rationalExtend k K G₁ u) = Φ₀ u)
    (hbij : Function.Bijective (algebraMap k K))
    (horder : ∀ t : kˣ, IntegerValuation.order w
      (Units.map (algebraMap k K).toMonoidHom t) = IntegerValuation.order v t)
    (hν : ∃ t : kˣ, IntegerValuation.order v t ≠ 0)
    (hmax : IsMaximalSplitTorus (T := (CommGroupScheme.baseChange b).obj B₁.S)
      ((GroupScheme.baseChange b).map B₁.i)) :
    ∃ g : rationalPoints G₂, Nonempty (B₁.FieldChart B₂ (fun u => g * Φ₀ u * g⁻¹)) := by
  have hG₁ := B₁.isConnectedReductive
  have : Smooth G₁.X.hom := hG₁.smooth
  have : Mono ((GroupScheme.baseChange b).map B₁.i).hom.hom.left :=
    mono_of_isMaximalSplitTorus hmax
  have hS₁ : IsSplitTorus B₁.S.toGrp := B₁.isMaximalSplitTorus.1.1
  have hE₁ : RelativeRoot.HasOppositeFactorPairs B₁.i := by
    have hrank := rootRankOneFactorization.{u} k G₁ hG₁ B₁.S B₁.i B₁.isMaximalSplitTorus
    exact fun a ha x hx hx1 => (hrank a ha x hx hx1).1.exists
  obtain ⟨g, e, he⟩ := (maximalSplitTorusConjugacy.{u} K G₂ B₂.isConnectedReductive).1
    ((CommGroupScheme.baseChange b).obj B₁.S) B₂.S
    ((GroupScheme.baseChange b).map B₁.i ≫ fG.hom) B₂.i (hmax.comp_iso fG)
    B₂.isMaximalSplitTorus
  let σS : (CommGroupScheme.baseChange b).obj B₁.S ≅ B₂.S :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  let F : baseChanged k K G₁ ≅ G₂ := fG ≪≫ G₂.innerIso g
  have h : (GroupScheme.baseChange b).map B₁.i ≫ F.hom =
      CommGroupScheme.groupHom σS.hom ≫ B₂.i := by
    rw [Iso.trans_hom, ← Category.assoc]
    exact he
  have h' := torusTransport_inverse_square σS F h
  let DK := B₂.apartment.transport σS.symm F.symm h'
  let CK := B₁.centralizer.baseChangeOfBasedIso B₂.centralizer σS F h
  have hDK : IntegerValuation.IsOmegaCompatible w DK CK :=
    B₂.isOmegaCompatible.transport_basedIso w B₂.centralizer CK σS.symm F.symm h'
  let R := IntegerValuation.fieldRestrictApartment hS₁ v w horder B₁.i hE₁ hν DK
  have hR : IntegerValuation.IsOmegaCompatible v R B₁.centralizer :=
    IntegerValuation.fieldRestrictApartment_isOmegaCompatible hS₁ v w horder B₁.i hE₁ hν DK
      B₁.centralizer CK.bijective hDK
  have hEq : R = B₁.apartment :=
    integerOmegaCompatibleApartmentUniqueness.{u} k v G₁ hG₁ B₁.S B₁.i
      B₁.isMaximalSplitTorus B₁.centralizer R B₁.apartment hR B₁.isOmegaCompatible
  have hmem : ∀ x : B₂.Apartment, RootFunctionFamily.fieldRestrict (k := k)
      (RootFunctionFamily.transportEquiv σS.symm F.symm x.val) ∈ B₁.apartment.carrier := by
    intro x
    rw [← hEq]
    exact ⟨_, ⟨x.val, x.mem, rfl⟩, rfl⟩
  have hF : ∀ y : rationalPoints (baseChanged k K G₁),
      rationalPoints.map F.hom y = g * rationalPoints.map fG.hom y * g⁻¹ := by
    intro y
    change (y ≫ fG.hom.hom.hom) ≫ (G₂.innerIso g).hom.hom.hom = _
    rw [comp_innerIso_hom, constantPoint_self]
    rfl
  let τ₀ : rationalPoints B₁.S.toGrp ≃ rationalPoints
      ((CommGroupScheme.baseChange b).obj B₁.S).toGrp :=
    Equiv.ofBijective (rationalExtend k K B₁.S.toGrp)
      (rationalExtend_bijective_of_bijective k K B₁.S.toGrp hbij)
  let τ₁ : rationalPoints ((CommGroupScheme.baseChange b).obj B₁.S).toGrp ≃
      rationalPoints B₂.S.toGrp :=
    { toFun := rationalPoints.map (CommGroupScheme.groupHom σS.hom)
      invFun := rationalPoints.map (CommGroupScheme.groupHom σS.inv)
      left_inv := fun p => by
        simp only [rationalPoints.map_apply, Category.assoc]
        change p ≫ (CommGroupScheme.groupHom (σS.hom ≫ σS.inv)).hom.hom = p
        rw [Iso.hom_inv_id]
        exact Category.comp_id p
      right_inv := fun p => by
        simp only [rationalPoints.map_apply, Category.assoc]
        change p ≫ (CommGroupScheme.groupHom (σS.inv ≫ σS.hom)).hom.hom = p
        rw [Iso.inv_hom_id]
        exact Category.comp_id p }
  refine ⟨g, ⟨{
    β := ((characterLattice.baseChangeEquiv b B₁.S hS₁).trans
      (characterLattice.congr σS)).toEquiv
    τ := τ₀.trans τ₁
    a := fun x => ⟨_, hmem x⟩
    a_val := ?_
    torus := ?_
    char := ?_ }⟩⟩
  · intro x χ u
    change RootFunctionFamily.transportEquiv σS.symm F.symm x.val
        (characterLattice.baseChange b B₁.S χ) (rationalExtend k K G₁ u) = _
    rw [RootFunctionFamily.transportEquiv_apply, ← hΦ₀, ← hF]
    rfl
  · intro t
    rw [← hΦ₀]
    change g * rationalPoints.map fG.hom (rationalExtend k K G₁ (rationalPoints.map B₁.i t)) *
        g⁻¹ = rationalPoints.map B₂.i
          (rationalPoints.map (CommGroupScheme.groupHom σS.hom)
            (rationalExtend k K B₁.S.toGrp t))
    rw [← hF, rationalExtend_map]
    simp only [rationalPoints.map_apply, Category.assoc]
    have h2 := congrArg (fun f => (rationalExtend k K B₁.S.toGrp t) ≫ f.hom.hom) h
    simpa only [Grp.comp_hom_hom, Category.assoc] using h2
  · intro χ t
    change torusCharacterValue (characterLattice.congr σS
        (characterLattice.baseChange b B₁.S χ))
        (rationalPoints.map (CommGroupScheme.groupHom σS.hom)
          (rationalExtend k K B₁.S.toGrp t)) = _
    rw [torusCharacterValue_congr]
    exact torusCharacterValue_baseChange χ t

end IntegerValuationBuildingData

section GaloisCharts

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

private instance coefficientChartAffineHom : IsAffineHom (baseChanged F K G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F K))
  infer_instance

variable (F) in
/-- The map `σ⁻¹` on units. -/
def unitsCoeff (σ : K ≃ₐ[F] K) : Kˣ → Kˣ :=
  Units.map (σ⁻¹).toMonoidHom

omit [IsAffineHom G.X.hom] in
@[simp] theorem unitsCoeff_one (z : Kˣ) : unitsCoeff F (1 : K ≃ₐ[F] K) z = z :=
  Units.ext (by simp [unitsCoeff])

omit [IsAffineHom G.X.hom] in
/-- The maps `σ⁻¹` on units compose contravariantly. -/
theorem unitsCoeff_mul (σ τ : K ≃ₐ[F] K) (z : Kˣ) :
    unitsCoeff F (σ * τ) z = unitsCoeff F τ (unitsCoeff F σ z) := by
  apply Units.ext
  simp [unitsCoeff, mul_inv_rev, AlgEquiv.mul_apply]

omit [IsAffineHom G.X.hom] in
private theorem rationalConjugate_left_fst (σ : K ≃ₐ[F] K)
    (u : rationalPoints (baseChanged F K G)) :
    (rationalConjugate F K G σ u).left ≫ Limits.pullback.fst G.X.hom (baseMap F K) =
      galoisBaseMap F K σ ≫ (u.left ≫ Limits.pullback.fst G.X.hom (baseMap F K)) := by
  have h := congrArg (fun p => p.left) (baseChangeCoeffEquiv_rationalConjugate F K G σ u)
  rw [baseChangeCoeffEquiv_left] at h
  change (rationalConjugate F K G σ u).left ≫ Limits.pullback.fst G.X.hom (baseMap F K) =
    galoisBaseMap F K σ ≫ (baseChangeCoeffEquiv F K G u).left at h
  rw [baseChangeCoeffEquiv_left] at h
  exact h

omit [IsAffineHom G.X.hom] in
/-- Maximal split tori stay maximal after base change along a map equal to `Spec e` for a ring
automorphism `e`. -/
private theorem isMaximalSplitTorus_baseChange_of_eq
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {H : GroupScheme (Spec (CommRingCat.of K))}
    {i : S.toGrp ⟶ H} (hi : IsMaximalSplitTorus i) (e : K ≃+* K)
    {b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K)}
    (hb : b = Spec.map (CommRingCat.ofHom e.toRingHom)) :
    IsMaximalSplitTorus (T := (CommGroupScheme.baseChange b).obj S)
      ((GroupScheme.baseChange b).map i) := by
  subst hb
  exact hi.baseChange_fieldIso e

/-! The charts are built for an arbitrary algebra structure of `K` over itself whose structure
map is `σ⁻¹`. Keeping that structure a variable keeps the kernel checks cheap; it is
instantiated only in the final statement, which does not mention it. -/

section Twisted

variable [Algebra K K]

omit [IsAffineHom G.X.hom] in
theorem baseMap_eq_galoisBaseMap {σ : K ≃ₐ[F] K} (halg : ∀ x : K, algebraMap K K x = σ⁻¹ x) :
    baseMap K K = galoisBaseMap F K σ⁻¹ :=
  congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (RingHom.ext fun x => halg x)

omit [IsAffineHom G.X.hom] in
theorem baseMap_self_over {σ : K ≃ₐ[F] K} (halg : ∀ x : K, algebraMap K K x = σ⁻¹ x) :
    baseMap K K ≫ baseMap F K = baseMap F K := by
  rw [baseMap_eq_galoisBaseMap halg]
  exact galoisBaseMap_over F K σ⁻¹

omit [IsAffineHom G.X.hom] in
private theorem selfExtend_left_fst (u : rationalPoints (baseChanged F K G)) :
    (rationalExtend K K (baseChanged F K G) u).left ≫
      Limits.pullback.fst (Limits.pullback.snd G.X.hom (baseMap F K)) (baseMap K K) =
      baseMap K K ≫ u.left := by
  rw [rationalExtend_eq_baseChangeBasePoint]
  exact baseChangeBasePoint_fst _ _ u

variable (G) in
/-- The descent isomorphism `G_K ×_{K,σ⁻¹} K ≅ G_K`. -/
def twistIso {σ : K ≃ₐ[F] K} (halg : ∀ x : K, algebraMap K K x = σ⁻¹ x) :
    baseChanged K K (baseChanged F K G) ≅ baseChanged F K G :=
  descentBaseChangeIso (baseMap F K) (baseMap K K) (baseMap_self_over halg) G

omit [IsAffineHom G.X.hom] in
private theorem twistIso_hom_fst {σ : K ≃ₐ[F] K} (halg : ∀ x : K, algebraMap K K x = σ⁻¹ x) :
    (twistIso G halg).hom.hom.hom.left ≫ Limits.pullback.fst G.X.hom (baseMap F K) =
      Limits.pullback.fst (Limits.pullback.snd G.X.hom (baseMap F K)) (baseMap K K) ≫
        Limits.pullback.fst G.X.hom (baseMap F K) :=
  descentBaseChangeIso_hom_fst (baseMap F K) (baseMap K K) (baseMap_self_over halg) G

omit [IsAffineHom G.X.hom] in
private theorem twistIso_map_left_fst {σ : K ≃ₐ[F] K}
    (halg : ∀ x : K, algebraMap K K x = σ⁻¹ x)
    (y : rationalPoints (baseChanged K K (baseChanged F K G))) :
    (rationalPoints.map (twistIso G halg).hom y).left ≫
        Limits.pullback.fst G.X.hom (baseMap F K) =
      y.left ≫ (Limits.pullback.fst (Limits.pullback.snd G.X.hom (baseMap F K)) (baseMap K K) ≫
        Limits.pullback.fst G.X.hom (baseMap F K)) :=
  (Category.assoc _ _ _).trans (congrArg (y.left ≫ ·) (twistIso_hom_fst halg))

omit [IsAffineHom G.X.hom] in
theorem twistIso_rationalExtend {σ : K ≃ₐ[F] K} (halg : ∀ x : K, algebraMap K K x = σ⁻¹ x)
    (u : rationalPoints (baseChanged F K G)) :
    rationalPoints.map (twistIso G halg).hom (rationalExtend K K (baseChanged F K G) u) =
      rationalConjugate F K G σ⁻¹ u := by
  apply (baseChangeCoeffEquiv F K G).injective
  apply Over.OverMorphism.ext
  rw [baseChangeCoeffEquiv_left, baseChangeCoeffEquiv_left, twistIso_map_left_fst,
    ← Category.assoc, selfExtend_left_fst, baseMap_eq_galoisBaseMap halg,
    rationalConjugate_left_fst, Category.assoc]

theorem selfAlgebra_isMaximalSplitTorus {v : Valuation K (WithZero (Multiplicative ℤ))}
    (C : IntegerValuationBuildingData v (baseChanged F K G)) {σ : K ≃ₐ[F] K}
    (halg : ∀ x : K, algebraMap K K x = σ⁻¹ x) :
    IsMaximalSplitTorus (T := (CommGroupScheme.baseChange (algebraBaseMap K K)).obj C.S)
      ((GroupScheme.baseChange (algebraBaseMap K K)).map C.i) :=
  isMaximalSplitTorus_baseChange_of_eq C.isMaximalSplitTorus (σ⁻¹).toRingEquiv
    (congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (RingHom.ext fun x => halg x))

theorem exists_selfFieldChart {v : Valuation K (WithZero (Multiplicative ℤ))}
    (C : IntegerValuationBuildingData v (baseChanged F K G)) {σ : K ≃ₐ[F] K}
    (halg : ∀ x : K, algebraMap K K x = σ⁻¹ x)
    (hbij : Function.Bijective (algebraMap K K))
    (horder : ∀ t : Kˣ, IntegerValuation.order v
      (Units.map (algebraMap K K).toMonoidHom t) = IntegerValuation.order v t)
    (hν : ∃ t : Kˣ, IntegerValuation.order v t ≠ 0) :
    ∃ g : rationalPoints (baseChanged F K G), Nonempty (C.FieldChart C
      (fun u => g * rationalConjugate F K G σ⁻¹ u * g⁻¹)) :=
  IntegerValuationBuildingData.exists_fieldChart C C (twistIso G halg)
    (rationalConjugate F K G σ⁻¹) (twistIso_rationalExtend halg) hbij horder hν
    (selfAlgebra_isMaximalSplitTorus C halg)

/-- Coefficient charts along `σ`, for a self-algebra structure through `σ⁻¹`. -/
theorem exists_coefficientChart_of_algebra {v : Valuation K (WithZero (Multiplicative ℤ))}
    (C : IntegerValuationBuildingData v (baseChanged F K G)) {σ : K ≃ₐ[F] K}
    (halg : ∀ x : K, algebraMap K K x = σ⁻¹ x)
    (horder : ∀ t : Kˣ, IntegerValuation.order v (Units.map (σ⁻¹).toMonoidHom t) =
      IntegerValuation.order v t)
    (hν : ∃ t : Kˣ, IntegerValuation.order v t ≠ 0) :
    Nonempty (C.apartment.CoefficientChart (rationalConjugate F K G σ) (unitsCoeff F σ)) := by
  have hunits : ∀ z : Kˣ, Units.map (algebraMap K K).toMonoidHom z = unitsCoeff F σ z :=
    fun z => Units.ext (halg z)
  have hbij : Function.Bijective (algebraMap K K) := by
    have : (algebraMap K K : K → K) = σ⁻¹ := funext halg
    rw [this]
    exact (σ⁻¹).bijective
  have horder' : ∀ t : Kˣ, IntegerValuation.order v
      (Units.map (algebraMap K K).toMonoidHom t) = IntegerValuation.order v t := by
    intro t
    rw [hunits]
    exact horder t
  obtain ⟨g, ⟨⟨β, τ, a, a_val, torus, char⟩⟩⟩ :=
    exists_selfFieldChart C halg hbij horder' hν
  have hθθ : ∀ w, rationalConjugate F K G σ⁻¹ (rationalConjugate F K G σ w) = w := by
    intro w
    rw [← rationalConjugate_mul, inv_mul_cancel, rationalConjugate_one]
  have hθθ' : ∀ w, rationalConjugate F K G σ (rationalConjugate F K G σ⁻¹ w) = w := by
    intro w
    rw [← rationalConjugate_mul, mul_inv_cancel, rationalConjugate_one]
  refine ⟨{
    c := rationalConjugate F K G σ g
    β := β
    a := a
    a_val := fun x b u => ?_
    τ := τ
    torus := fun t => ?_
    char := fun χ t => ?_ }⟩
  · rw [a_val]
    congr 1
    rw [map_mul, map_mul, map_inv, hθθ, hθθ]
    group
  · rw [← torus t, map_mul, map_mul, map_inv, hθθ']
    group
  · rw [char, hunits]

end Twisted

variable (F) in
/-- The algebra structure of `K` over itself through `σ⁻¹`. -/
abbrev twistAlgebra (σ : K ≃ₐ[F] K) : Algebra K K :=
  RingHom.toAlgebra (σ⁻¹).toRingHom

/-- **Coefficient charts for Galois automorphisms.** Let `v` be an integer valuation of `K`
whose order is invariant under `σ⁻¹ ∈ Aut(K/F)` and not identically zero. Then the apartment
of every building datum of `G_K` over `v` has a coefficient chart along `σ` acting on `G(K)`,
with `σ⁻¹` on `Kˣ`. -/
theorem exists_coefficientChart {v : Valuation K (WithZero (Multiplicative ℤ))}
    (C : IntegerValuationBuildingData v (baseChanged F K G)) (σ : K ≃ₐ[F] K)
    (horder : ∀ t : Kˣ, IntegerValuation.order v (Units.map (σ⁻¹).toMonoidHom t) =
      IntegerValuation.order v t)
    (hν : ∃ t : Kˣ, IntegerValuation.order v t ≠ 0) :
    Nonempty (C.apartment.CoefficientChart (rationalConjugate F K G σ) (unitsCoeff F σ)) :=
  @exists_coefficientChart_of_algebra F K _ _ _ G _ (twistAlgebra F σ) v C σ (fun _ => rfl)
    horder hν

end GaloisCharts

namespace MaximalUnramified

open Langlands.LocalGalois.Separable

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- **Coefficient charts on the unramified apartment.** For every `σ ∈ Aut(K/F)`, with `K`
the maximal unramified extension, the apartment of every building datum of `G_K` has a
coefficient chart along `σ` acting on `G(K)`, with `σ⁻¹` on `Kˣ`. -/
theorem exists_coefficientChart
    (C : BuildingData F (baseChanged F (inertiaFixedField F) G))
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    Nonempty (C.apartment.CoefficientChart (rationalConjugate F (inertiaFixedField F) G σ)
      (unitsCoeff F σ)) :=
  Building.exists_coefficientChart C σ (order_galois F σ⁻¹)
    (let ⟨t, ht⟩ := exists_order_eq_one F; ⟨t, by rw [ht]; exact one_ne_zero⟩)

variable (C : BuildingData F (baseChanged F (inertiaFixedField F) G))

/-- The chart along the identity coefficient automorphism. -/
def oneChart :
    C.apartment.CoefficientChart (rationalConjugateAction F (inertiaFixedField F) G 1)
      (unitsCoeff F 1) where
  c := 1
  β := Equiv.refl _
  a := id
  a_val x b u := by simp
  τ := Equiv.refl _
  torus t := by simp
  char χ t := by simp

open Classical in
/-- The chosen coefficient chart along `σ`, normalized to `oneChart` at `σ = 1`. -/
def coefficientChart (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    C.apartment.CoefficientChart (rationalConjugateAction F (inertiaFixedField F) G σ)
      (unitsCoeff F σ) :=
  if h : σ = 1 then h ▸ oneChart C else Classical.choice (exists_coefficientChart C σ)

theorem coefficientChart_one_c : (coefficientChart C 1).c = 1 := by
  simp [coefficientChart, oneChart]

theorem coefficientChart_one_a (x : C.Apartment) : (coefficientChart C 1).a x = x := by
  simp [coefficientChart, oneChart]

/-- The moving semilinear action data of the Galois action on the apartment of `C`: the
corrections and apartment maps of the coefficient charts. -/
def coefficientActionData :
    ApartmentQuotient.MovingSemilinearActionData C.apartment.sharpFixerFamily
      (rationalConjugateAction F (inertiaFixedField F) G) :=
  haveI : Infinite F := LocalField.infinite_of_isNonarchimedeanLocalField F
  haveI : Infinite (inertiaFixedField F) :=
    Infinite.of_injective (algebraMap F (inertiaFixedField F))
      (algebraMap F (inertiaFixedField F)).injective
  KPApartmentData.CoefficientChart.movingSemilinearActionData C.apartment
    C.isConnectedReductive C.isMaximalSplitTorus.1
    (rationalConjugateAction F (inertiaFixedField F) G) (unitsCoeff F)
    (fun σ τ z => unitsCoeff_mul σ τ z) (coefficientChart C) (coefficientChart_one_c C)
    (coefficientChart_one_a C)

@[simp] theorem coefficientActionData_correction
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    (coefficientActionData C).correction σ = (coefficientChart C σ).c :=
  rfl

@[simp] theorem coefficientActionData_apartment
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    (coefficientActionData C).apartment σ = (coefficientChart C σ).a :=
  rfl

end MaximalUnramified

end Langlands.Geometry.Building

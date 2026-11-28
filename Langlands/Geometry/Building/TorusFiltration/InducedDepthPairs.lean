import Langlands.BruhatTits.IntegralModels.InducedTorusShallowModel
import Langlands.Geometry.Building.TorusFiltration.TameDegree
import Langlands.Geometry.Building.TorusFiltration.WeilUnitReduction

/-! # First congruence of the induced coefficient models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.LocalField
open Langlands.LocalGalois.Separable
open scoped NNReal TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000
set_option quotPrecheck false

namespace Langlands.BruhatTits.IntegralModels

section WeilModel

variable (A K : Type u) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [IsLocalRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  {C : Type u} [CommRing C] [Algebra A C] [Module.Finite A C] [Module.Free A C]
  (J : Ideal C) (B : Type u) [CommRing B] [Algebra K B] [Module.Finite K B]
  (e : K ⊗[A] C ≃ₐ[K] B) (a : A) (ha : a ≠ 0) (hJ : algebraMap A C a ∈ J)

local notation "M" => WeilCongruence.integralModel A K J B e a ha hJ
local notation "W" => WeilGm.groupScheme (CommRingCat.of K) B

omit [IsLocalRing A] in
private theorem weilModel_integralPoint_val (x : (M).integralSections) :
    (WeilGm.rationalUnitsEquiv K B ((M).integralPointMap x) : B) =
      e (1 ⊗ₜ WeilCongruence.second A J (WeilCongruence.sectionUnit A J x)) := by
  let f := WeilCongruence.toAmbient A K J B e a ha hJ
  have h := f.integralPointMap_naturality x
  rw [rationalPoints.map_apply (𝟙 W), Grp.id_hom_hom, Category.comp_id] at h
  rw [← h, WeilGm.rationalUnitsEquiv_integralPointMap]
  have hf : rationalPoints.map f.hom x =
      rationalPoints.map (WeilCongruence.coefficientMap (WeilCongruence.second A J))
        (rationalPoints.map (GroupScheme.kernelι (WeilCongruence.quotient A J)) x) := by
    simp only [f, WeilCongruence.toAmbient, rationalPoints.map_apply,
      Grp.comp_hom_hom, Category.assoc]
  rw [hf, WeilCongruence.coefficientMap_sectionUnits]
  rfl

private def coefficientCongruence (J' : Ideal C) (x : rationalPoints W) : Prop :=
  ∃ w : Cˣ, (w : C) - 1 ∈ J' ∧ (WeilGm.rationalUnitsEquiv K B x : B) = e (1 ⊗ₜ (w : C))

private theorem weilModel_mem_congruenceSubgroup (J' : Ideal C) (hLe : J' ≤ J)
    (hInjective : Function.Injective (fun z : C => e (1 ⊗ₜ z)))
    (hPair : ∀ z : WeilCongruence.pairs A J, WeilCongruence.first A J z = 0 →
      (z ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A (WeilCongruence.pairs A J)) ↔
        WeilCongruence.second A J z ∈ J')) (x : rationalPoints W) :
    x ∈ (M).congruenceSubgroup ↔ coefficientCongruence A K B e J' x := by
  have hRed (y : (M).integralSections) : (M).reduction y = 1 ↔
      WeilCongruence.second A J (WeilCongruence.sectionUnit A J y) - 1 ∈ J' := by
    let w := WeilCongruence.sectionUnit A J y
    have hz : WeilCongruence.first A J ((w : WeilCongruence.pairs A J) - 1) = 0 := by
      rw [map_sub, map_one, WeilCongruence.first_sectionUnit, sub_self]
    change baseChangeSectionHom (IntegralModel.residueBaseMap A) (WeilCongruence.group A J) y = 1 ↔ _
    rw [WeilCongruence.reduction_eq_one_iff, hPair _ hz, map_sub, map_one]
  rw [IntegralModel.mem_congruenceSubgroup]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Units.map (WeilCongruence.second A J).toMonoidHom (WeilCongruence.sectionUnit A J y),
      (hRed y).mp hy, weilModel_integralPoint_val A K J B e a ha hJ y⟩
  · rintro ⟨w, hw, hx⟩
    obtain ⟨y, rfl⟩ := (WeilCongruence.mem_integralPoints_iff A K J B e a ha hJ x).mpr
      ⟨w, hLe hw, hx⟩
    refine ⟨y, (hRed y).mpr ?_, rfl⟩
    have h := hInjective ((weilModel_integralPoint_val A K J B e a ha hJ y).symm.trans hx)
    rwa [h]

private def weilDepthModelData (J' : Ideal C) (hLe : J' ≤ J)
    (hInjective : Function.Injective (fun z : C => e (1 ⊗ₜ z)))
    (hPair : ∀ z : WeilCongruence.pairs A J, WeilCongruence.first A J z = 0 →
      (z ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A (WeilCongruence.pairs A J)) ↔
        WeilCongruence.second A J z ∈ J')) :
    {N : IntegralModel A K W // N.IsSmooth ∧
      (∀ x : rationalPoints W, x ∈ N.integralPoints ↔ coefficientCongruence A K B e J x) ∧
      ∀ x : rationalPoints W, x ∈ N.congruenceSubgroup ↔ coefficientCongruence A K B e J' x} :=
  ⟨M, WeilCongruence.group_smooth A J, WeilCongruence.mem_integralPoints_iff A K J B e a ha hJ,
    weilModel_mem_congruenceSubgroup A K J B e a ha hJ J' hLe hInjective hPair⟩

end WeilModel

namespace InducedTorusShallow

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local notation "O" => fixedFieldIntegers F
local notation "K" => inertiaFixedField F
local notation "Ω" => SeparableClosure F
local notation "ν" => algebraicExtensionAddValuation F Ω
local notation "π" => baseUniformizer F

private local instance integersDVR : IsDiscreteValuationRing O :=
  fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)

variable {I : Type u} [Fintype I]
  (E : I → IntermediateField (inertiaFixedField F) (SeparableClosure F))
  [∀ i, FiniteDimensional (inertiaFixedField F) (E i)]

local notation "C" => productIntegers F E
local notation "B" => (∀ i, E i)
local notation "J" => depthIdeal F E
local notation "D" => fun r => WeilCongruence.pairs O (J r)

private local instance coefficientFieldAlgebra : ∀ i, Algebra K (E i) :=
  fun i => (E i).toSubalgebra.algebra
private local instance coefficientFieldModule : ∀ i, Module K (E i) := fun i =>
  @Algebra.toModule _ _ _ _ (E i).toSubalgebra.algebra
private local instance coefficientFieldSMul : ∀ i, SMul K (E i) :=
  fun i => (E i).toSubalgebra.algebra.toSMul
private local instance coefficientAlgebra : Algebra K B := Pi.algebra _ _
private local instance coefficientModule : Module K B := @Algebra.toModule _ _ _ _
  (coefficientAlgebra F E)
private local instance coefficientSMul : SMul K B := (coefficientAlgebra F E).toSMul
private local instance coefficientFinite : Module.Finite K B := Module.Finite.pi
private local instance coefficientProjective : Module.Projective K B :=
  Module.Projective.of_basis (Module.Basis.ofVectorSpace K B)

local notation "W" => WeilGm.commGroupScheme (CommRingCat.of K) B

omit [Fintype I] [∀ i, FiniteDimensional K (E i)] in
private theorem uniformizer_pow_mem_depthIdeal (r : ℝ≥0) :
    algebraMap O C (π ^ ⌈r⌉₊) ∈ J r := by
  rw [mem_depthIdeal]
  intro i
  change ((r : ℝ) : WithTop ℝ) ≤ ν ((((π : O) : K) : Ω) ^ ⌈r⌉₊)
  rw [AddValuation.map_pow, baseUniformizer_value, ← WithTop.coe_one, ← WithTop.coe_nsmul,
    WithTop.coe_le_coe, nsmul_one]
  exact_mod_cast Nat.le_ceil r

omit [Fintype I] [∀ i, FiniteDimensional K (E i)] in
private theorem mem_depthIdeal_add_one_iff (r : ℝ≥0) (z : C) :
    z ∈ J (r + 1) ↔ ∃ b ∈ J r, z = algebraMap O C π * b := by
  let π' (i : I) : E i := algebraMap K (E i) (π : K)
  have hπ (i : I) : ν (π' i : Ω) = 1 := baseUniformizer_value F
  have hπ₀ (i : I) : π' i ≠ 0 := by
    intro h
    have hv := hπ i
    simp [h] at hv
  have hmul (i : I) (x : E i) :
      ((↑(r + 1) : ℝ) : WithTop ℝ) ≤ ν ((π' i : Ω) * (x : Ω)) ↔
        ((r : ℝ) : WithTop ℝ) ≤ ν (x : Ω) := by
    rw [AddValuation.map_mul, hπ, NNReal.coe_add, NNReal.coe_one, WithTop.coe_add,
      WithTop.coe_one, add_comm ((r : ℝ) : WithTop ℝ),
      WithTop.add_le_add_iff_left (by simp : (1 : WithTop ℝ) ≠ ⊤)]
  constructor
  · intro hz
    let y (i : I) : E i := (z i : E i) / π' i
    have hy (i : I) : π' i * y i = z i := by
      rw [mul_comm, div_mul_cancel₀ _ (hπ₀ i)]
    have hdepth (i : I) : ((r : ℝ) : WithTop ℝ) ≤ ν (y i : Ω) := by
      apply (hmul i _).mp
      exact (congrArg (fun x : E i => ν (x : Ω)) (hy i)) ▸
        (mem_depthIdeal F E (r + 1) z).mp hz i
    let b (i : I) : ConnectedImage.integers F (E i) :=
      ⟨y i, (geometricValue_nonneg_iff F _).mp
        ((show (0 : WithTop ℝ) ≤ ((r : ℝ) : WithTop ℝ) by
          exact_mod_cast (show 0 ≤ r from zero_le)).trans (hdepth i))⟩
    exact ⟨b, (mem_depthIdeal F E r b).mpr hdepth, funext fun i => Subtype.ext (hy i).symm⟩
  · rintro ⟨b, hb, rfl⟩
    exact (mem_depthIdeal F E (r + 1) _).mpr fun i =>
      (hmul i (b i : E i)).mpr ((mem_depthIdeal F E r b).mp hb i)

omit [Fintype I] [∀ i, FiniteDimensional K (E i)] in
private theorem pair_mem_maximalIdeal_iff (r : ℝ≥0) (z : D r)
    (hz : WeilCongruence.first O (J r) z = 0) :
    z ∈ (IsLocalRing.maximalIdeal O).map (algebraMap O (D r)) ↔
      WeilCongruence.second O (J r) z ∈ J (r + 1) := by
  rw [maximalIdeal_eq_span_depthUniformizer F, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton, mem_depthIdeal_add_one_iff]
  constructor
  · rintro ⟨b, rfl⟩
    have hb : WeilCongruence.first O (J r) b = 0 := by
      rw [map_mul, AlgHom.commutes, Algebra.algebraMap_self] at hz
      exact (mul_eq_zero.mp hz).resolve_left (baseUniformizer_ne_zero F)
    have hmem := (WeilCongruence.mem_pairs O (J r) _).mp b.property
    change (b : O × C).1 = 0 at hb
    rw [hb, map_zero, sub_zero] at hmem
    refine ⟨WeilCongruence.second O (J r) b, hmem, ?_⟩
    rw [map_mul, AlgHom.commutes]
  · rintro ⟨b, hb, he⟩
    let d : D r := ⟨(0, b), (WeilCongruence.mem_pairs O (J r) _).mpr (by simpa using hb)⟩
    refine ⟨d, Subtype.ext (Prod.ext ?_ he)⟩
    change (z : O × C).1 = π * 0
    rw [mul_zero]
    exact hz

omit [∀ i, FiniteDimensional K (E i)] in
private theorem integralCoefficient_injective :
    Function.Injective (fun w : C => productTensorEquiv F E (1 ⊗ₜ w)) := by
  intro a b h
  funext i
  apply Subtype.ext
  have hi := congrFun h i
  simpa only [productTensorEquiv_tmul, map_one, one_mul] using hi

omit [Fintype I] [∀ i, FiniteDimensional K (E i)] in
private theorem depthIdeal_succ_le (r : ℝ≥0) : J (r + 1) ≤ J r := by
  intro w hw
  exact (mem_depthIdeal F E r _).mpr fun i =>
    (show ((r : ℝ) : WithTop ℝ) ≤ ((↑(r + 1) : ℝ) : WithTop ℝ) by
      exact_mod_cast (show r ≤ r + 1 from le_add_of_nonneg_right zero_le)).trans
      ((mem_depthIdeal F E (r + 1) _).mp hw i)

private def depthModelData (r : ℝ≥0) :=
  weilDepthModelData O K (J r) B (productTensorEquiv F E) (π ^ ⌈r⌉₊)
    (pow_ne_zero _ (baseUniformizer_ne_zero F)) (uniformizer_pow_mem_depthIdeal F E r)
    (J (r + 1)) (depthIdeal_succ_le F E r) (integralCoefficient_injective F E)
    (pair_mem_maximalIdeal_iff F E r)

/-- The Weil congruence pair model with the ideal at an arbitrary depth. -/
def depthModel (r : ℝ≥0) : IntegralModel O K (W).toGrp := (depthModelData F E r).val

theorem depthModel_smooth (r : ℝ≥0) : (depthModel F E r).IsSmooth :=
  (depthModelData F E r).property.1

/-- A point of the coefficient model is an integral unit with difference from
one in the depth ideal. -/
theorem mem_depthModel (r : ℝ≥0) (x : rationalPoints (W).toGrp) :
    x ∈ (depthModel F E r).integralPoints ↔ ∃ w : Cˣ, (w : C) - 1 ∈ J r ∧
      (WeilGm.rationalUnitsEquiv K B x : B) = productTensorEquiv F E (1 ⊗ₜ (w : C)) :=
  (depthModelData F E r).property.2.1 x

/-- Reducing the depth model to the identity raises the coefficient depth by
one in the valuation normalized over the base field. -/
theorem depthModel_congruenceSubgroup (r : ℝ≥0) :
    (depthModel F E r).congruenceSubgroup = (depthModel F E (r + 1)).integralPoints :=
  Subgroup.ext fun x => ((depthModelData F E r).property.2.2 x).trans
    ((depthModelData F E (r + 1)).property.2.1 x).symm

omit [Fintype I] [∀ i, FiniteDimensional K (E i)] in
/-- A tuple with unit valuation in every coordinate comes from a unit of the
product of the valuation rings. -/
private theorem exists_integralCoefficient (w : B)
    (hw : ∀ i, intermediateValuation F (E i) (w i) = 1) :
    ∃ v : Cˣ, ∀ i, (v.val i : E i) = w i := by
  let z (i : I) : ConnectedImage.integers F (E i) := ⟨w i, (hw i).le⟩
  have hz (i : I) : IsUnit (z i) := (ConnectedImage.isUnit_integers_iff F (E i) _).mpr (hw i)
  let v : Cˣ := MulEquiv.piUnits.symm (fun i => (hz i).unit)
  refine ⟨v, fun i => ?_⟩
  have hv : v.val i = z i := by
    change (MulEquiv.piUnits v i).val = z i
    rw [MulEquiv.apply_symm_apply]
    exact IsUnit.unit_spec _
  exact congrArg Subtype.val hv

/-- At depth zero every tuple of valuation-ring units is an integral point of
the coefficient model. -/
theorem mem_depthModel_zero_of_coordinate_valuation (t : rationalPoints (W).toGrp)
    (ht : ∀ i, intermediateValuation F (E i)
      ((WeilGm.rationalUnitsEquiv K B t).val i) = 1) :
    t ∈ (depthModel F E 0).integralPoints := by
  obtain ⟨v, hv⟩ := exists_integralCoefficient F E _ ht
  refine (mem_depthModel F E 0 t).mpr ⟨v, (mem_depthIdeal F E 0 _).mpr ?_, ?_⟩
  · intro i
    exact (geometricValue_nonneg_iff F _).mpr (v.val i - 1).property
  · funext i
    rw [productTensorEquiv_tmul, map_one, one_mul, hv i]

/-- At positive depth the coefficient model realizes the geometric-character
inequality on the induced torus. -/
theorem depthModel_integralPoints_positive (r : ℝ≥0) (hr : 0 < r) :
    (depthModel F E r).integralPoints = localGeometricCharacterCongruence F W r := by
  refine Subgroup.ext fun (t : rationalPoints (W).toGrp) => ?_
  rw [mem_depthModel, mem_geometricCharacterCongruence_iff F E r hr]
  let w := WeilGm.rationalUnitsEquiv K B t
  have hcoeff (v : Cˣ) (i : I) :
      productTensorEquiv F E (1 ⊗ₜ (v : C)) i = (v.val i : E i) := by
    rw [productTensorEquiv_tmul, map_one, one_mul]
  constructor
  · rintro ⟨v, hv, ht⟩ i
    rw [(congrFun ht i).trans (hcoeff v i)]
    exact (mem_depthIdeal F E r _).mp hv i
  · intro ht
    have hv (i : I) : intermediateValuation F (E i) (w.val i) = 1 := by
      let a := Units.map (E i).val.toMonoidHom (MulEquiv.piUnits w i)
      have ha : ((r : ℝ) : WithTop ℝ) ≤ ν ((a : Ω) - 1) := ht i
      have h0 := ((mem_addValuationUnitFiltration_of_pos ν hr a).mpr ha).1
      change negativeLogValue (localLogScale F) (intermediateValuation F (E i) (w.val i)) = 0 at h0
      exact (negativeLogValue_eq_zero_iff (localLogScale_pos F) _).mp h0
    obtain ⟨v, hvi⟩ := exists_integralCoefficient F E w.val hv
    refine ⟨v, (mem_depthIdeal F E r _).mpr ?_, funext fun i =>
      (hvi i).symm.trans (hcoeff v i).symm⟩
    intro i
    change ((r : ℝ) : WithTop ℝ) ≤ ν (((v.val i : E i) : Ω) - 1)
    rw [hvi i]
    exact ht i

end InducedTorusShallow
end Langlands.BruhatTits.IntegralModels

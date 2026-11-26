import Langlands.BruhatTits.IntegralModels.InducedTorusShallowCharacters
import Langlands.BruhatTits.IntegralModels.InducedTorusShallowIntegers
import Langlands.BruhatTits.IntegralModels.WeilCongruenceModel
import Langlands.GroupScheme.IntegralModel.Iso
import Langlands.GroupScheme.IntegralModelReduction

/-! # Shallow positive-depth standard models of induced tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.LocalField
open Langlands.LocalGalois.Separable
open scoped NNReal TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000
set_option quotPrecheck false

namespace Langlands.BruhatTits.IntegralModels

private def checkedWeilModel (A K : Type u) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    {C : Type u} [CommRing C] [Algebra A C] [Module.Finite A C] [Module.Free A C]
    (J : Ideal C) (B : Type u) [CommRing B] [Algebra K B] [Module.Finite K B]
    (e : K ⊗[A] C ≃ₐ[K] B) (a : A) (ha : a ≠ 0) (hJ : algebraMap A C a ∈ J) :
    {M : IntegralModel A K (WeilGm.groupScheme (CommRingCat.of K) B) //
      M.IsSmooth ∧ M.HasGeometricallyConnectedFibres ∧
        ∀ y : rationalPoints (WeilGm.groupScheme (CommRingCat.of K) B),
          y ∈ M.integralPoints ↔ ∃ w : Cˣ, (w : C) - 1 ∈ J ∧
            (WeilGm.rationalUnitsEquiv K B y : B) = e (1 ⊗ₜ (w : C))} :=
  ⟨WeilCongruence.integralModel A K J B e a ha hJ, WeilCongruence.group_smooth A J,
    WeilCongruence.group_geometricallyConnected A J, WeilCongruence.mem_integralPoints_iff A K J B e a ha hJ⟩

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local notation "O" => fixedFieldIntegers F
local notation "K" => inertiaFixedField F
local notation "Ω" => SeparableClosure F
local notation "ν" => algebraicExtensionAddValuation F (SeparableClosure F)

namespace InducedTorusShallow

section Factors

variable {I : Type u} [Fintype I] (E : I → IntermediateField (inertiaFixedField F) (SeparableClosure F))
  [∀ i, FiniteDimensional (inertiaFixedField F) (E i)]

local notation "C" => productIntegers F E
local notation "B" => (∀ i, E i)
private local instance modelFactorFieldAlgebra : ∀ i, Algebra K (E i) := fun i => (E i).toSubalgebra.algebra
private local instance modelFactorFieldModule : ∀ i, Module K (E i) := fun i =>
  @Algebra.toModule _ _ _ _ (E i).toSubalgebra.algebra
private local instance modelFactorFieldSMul : ∀ i, SMul K (E i) := fun i => (E i).toSubalgebra.algebra.toSMul
private local instance coefficientAlgebra : Algebra K B := Pi.algebra _ _
private local instance modelFieldProductModule : Module K B := @Algebra.toModule _ _ _ _ (coefficientAlgebra F E)
private local instance modelFieldProductSMul : SMul K B := (coefficientAlgebra F E).toSMul
private local instance modelFieldProductFinite : Module.Finite K B := Module.Finite.pi
private local instance modelFieldProductProjective : Module.Projective K B :=
  Module.Projective.of_basis (Module.Basis.ofVectorSpace K B)

local notation "W" => WeilGm.commGroupScheme (CommRingCat.of K) B

private def factorModelData (r : ℝ≥0) (hr : r < 1) :=
  checkedWeilModel O K (depthIdeal F E r) B (productTensorEquiv F E)
    (baseUniformizer F) (baseUniformizer_ne_zero F) (baseUniformizer_mem_depthIdeal F E r hr)

/-- The shallow standard model for the multiplicative restriction from a
finite product of embedded finite separable fields. -/
def modelOfFactors (r : ℝ≥0) (hr : r < 1) : IntegralModel O K (W).toGrp :=
  (factorModelData F E r hr).val

theorem modelOfFactors_smooth (r : ℝ≥0) (hr : r < 1) :
    (modelOfFactors F E r hr).IsSmooth :=
  (factorModelData F E r hr).property.1

theorem modelOfFactors_geometricallyConnected (r : ℝ≥0) (hr : r < 1) :
    (modelOfFactors F E r hr).HasGeometricallyConnectedFibres :=
  (factorModelData F E r hr).property.2.1

omit [Fintype I] [∀ i, FiniteDimensional (inertiaFixedField F) (E i)] in
private theorem coordinate_units (r : ℝ≥0) (hr : 0 < r) (w : Bˣ)
    (h : ∀ i, ((r : ℝ) : WithTop ℝ) ≤ ν (((w : B) i : Ω) - 1)) :
    ∃ v : Cˣ, (v : C) - 1 ∈ depthIdeal F E r ∧
      ∀ i, (v.val i : E i) = w.val i := by
  have hv (i : I) : intermediateValuation F (E i) (w.val i) = 1 := by
    let t := Units.map (E i).val.toMonoidHom (MulEquiv.piUnits w i)
    have ht : ((r : ℝ) : WithTop ℝ) ≤ ν ((t : Ω) - 1) := h i
    have h0 := ((mem_addValuationUnitFiltration_of_pos ν hr t).mpr ht).1
    change negativeLogValue (localLogScale F) (intermediateValuation F (E i) (w.val i)) = 0 at h0
    exact (negativeLogValue_eq_zero_iff (localLogScale_pos F) _).mp h0
  let z (i : I) : ConnectedImage.integers F (E i) :=
    ⟨w.val i, (ConnectedImage.mem_integers_iff F (E i) _).mpr (hv i).le⟩
  have hz (i : I) : IsUnit (z i) := (ConnectedImage.isUnit_integers_iff F (E i) _).mpr (hv i)
  let v : Cˣ := MulEquiv.piUnits.symm (fun i => (hz i).unit)
  have hvz : (v : C) = z := by
    funext i
    change (MulEquiv.piUnits v i).val = z i
    rw [MulEquiv.apply_symm_apply]
    exact IsUnit.unit_spec _
  refine ⟨v, ?_, fun i => congrArg (fun f : C => (f i : E i)) hvz⟩
  rw [hvz, mem_depthIdeal]
  exact h

omit [∀ i, FiniteDimensional (inertiaFixedField F) (E i)] in
private theorem coordinate_congruence_iff (r : ℝ≥0) (hr : 0 < r) (t : Bˣ) :
    (∃ w : Cˣ, (w : C) - 1 ∈ depthIdeal F E r ∧
      (t : B) = productTensorEquiv F E (1 ⊗ₜ (w : C))) ↔
    ∀ i, ((r : ℝ) : WithTop ℝ) ≤ ν (((t : B) i : Ω) - 1) := by
  have hcoeff (w : Cˣ) (i : I) :
      productTensorEquiv F E (1 ⊗ₜ (w : C)) i = (w.val i : E i) := by
    rw [productTensorEquiv_tmul, map_one, one_mul]
  constructor
  · rintro ⟨w, hw, ht⟩ i
    have hti := (congrFun ht i).trans (hcoeff w i)
    rw [hti]
    exact (mem_depthIdeal F E r _).1 hw i
  · intro ht
    obtain ⟨w, hw, hwi⟩ := coordinate_units F E r hr t ht
    exact ⟨w, hw, funext fun i => (hwi i).symm.trans (hcoeff w i).symm⟩

private theorem mem_factorModel (r : ℝ≥0) (hr₁ : r < 1)
    (t : rationalPoints (W).toGrp) :
    t ∈ (modelOfFactors F E r hr₁).integralPoints ↔
      ∃ w : Cˣ, (w : C) - 1 ∈ depthIdeal F E r ∧
        (WeilGm.rationalUnitsEquiv K B t : B) = productTensorEquiv F E (1 ⊗ₜ (w : C)) :=
  (factorModelData F E r hr₁).property.2.2 t

/-- The actual model image equals the geometric-character subgroup at the
same normalized depth. -/
theorem modelOfFactors_integralPoints (r : ℝ≥0) (hr : 0 < r) (hr₁ : r < 1) :
    (modelOfFactors F E r hr₁).integralPoints = localGeometricCharacterCongruence F W r := by
  refine Subgroup.ext (fun (t : rationalPoints (W).toGrp) => ?_)
  have hCoordinate := coordinate_congruence_iff F E r hr (WeilGm.rationalUnitsEquiv K B t)
  have hCharacter := mem_geometricCharacterCongruence_iff F E r hr t
  exact (mem_factorModel F E r hr₁ t).trans (hCoordinate.trans hCharacter.symm)

end Factors

section Transport

private theorem characterCongruence_map_iso
    {W R : CommGroupScheme (Spec (CommRingCat.of K))} (e : W.toGrp ≅ R.toGrp) (r : ℝ≥0) :
    (localGeometricCharacterCongruence F W r).map (rationalPoints.map e.hom) =
      localGeometricCharacterCongruence F R r := by
  apply le_antisymm (map_extendedCharacterCongruence_le K Ω ν W.toGrp e.hom r)
  intro t ht
  have h : rationalPoints.map e.inv t ∈ localGeometricCharacterCongruence F W r :=
    map_extendedCharacterCongruence_le K Ω ν R.toGrp e.inv r ⟨t, ht, rfl⟩
  refine ⟨_, h, ?_⟩
  simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
    e.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

/-- A smooth affine model with geometrically connected fibres and the exact
positive-depth subgroup, for an arbitrary induced torus at depth `0 < r < 1`. -/
def standardModel
    (R : CommGroupScheme (Spec (CommRingCat.of K)))
    (r : ℝ≥0) (hR : IsInducedTorus R) (hr : 0 < r) (hr₁ : r < 1) :
    {M : IntegralModel O K R.toGrp // M.IsSmooth ∧ M.HasGeometricallyConnectedFibres ∧
      M.integralPoints = localGeometricCharacterCongruence F R r} := Classical.choice (by
  classical
  let S := localTorusSplittingData F R hR.isTorus
  obtain ⟨n, E, ⟨e⟩⟩ := inducedTorusWeilDecomposition K S.L R S.splits hR
  let I := ULift.{u} (Fin n)
  let q : I ≃ Fin n := Equiv.ulift
  let LtoOmega := IsScalarTower.toAlgHom K S.L Ω
  let D (i : I) := (E (q i)).map LtoOmega
  let j (i : I) : E (q i) ≃ₐ[K] D i := (E (q i)).equivMap LtoOmega
  let : ∀ i, Algebra K (E (q i)) := fun i => (E (q i)).toSubalgebra.algebra
  let : ∀ i, Module K (E (q i)) := fun i =>
    @Algebra.toModule _ _ _ _ (E (q i)).toSubalgebra.algebra
  let : ∀ i, SMul K (E (q i)) := fun i => (E (q i)).toSubalgebra.algebra.toSMul
  let : ∀ i, Algebra K (D i) := fun i => (D i).toSubalgebra.algebra
  let : ∀ i, Module K (D i) := fun i => @Algebra.toModule _ _ _ _ (D i).toSubalgebra.algebra
  let : ∀ i, SMul K (D i) := fun i => (D i).toSubalgebra.algebra.toSMul
  let A₀ : Algebra K (∀ i : Fin n, E i) := Pi.algebra _ _
  let A₁ : Algebra K (∀ i : I, E (q i)) := Pi.algebra _ _
  let A₂ : Algebra K (∀ i : I, D i) := Pi.algebra _ _
  let : Module K (∀ i : Fin n, E i) := @Algebra.toModule _ _ _ _ A₀
  let : Module K (∀ i : I, E (q i)) := @Algebra.toModule _ _ _ _ A₁
  let : Module K (∀ i : I, D i) := @Algebra.toModule _ _ _ _ A₂
  let : SMul K (∀ i : Fin n, E i) := A₀.toSMul
  let : SMul K (∀ i : I, E (q i)) := A₁.toSMul
  let : SMul K (∀ i : I, D i) := A₂.toSMul
  let : ∀ i, FiniteDimensional K (E i) := fun i => IntermediateField.finiteDimensional_left (E i)
  let : ∀ i, FiniteDimensional K (D i) := fun i => Module.Finite.equiv (j i).toLinearEquiv
  let : Module.Finite K (∀ i : Fin n, E i) := Module.Finite.pi
  let : Module.Finite K (∀ i : I, D i) := Module.Finite.pi
  let : Module.Projective K (∀ i : Fin n, E i) :=
    Module.Projective.of_basis (Module.Basis.ofVectorSpace K _)
  let : Module.Projective K (∀ i : I, D i) :=
    Module.Projective.of_basis (Module.Basis.ofVectorSpace K _)
  let reindex : (∀ i : Fin n, E i) ≃ₐ[K] (∀ i : I, E (q i)) :=
    (AlgEquiv.piCongrLeft K (fun i : Fin n => E i) q).symm
  let eB := reindex.trans (AlgEquiv.piCongrRight j)
  let W := WeilGm.commGroupScheme (CommRingCat.of K) (∀ i : I, D i)
  let eW : R ≅ W := e ≪≫ WeilGm.commCongrIso eB
  let d : W.toGrp ≅ R.toGrp :=
    { hom := CommGroupScheme.groupHom eW.inv
      inv := CommGroupScheme.groupHom eW.hom
      hom_inv_id := congrArg CommGroupScheme.groupHom eW.inv_hom_id
      inv_hom_id := congrArg CommGroupScheme.groupHom eW.hom_inv_id }
  let N := modelOfFactors F D r hr₁
  let M : IntegralModel O K R.toGrp := { N with genericIso := N.genericIso ≪≫ d }
  let hM : N.Iso M d :=
    { iso := CategoryTheory.Iso.refl _
      generic_comm := by simp [M] }
  refine ⟨⟨M, modelOfFactors_smooth F D r hr₁,
    modelOfFactors_geometricallyConnected F D r hr₁, ?_⟩⟩
  rw [← hM.map_integralPoints, modelOfFactors_integralPoints F D r hr hr₁]
  exact characterCongruence_map_iso F d r)

end Transport
end InducedTorusShallow
end Langlands.BruhatTits.IntegralModels

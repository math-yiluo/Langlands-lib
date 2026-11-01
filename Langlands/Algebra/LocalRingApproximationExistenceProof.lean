import Langlands.Algebra.LocalRingApproximationExistenceStatement
import Langlands.Algebra.LocalAlgebraApproximationExistence
import Langlands.Algebra.PrimeLocalizationCriterion

/-! # Independent existence of identity local-ring approximation systems -/

universe u v

open scoped TensorProduct

namespace Langlands.Algebra

namespace LocalRingApproximationExistence

open LocalAlgebraApproximationExistence

section Construction

variable {R₀ : Type v} {R : Type u} [CommRing R₀] [CommRing R]
  [IsLocalRing R₀] [IsLocalRing R] (e : R₀ ≃+* R)

local instance : IsLocalHom (algebraMap R R) := isLocalHom_id R

/-- The finite local subring used for both components of the identity system. -/
abbrev B (i : Finset R₀) : Subring R₀ := locSub ∅ i

/-- The same inclusion supplies both transition maps. -/
def transition {i j : Finset R₀} (h : i ≤ j) : B i →+* B j :=
  Subring.inclusion (locSub_mono ∅ h)

instance transition_local {i j : Finset R₀} (h : i ≤ j) :
    IsLocalHom (transition h) := by
  have : IsLocalHom ((B j).subtype.comp (transition h)) := by
    change IsLocalHom (B i).subtype
    infer_instance
  exact isLocalHom_of_comp _ (B j).subtype

/-- The inclusion of a stage into the original ambient ring. -/
def cocone (i : Finset R₀) : B i →+* R :=
  e.toRingHom.comp (B i).subtype

instance cocone_local (i : Finset R₀) : IsLocalHom (cocone e i) := by
  have : IsLocalHom e.toRingHom := IsLocalHom.of_surjective _ e.surjective
  unfold cocone
  infer_instance

/-- The independent base-ring system, with identity component algebras. -/
def system : LocalAlgebraSystem (Finset R₀) R R where
  base i := B i
  alg i := B i
  baseCommRing i := inferInstanceAs (CommRing (B i))
  algCommRing i := inferInstanceAs (CommRing (B i))
  baseLocalRing i := inferInstanceAs (IsLocalRing (B i))
  algLocalRing i := inferInstanceAs (IsLocalRing (B i))
  componentAlgebra i := Algebra.id (B i)
  structure_local i := isLocalHom_id (B i)
  baseMap _ _ h := transition h
  algMap _ _ h := transition h
  base_directed := ⟨fun _ _ ↦ rfl, fun _ _ _ _ _ _ ↦ rfl⟩
  alg_directed := ⟨fun _ _ ↦ rfl, fun _ _ _ _ _ _ ↦ rfl⟩
  baseMap_local _ _ h := transition_local h
  algMap_local _ _ h := transition_local h
  map_comm _ _ _ _ := rfl
  baseι := cocone e
  algι := cocone e
  baseι_local := cocone_local e
  algι_local := cocone_local e
  baseι_compat _ _ _ _ := rfl
  algι_compat _ _ _ _ := rfl
  ι_comm _ _ := rfl

/-- Both actual direct-limit comparisons are bijective. -/
theorem system_isColimit : (system e).IsColimit := by
  classical
  have hinj : Function.Injective (system e).baseColimitMap :=
    Ring.DirectLimit.lift_injective _ _ _ fun _ _ _ h ↦ Subtype.ext (e.injective h)
  have hsurj : Function.Surjective (system e).baseColimitMap := by
    intro r
    let b : (system e).base {e.symm r} :=
      ⟨e.symm r, mem_locSub_of_mem_right ∅ (by simp)⟩
    exact ⟨Ring.DirectLimit.of _ _ _ b,
      (LocalAlgebraSystem.baseColimitMap_of _ _ b).trans (e.apply_symm_apply r)⟩
  exact ⟨⟨hinj, hsurj⟩, ⟨hinj, hsurj⟩⟩

/-- The actual tensor transition is the canonical left identity equivalence. -/
theorem ringBaseChangeMap_eq_lid {i j : Finset R₀} (h : i ≤ j) :
    letI := ((system e).baseMap i j h).toAlgebra
    (system e).ringBaseChangeMap h =
      (_root_.Algebra.TensorProduct.lid
        ((system e).base i) ((system e).base j)).toRingHom := by
  let := ((system e).baseMap i j h).toAlgebra
  apply _root_.Algebra.TensorProduct.ringHom_ext
  · ext s
    change transition h s * 1 = transition h s * 1
    rfl
  · ext r
    change (system e).ringBaseChangeMap h ((1 : (system e).alg i) ⊗ₜ r) =
      _root_.Algebra.TensorProduct.lid
        ((system e).base i) ((system e).base j) (1 ⊗ₜ r)
    simp only [LocalAlgebraSystem.ringBaseChangeMap_tmul, map_one, one_mul,
      _root_.Algebra.TensorProduct.lid_tmul, one_smul]
    rfl

/-- Prime localization holds for the algebra induced by the actual transition. -/
theorem system_isPrimeLocalization {i j : Finset R₀} (h : i ≤ j) :
    (system e).IsPrimeLocalization h := by
  let := ((system e).baseMap i j h).toAlgebra
  have hbij : Function.Bijective ((system e).ringBaseChangeMap h) := by
    rw [ringBaseChangeMap_eq_lid]
    exact (_root_.Algebra.TensorProduct.lid
      ((system e).base i) ((system e).base j)).bijective
  let := ((system e).ringBaseChangeMap h).toAlgebra
  refine ⟨(IsLocalRing.maximalIdeal ((system e).alg j)).comap
    ((system e).ringBaseChangeMap h),
    inferInstance, ?_⟩
  apply isLocalization_atPrime_of_fractions
  · intro b
    obtain ⟨a, ha⟩ := hbij.surjective b
    refine ⟨a, 1, by simp, ?_⟩
    change b * (system e).ringBaseChangeMap h 1 = (system e).ringBaseChangeMap h a
    simpa only [map_one, mul_one] using ha.symm
  · intro a ha
    change (system e).ringBaseChangeMap h a = 0 at ha
    refine ⟨1, by simp, ?_⟩
    simpa using hbij.injective (ha.trans (map_zero _).symm)

/-- All four approximation clauses for the independent identity system. -/
theorem system_isApproximation : (system e).IsApproximation := by
  refine ⟨system_isColimit e, fun i ↦ essFiniteType_locSub ∅ i,
    ?_, fun _ _ h ↦ system_isPrimeLocalization e h⟩
  intro i
  change _root_.Algebra.EssFiniteType (B i) (B i)
  infer_instance

end Construction

end LocalRingApproximationExistence

/-- Every local ring admits an approximation system for its identity algebra,
constructed independently from finite local subrings. -/
theorem localRingApproximationExistence :
    LocalRingApproximationExistenceStatement.{u, v} := by
  intro R _ _
  exact ⟨Finset (ULift.{v} R), inferInstance, ⟨∅⟩, inferInstance,
    LocalRingApproximationExistence.system
      (ULift.ringEquiv : ULift.{v} R ≃+* R),
    LocalRingApproximationExistence.system_isApproximation
      (ULift.ringEquiv : ULift.{v} R ≃+* R)⟩

end Langlands.Algebra

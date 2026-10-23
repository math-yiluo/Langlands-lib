import Langlands.Automorphic.FiniteRealization
import Langlands.Global.FiniteAdelicGL.LocalTensorSeparation

/-! # Local comparison for finite tensor realizations in automorphic forms -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV

namespace Langlands.Automorphic.FiniteTensorRealization

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor
open ContinuousRationalFunctions

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorRealizationRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance tensorRealizationContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorRealizationSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorRealizationFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

variable (ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v))
variable (E : Finset (FinitePlace F)) (e : ∀ v, V v)
variable (he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v)

/-- Actual form-valued intertwiners from the constructed finite adelic tensor action. -/
abbrev Map := FiniteRealizationMap F n (tensorRepresentation F n ρ E e he)

/-- Faithfulness is a property of the supplied intertwiner. -/
abbrev IsInjective (T : Map F n ρ E e he) : Prop := Function.Injective T

/-- Local maps with the entire complementary tensor space retained. -/
abbrev LocalMap (v : FinitePlace F) :=
  (separatedLocalRepresentation F n ρ E v e).IntertwiningMap
    (automorphicLocalRightAction F n v)

variable (hne : ∀ v ∉ E, e v ≠ 0)

/-- Reassemble the tensor and apply the given actual form-valued map. -/
def localMap (T : Map F n ρ E e he) (v : FinitePlace F) : LocalMap F n ρ E e v :=
  let Tlocal : (tensorLocalRepresentation F n ρ E e he v).IntertwiningMap
      (automorphicLocalRightAction F n v) :=
    { toLinearMap := T.toLinearMap
      isIntertwining' g := T.isIntertwining' (localInclusion F n v g) }
  Tlocal.comp (localTensorSeparation F n ρ E e he hne v).symm.toIntertwiningMap

@[simp]
theorem localMap_apply (T : Map F n ρ E e he) (v : FinitePlace F)
    (z : V v ⊗[ℂ] LocalTensorTail (K := ℂ) F E v e) :
    localMap F n ρ E e he hne T v z =
      T ((localTensorSeparation F n ρ E e he hne v).symm z) := rfl

/-- Separating before the local map recovers the original realization. -/
@[simp]
theorem localMap_separate (T : Map F n ρ E e he) (v : FinitePlace F)
    (z : Space ℂ V E e) :
    localMap F n ρ E e he hne T v (localTensorSeparation F n ρ E e he hne v z) =
      T z := by
  rw [localMap_apply, Representation.Equiv.symm_apply_apply]

/-- The separated map has precisely the original form-valued image. -/
theorem mem_image_iff (T : Map F n ρ E e he) (v : FinitePlace F)
    (f : AutomorphicForms F n) :
    f ∈ finiteRealizationImage F n T ↔
      ∃ z, localMap F n ρ E e he hne T v z = f := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨localTensorSeparation F n ρ E e he hne v x,
      localMap_separate F n ρ E e he hne T v x⟩
  · rintro ⟨z, rfl⟩
    exact ⟨(localTensorSeparation F n ρ E e he hne v).symm z, rfl⟩

/-- Containment of the full realized image can be checked on separated tensors.
In particular this applies to the published character and cuspidal subspaces. -/
theorem image_le_iff (T : Map F n ρ E e he) (v : FinitePlace F)
    (S : FiniteRealization F n) :
    finiteRealizationImage F n T ≤ S ↔
      ∀ z, localMap F n ρ E e he hne T v z ∈ S := by
  constructor
  · intro h z
    exact h ((mem_image_iff F n ρ E e he hne T v _).mpr ⟨z, rfl⟩)
  · intro h f hf
    obtain ⟨z, rfl⟩ := (mem_image_iff F n ρ E e he hne T v f).mp hf
    exact h z

/-- Injectivity is unchanged by separating and reassembling one factor. -/
theorem localMap_injective_iff (T : Map F n ρ E e he) (v : FinitePlace F) :
    Function.Injective (localMap F n ρ E e he hne T v) ↔
      IsInjective F n ρ E e he T := by
  constructor
  · intro h x y hxy
    apply (localTensorSeparation F n ρ E e he hne v).injective
    apply h
    change localMap F n ρ E e he hne T v
        (localTensorSeparation F n ρ E e he hne v x) =
      localMap F n ρ E e he hne T v
        (localTensorSeparation F n ρ E e he hne v y)
    simpa only [localMap_separate] using hxy
  · intro h
    exact h.comp (localTensorSeparation F n ρ E e he hne v).symm.injective

/-- The comparison target is the whole image with its actual local restriction. -/
abbrev LocalImageEquivalence (T : Map F n ρ E e he) (v : FinitePlace F) :=
  (separatedLocalRepresentation F n ρ E v e).Equiv
    ((finiteRealizationImage F n T).localRepresentation v)

/-- A faithful tensor realization gives a genuine local equivalence onto its image. -/
def localImageEquiv (T : Map F n ρ E e he) (hT : IsInjective F n ρ E e he T)
    (v : FinitePlace F) : LocalImageEquivalence F n ρ E e he T v :=
  (localTensorSeparation F n ρ E e he hne v).symm.trans
    (Representation.Equiv.mk (finiteRealizationImageEquiv F n T hT).toLinearEquiv
      (fun g => (finiteRealizationImageEquiv F n T hT).isIntertwining'
        (localInclusion F n v g)))

@[simp]
theorem inclusion_localImageEquiv (T : Map F n ρ E e he)
    (hT : IsInjective F n ρ E e he T) (v : FinitePlace F)
    (z : V v ⊗[ℂ] LocalTensorTail (K := ℂ) F E v e) :
    (finiteRealizationImage F n T).inclusion
        (localImageEquiv F n ρ E e he hne T hT v z) =
      localMap F n ρ E e he hne T v z := rfl

include hne in
/-- Faithful occurrence in forms forces smoothness of the separated local action. -/
theorem separated_isSmooth (T : Map F n ρ E e he)
    (hT : IsInjective F n ρ E e he T) (v : FinitePlace F) :
    Langlands.IsSmooth (separatedLocalRepresentation F n ρ E v e) :=
  Langlands.isSmooth_of_injective (localMap F n ρ E e he hne T v)
    ((localMap_injective_iff F n ρ E e he hne T v).mpr hT)
    (automorphicLocalRightAction_isSmooth F n v)

/-- The local component acts on the first tensor coordinate, as actual right translation. -/
theorem evaluate_localMap_tmul (T : Map F n ρ E e he) (v : FinitePlace F)
    (g : FiniteLocalGL F n v) (x : V v) (y : LocalTensorTail (K := ℂ) F E v e)
    (a : AdelicGL F n) :
    evaluate F n (automorphicToContinuous F n
        (localMap F n ρ E e he hne T v (ρ v g x ⊗ₜ[ℂ] y))) a =
      evaluate F n (automorphicToContinuous F n
        (localMap F n ρ E e he hne T v (x ⊗ₜ[ℂ] y)))
        (a * AdelicGL.ofFinite F n (localInclusion F n v g)) := by
  have h := Representation.IntertwiningMap.isIntertwining _ _
    (localMap F n ρ E e he hne T v) g (x ⊗ₜ[ℂ] y)
  change localMap F n ρ E e he hne T v (ρ v g x ⊗ₜ[ℂ] y) = _ at h
  rw [h, evaluate_automorphicLocalRightAction]

/-- Each chosen complementary vector gives an actual local form-valued intertwiner.
This choice does not identify the whole restricted representation with one factor. -/
def localSlice (T : Map F n ρ E e he) (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    (ρ v).IntertwiningMap (automorphicLocalRightAction F n v) :=
  (localMap F n ρ E e he hne T v).comp
    { toLinearMap := (TensorProduct.mk ℂ (V v) (LocalTensorTail (K := ℂ) F E v e)).flip y
      isIntertwining' _ := by ext; rfl }

@[simp]
theorem localSlice_apply (T : Map F n ρ E e he) (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) (x : V v) :
    localSlice F n ρ E e he hne T v y x =
      localMap F n ρ E e he hne T v (x ⊗ₜ[ℂ] y) := rfl

/-- A nonzero complementary vector gives a faithful local slice of a faithful realization. -/
theorem localSlice_injective (T : Map F n ρ E e he)
    (hT : IsInjective F n ρ E e he T) (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) (hy : y ≠ 0) :
    Function.Injective (localSlice F n ρ E e he hne T v y) := by
  intro x x' h
  have hz : x ⊗ₜ[ℂ] y = x' ⊗ₜ[ℂ] y :=
    ((localMap_injective_iff F n ρ E e he hne T v).mpr hT) h
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℂ hy
  have hc := congrArg (fun z => TensorProduct.rid ℂ (V v)
    (TensorProduct.map (LinearMap.id : V v →ₗ[ℂ] V v) φ z)) hz
  simpa only [TensorProduct.map_tmul, LinearMap.id_apply,
    TensorProduct.rid_tmul, hφ, one_smul] using hc

include hne in
/-- With a nonzero complementary vector, faithful occurrence forces the local factor smooth. -/
theorem localFactor_isSmooth (T : Map F n ρ E e he)
    (hT : IsInjective F n ρ E e he T) (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) (hy : y ≠ 0) :
    Langlands.IsSmooth (ρ v) :=
  Langlands.isSmooth_of_injective (localSlice F n ρ E e he hne T v y)
    (localSlice_injective F n ρ E e he hne T hT v y hy)
    (automorphicLocalRightAction_isSmooth F n v)

end Langlands.Automorphic.FiniteTensorRealization

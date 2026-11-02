import Langlands.AlgebraicGeometry.GroupoidCoactionUnit
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-! # Flatness over the invariant ring -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}

section ReflectInjective

variable (hE : RingEtaleEquivalenceRelation t)
variable (hzero : ∀ (K : Type v) [AddCommGroup K] [Module B K]
  (θK : GroupoidCoaction t K), Subsingleton θK.invariantSubmodule → Subsingleton K)
variable {M N : Type v} [AddCommGroup M] [Module B M]
  [AddCommGroup N] [Module B N]

include hE hzero in
/-- Invariants detect injectivity if they detect zero coactions. -/
lemma injective_of_invariantsMap_injective
    (θM : GroupoidCoaction t M) (θN : GroupoidCoaction t N)
    (f : M →ₗ[B] N) (hf : θM.IsHom θN f)
    (hinv : Function.Injective (θM.invariantsMap θN f hf)) :
    Function.Injective f := by
  let θK := kernel hE θM θN f hf
  have hsub : θK.IsHom θM (LinearMap.ker f).subtype :=
    kernel_subtype_isHom hE θM θN f hf
  have hKinv : Subsingleton θK.invariantSubmodule := by
    apply subsingleton_of_forall_eq 0
    intro k
    have hzeroImage : θM.invariantsMap θN f hf
        (θK.invariantsMap θM (LinearMap.ker f).subtype hsub k) = 0 := by
      apply Subtype.ext
      exact (k : LinearMap.ker f).property
    have hk := hinv (hzeroImage.trans (map_zero _).symm)
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : θM.invariantSubmodule => (x : M)) hk
  let : Subsingleton (LinearMap.ker f) := hzero _ θK hKinv
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro m hm
  exact congrArg Subtype.val (Subsingleton.elim (⟨m, hm⟩ : LinearMap.ker f) 0)

end ReflectInjective

section Flat

variable (hE : RingEtaleEquivalenceRelation t)
variable (hacyclic : ∀ (K : Type u) [AddCommGroup K] [Module B K]
  (θK : GroupoidCoaction t K), θK.IsAcyclic)
variable (hzero : ∀ (K : Type u) [AddCommGroup K] [Module B K]
  (θK : GroupoidCoaction t K), Subsingleton θK.invariantSubmodule → Subsingleton K)
variable {M N : Type u} [AddCommGroup M] [Module (invariantRing t) M]
  [AddCommGroup N] [Module (invariantRing t) N]

include hE hacyclic hzero in
/-- Scalar extension to the relation's object ring preserves injective maps. -/
lemma baseChange_injective_of_acyclic
    (f : M →ₗ[invariantRing t] N) (hinj : Function.Injective f) :
    Function.Injective (f.baseChange B) := by
  apply injective_of_invariantsMap_injective hE hzero
    (induced t M) (induced t N) (f.baseChange B) (induced_isHom_baseChange t f)
  intro x y hxy
  obtain ⟨m, rfl⟩ := inducedUnit_surjective_of_acyclic hE hacyclic M x
  obtain ⟨n, rfl⟩ := inducedUnit_surjective_of_acyclic hE hacyclic M y
  apply congrArg (inducedUnit t M)
  apply hinj
  apply inducedUnit_injective_of_acyclic hE hacyclic N
  exact (LinearMap.congr_fun (inducedUnit_natural t f) m).symm.trans
    (hxy.trans (LinearMap.congr_fun (inducedUnit_natural t f) n))

/-- An injective map's scalar extension identifies its domain with its range. -/
noncomputable def baseChangeEquivRangeOfAcyclic
    (f : M →ₗ[invariantRing t] N) (hinj : Function.Injective f) :
    (B ⊗[invariantRing t] M) ≃ₗ[B] LinearMap.range (f.baseChange B) :=
  LinearEquiv.ofInjective (f.baseChange B)
    (baseChange_injective_of_acyclic hE hacyclic hzero f hinj)

@[simp]
lemma baseChangeEquivRangeOfAcyclic_apply
    (f : M →ₗ[invariantRing t] N) (hinj : Function.Injective f)
    (x : B ⊗[invariantRing t] M) :
    (baseChangeEquivRangeOfAcyclic hE hacyclic hzero f hinj x :
      B ⊗[invariantRing t] N) = f.baseChange B x :=
  rfl

include hE hacyclic hzero in
/-- The object ring is flat over the equalizer ring. -/
lemma flat_invariantRing_of_acyclic : Module.Flat (invariantRing t) B := by
  apply Module.Flat.iff_lTensor_preserves_injective_linearMap.mpr
  intro M N _ _ _ _ f hf
  simpa only [← LinearMap.baseChange_eq_ltensor] using
    baseChange_injective_of_acyclic hE hacyclic hzero f hf

include hE hacyclic hzero in
/-- The invariant unit also makes scalar extension reflect zero modules. -/
lemma faithfullyFlat_invariantRing_of_acyclic :
    Module.FaithfullyFlat (invariantRing t) B := by
  apply (Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality
    (invariantRing t) B).mpr
  refine ⟨flat_invariantRing_of_acyclic hE hacyclic hzero, ?_⟩
  intro N _ _ hN
  let := hN
  exact (inducedUnit_injective_of_acyclic hE hacyclic N).subsingleton

include hE hacyclic hzero in
/-- The inclusion of the invariant ring is faithfully flat as a ring homomorphism. -/
lemma faithfullyFlat_invariantRing_algebraMap_of_acyclic :
    (algebraMap (invariantRing t) B).FaithfullyFlat :=
  RingHom.faithfullyFlat_algebraMap_iff.mpr
    (faithfullyFlat_invariantRing_of_acyclic hE hacyclic hzero)

end Flat

end Langlands.AlgebraicGeometry.GroupoidCoaction

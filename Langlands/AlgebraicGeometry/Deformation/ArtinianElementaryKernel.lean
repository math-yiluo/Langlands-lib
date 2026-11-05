import Langlands.AlgebraicGeometry.Deformation.ArtinianTests
import Mathlib.Algebra.Module.RingHom
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.LinearAlgebra.Dimension.Finite

/-! # The actual elementary Artinian kernel as a finite residue-field module -/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.AlgebraicGeometry.Deformation.ArtinianTest

namespace ElementaryKernel

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {A B : ArtinianTest k K} (q : A ⟶ B)

/-- The actual ideal kernel, with its existing additive group and source-ring action. -/
abbrev Kernel := RingHom.ker (toAlgHom q).toRingHom

/-- The maximal ideal acts by zero on the actual kernel of an elementary arrow. -/
lemma maximalIdeal_smul_eq_zero (hq : IsElementarySurjection q)
    (a : A.algebra) (ha : a ∈ IsLocalRing.maximalIdeal A.algebra) (x : Kernel q) :
    a • x = 0 := by
  apply Subtype.ext
  change a * x.val = 0
  exact Ideal.mem_bot.mp (hq.2 ▸ Ideal.mul_mem_mul ha x.property)

/-- The augmentation kernel annihilates the actual elementary kernel module. -/
lemma augmentation_ker_le_annihilator (hq : IsElementarySurjection q) :
    RingHom.ker A.augmentation.toRingHom ≤ Module.annihilator A.algebra (Kernel q) := by
  intro a ha
  exact Module.mem_annihilator.mpr fun x ↦
    maximalIdeal_smul_eq_zero q hq a (ker_augmentation A ▸ ha) x

/-- Descend the actual source-ring action along the surjective augmentation. -/
def residueAction (hq : IsElementarySurjection q) : K →+* AddMonoid.End (Kernel q) :=
  A.augmentation.toRingHom.liftOfSurjective A.augmentation_surjective
    ⟨Module.toAddMonoidEnd A.algebra (Kernel q), augmentation_ker_le_annihilator q hq⟩

lemma residueAction_augmentation (hq : IsElementarySurjection q) (a : A.algebra) :
    residueAction q hq (A.augmentation a) = Module.toAddMonoidEnd A.algebra (Kernel q) a :=
  RingHom.liftOfSurjective_comp_apply _ _ _ a

/-- This action is the unique action factoring the actual source-ring action. -/
lemma residueAction_unique (hq : IsElementarySurjection q)
    (ρ : K →+* AddMonoid.End (Kernel q))
    (hρ : ρ.comp A.augmentation.toRingHom = Module.toAddMonoidEnd A.algebra (Kernel q)) :
    ρ = residueAction q hq :=
  RingHom.eq_liftOfSurjective _ _ _ _ ρ hρ

/-- The residue-field module on the unchanged actual elementary kernel. -/
@[instance_reducible]
def residueModule (hq : IsElementarySurjection q) : Module K (Kernel q) :=
  Module.compHom (Kernel q) (residueAction q hq)

/-- Restriction through the augmentation recovers the actual source-ring scalar action. -/
@[simp]
lemma augmentation_smul (hq : IsElementarySurjection q) (a : A.algebra) (x : Kernel q) :
    letI := residueModule q hq
    A.augmentation a • x = a • x := by
  change residueAction q hq (A.augmentation a) x = a • x
  rw [residueAction_augmentation]
  rfl

/-- The identity of the actual additive kernel is semilinear for the augmentation. -/
def identitySemilinear (hq : IsElementarySurjection q) :
    letI := residueModule q hq
    Kernel q →ₛₗ[A.augmentation.toRingHom] Kernel q := by
  letI := residueModule q hq
  exact
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a x ↦ (augmentation_smul q hq a x).symm }

/-- The descended residue-field module is finite dimensional, including zero kernels. -/
lemma finiteDimensional (hq : IsElementarySurjection q) :
    letI := residueModule q hq
    FiniteDimensional K (Kernel q) := by
  let := residueModule q hq
  have : Module.Finite A.algebra (Kernel q) := inferInstance
  exact Module.Finite.of_surjective (identitySemilinear q hq) Function.surjective_id

end ElementaryKernel

end Langlands.AlgebraicGeometry.Deformation.ArtinianTest

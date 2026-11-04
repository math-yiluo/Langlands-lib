import Langlands.GroupScheme.Lie.ElementCentralizerTangent
import Langlands.GroupScheme.Lie.UnipotentTangent
import Langlands.GroupScheme.Lie.SemisimpleNilpotentMatrix
import Langlands.GroupScheme.Lie.SmoothDifferential
import Langlands.GroupScheme.IdentityComponent

/-! # Nonunipotence detected by an ambient semisimple tangent image -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- A semisimple tangent image of a unipotent group vanishes in an affine
locally finite type ambient group. Semisimplicity is tested in the ambient
group, so no reflection of semisimplicity along the homomorphism is needed. -/
theorem targetMap_eq_one_of_isUnipotent (f : H ⟶ G) (hH : IsUnipotent H)
    (Y : lieKernel H k) (hY : IsSemisimpleElement G (targetMap f k Y)) :
    targetMap f k Y = 1 := by
  obtain ⟨n, ρ, hρ⟩ :=
    affineLinearEmbeddingStatement k G inferInstance inferInstance
  have hn : IsNilpotent (ρ.tangentMatrix k (targetMap f k Y)) := by
    rw [← MatrixRepresentation.tangentMatrix_restrict]
    exact (ρ.restrict f).isNilpotent_tangentMatrix_of_isUnipotent hH k Y
  have hz : ρ.tangentMatrix k (targetMap f k Y) = 0 :=
    (hY n ρ).eq_zero_of_isNilpotent hn
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have hm : Mono ρ.hom.hom := Over.mono_of_mono_left _
  apply lieKernelTarget_injective ρ k hm
  rw [← ρ.pointKernelEquiv_tangentMatrix k (targetMap f k Y),
    ← ρ.pointKernelEquiv_tangentMatrix k 1, hz, ρ.tangentMatrix_one]

/-- A subgroup with a nonzero ambient semisimple tangent image is not
unipotent. No faithfulness assumption on the subgroup homomorphism is needed. -/
theorem not_isUnipotent_of_semisimple_tangent_image (f : H ⟶ G)
    (Y : lieKernel H k) (hY : IsSemisimpleElement G (targetMap f k Y))
    (hne : targetMap f k Y ≠ 1) : ¬ IsUnipotent H := by
  intro hH
  exact hne (targetMap_eq_one_of_isUnipotent f hH Y hY)

variable {C : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth C.X.hom] [IsAffineHom C.X.hom]

/-- The original tangent element lifted to the identity component of a smooth
representative of its actual centralizer. -/
def identityComponentElementCentralizerTangentFactor
    (X : lieKernel G k) (j : C ⟶ G)
    (hrep : (elementCentralizer G X).IsRepresentedBy j) :
    lieKernel (identityComponent C) k :=
  smoothKernelLift (identityComponentι C) k inferInstance
    (elementCentralizerTangentFactor X j hrep)

@[simp]
theorem targetMap_identityComponentElementCentralizerTangentFactor
    (X : lieKernel G k) (j : C ⟶ G)
    (hrep : (elementCentralizer G X).IsRepresentedBy j) :
    targetMap (identityComponentι C ≫ j) k
      (identityComponentElementCentralizerTangentFactor X j hrep) = X := by
  have he (Y : lieKernel (identityComponent C) k) :
      targetMap (identityComponentι C ≫ j) k Y =
        targetMap j k (targetMap (identityComponentι C) k Y) := rfl
  rw [he, identityComponentElementCentralizerTangentFactor,
    targetMap_smoothKernelLift, targetMap_elementCentralizerTangentFactor]

/-- The identity component of a smooth representative of the centralizer
of a nonzero ambient semisimple Lie element is not unipotent. -/
theorem not_isUnipotent_identityComponent_elementCentralizer
    (X : lieKernel G k) (hX : IsSemisimpleElement G X) (hne : X ≠ 1)
    (j : C ⟶ G) (hrep : (elementCentralizer G X).IsRepresentedBy j) :
    ¬ IsUnipotent (identityComponent C) := by
  apply not_isUnipotent_of_semisimple_tangent_image
    (identityComponentι C ≫ j)
    (identityComponentElementCentralizerTangentFactor X j hrep)
  · simpa only [targetMap_identityComponentElementCentralizerTangentFactor] using hX
  · simpa only [targetMap_identityComponentElementCentralizerTangentFactor] using hne

end Langlands.GroupScheme.Lie

import Langlands.GroupScheme.Rational.RootKernelTorus
import Langlands.GroupScheme.IdentityComponent

/-! # The split torus in the identity component of a root-kernel centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G C : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth C.X.hom] [IsAffineHom C.X.hom]

namespace RelativeRoot

variable (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (a : characterLattice T) (j : C ⟶ G)
    (hj : (kernelCentralizer i a).IsRepresentedBy j)

/-- The split torus lies in the actual identity component of a smooth affine
representative of its full character-kernel centralizer. -/
def kernelCentralizerIdentityTorus : T.toGrp ⟶ identityComponent C := by
  letI := hT.connectedSpace
  exact IdentityComponent.factor C (kernelCentralizerTorus i a j hj)

@[simp] theorem kernelCentralizerIdentityTorus_comp :
    kernelCentralizerIdentityTorus i hT a j hj ≫ identityComponentι C =
      kernelCentralizerTorus i a j hj := by
  have := hT.connectedSpace
  exact IdentityComponent.factor_identityComponentι C _

/-- The composite of the identity-component inclusion with the represented
centralizer inclusion is the actual ambient embedding. -/
theorem kernelCentralizerIdentityTorus_comp_ambient :
    kernelCentralizerIdentityTorus i hT a j hj ≫ (identityComponentι C ≫ j) = i := by
  rw [← Category.assoc, kernelCentralizerIdentityTorus_comp, kernelCentralizerTorus_comp]

/-- The identity component is a closed subgroup of the ambient group whenever
the represented full kernel centralizer is closed. -/
theorem kernelCentralizerIdentityι_isClosedSubgroup (hjc : IsClosedSubgroup j) :
    IsClosedSubgroup (identityComponentι C ≫ j) :=
  (IdentityComponent.isClosedSubgroup_identityComponentι C).comp hjc

/-- Actual normalizers inside the identity component map to ambient normalizers
of the original torus. -/
def kernelCentralizerIdentityNormalizerMap :
    normalizerPoints (kernelCentralizerIdentityTorus i hT a j hj) →*
      normalizerPoints i :=
  normalizerPointsMap _ (identityComponentι C ≫ j) i
    (kernelCentralizerIdentityTorus_comp_ambient i hT a j hj)

@[simp] theorem kernelCentralizerIdentityNormalizerMap_val
    (n : normalizerPoints (kernelCentralizerIdentityTorus i hT a j hj)) :
    (kernelCentralizerIdentityNormalizerMap i hT a j hj n).val =
      n.val ≫ (identityComponentι C).hom.hom ≫ j.hom.hom := by
  rw [kernelCentralizerIdentityNormalizerMap, normalizerPointsMap_val, Grp.comp_hom_hom]

/-- The transported point still centralizes the entire scheme-theoretic kernel
on every test scheme and every refinement. -/
theorem kernelCentralizerIdentityNormalizerMap_mem
    (n : normalizerPoints (kernelCentralizerIdentityTorus i hT a j hj)) :
    (kernelCentralizerIdentityNormalizerMap i hT a j hj n).val ∈
      (kernelCentralizer i a).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  rw [kernelCentralizerIdentityNormalizerMap_val, ← hj.2]
  refine ⟨n.val ≫ (identityComponentι C).hom.hom, ?_⟩
  change (n.val ≫ (identityComponentι C).hom.hom) ≫ j.hom.hom =
    n.val ≫ (identityComponentι C).hom.hom ≫ j.hom.hom
  exact Category.assoc _ _ _

/-- The whole-character action is unchanged on passing from the identity
component to the ambient group. -/
theorem weylAction_kernelCentralizerIdentityNormalizerMap
    [Mono i.hom.hom.left]
    [Mono (kernelCentralizerIdentityTorus i hT a j hj).hom.hom.left]
    (n : normalizerPoints (kernelCentralizerIdentityTorus i hT a j hj)) :
    weylAction i (kernelCentralizerIdentityNormalizerMap i hT a j hj n) =
      weylAction (kernelCentralizerIdentityTorus i hT a j hj) n :=
  weylAction_normalizerPointsMap _ (identityComponentι C ≫ j) i
    (kernelCentralizerIdentityTorus_comp_ambient i hT a j hj) n

end RelativeRoot

variable {i : T.toGrp ⟶ G}

/-- An ambient maximal split torus remains maximal split inside the actual
identity component of a smooth affine closed kernel-centralizer representative. -/
theorem IsMaximalSplitTorus.kernelCentralizerIdentityTorus
    (hi : IsMaximalSplitTorus i) (a : characterLattice T) (j : C ⟶ G)
    (hj : (RelativeRoot.kernelCentralizer i a).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) :
    IsMaximalSplitTorus
      (RelativeRoot.kernelCentralizerIdentityTorus i hi.1.1 a j hj) := by
  apply IsMaximalSplitTorus.of_comp
    (IdentityComponent.isClosedSubgroup_identityComponentι C)
  rw [RelativeRoot.kernelCentralizerIdentityTorus_comp]
  exact IsMaximalSplitTorus.kernelCentralizerTorus hi a j hj hjc

end Langlands.GroupScheme

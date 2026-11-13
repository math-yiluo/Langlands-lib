import Langlands.AbelianScheme.Kernel
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # The scheme-theoretic kernel of an isomorphism -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H : Grp (Over S)}

/-- The actual kernel of an isomorphism has an isomorphic structure map. -/
instance kernel_hom_isIso (f : G ⟶ H) [IsIso f] : IsIso (kernel f).X.hom := by
  have : IsIso f.hom.hom := (Grp.forget (Over S)).map_isIso f
  have : IsIso f.hom.hom.left := (Over.forget S).map_isIso f.hom.hom
  exact (kernel_isPullback_scheme f).isIso_snd_of_isIso

/-- The actual scheme kernel of an isomorphism is isomorphic to the base,
via its structure morphism. -/
def kernelBaseIso (f : G ⟶ H) [IsIso f] : (kernel f).X.left ≅ S :=
  asIso (kernel f).X.hom

@[simp] theorem kernelBaseIso_hom (f : G ⟶ H) [IsIso f] :
    (kernelBaseIso f).hom = (kernel f).X.hom := rfl

/-- Smoothness and affineness of the trivial kernel over any base. -/
theorem smooth_isAffineHom_kernel_of_isIso (f : G ⟶ H) [IsIso f] :
    Smooth (kernel f).X.hom ∧ IsAffineHom (kernel f).X.hom :=
  ⟨inferInstance, inferInstance⟩

/-- Connectedness of the trivial kernel over a connected base. -/
theorem connectedSpace_kernel_of_isIso [ConnectedSpace S] (f : G ⟶ H) [IsIso f] :
    ConnectedSpace (kernel f).X.left :=
  (Scheme.homeoOfIso (kernelBaseIso f)).connectedSpace_iff.2 inferInstance

end Langlands.GroupScheme

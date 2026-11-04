import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Absolute.SolvableFieldExtensionProof

/-! # The non-maximality Borel fields after a field extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme
namespace BorelFieldExtension

variable {k K : Type u} [Field k] [Field K]
  (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
variable {G B : GroupScheme (Spec (CommRingCat.of k))} {i : B ⟶ G}

/-- A closed subgroup of an affine group scheme is affine over the base field. -/
theorem isAffineHom_source [IsAffineHom G.X.hom] (hi : IsClosedSubgroup i) :
    IsAffineHom B.X.hom := by
  have : IsClosedImmersion i.hom.hom.left := hi
  rw [← Over.w i.hom.hom]
  infer_instance

/-- The base change of a Borel inclusion is a closed subgroup inclusion. -/
theorem isClosedSubgroup_baseChange (hi : IsBorelSubgroup i) :
    IsClosedSubgroup ((GroupScheme.baseChange b).map i) :=
  hi.isClosedSubgroup.baseChange b

/-- The base change of a Borel subgroup is smooth. -/
theorem smooth_baseChange (hi : IsBorelSubgroup i) :
    Smooth ((GroupScheme.baseChange b).obj B).X.hom := by
  have : Smooth B.X.hom := hi.smooth
  change Smooth (pullback.snd B.X.hom b)
  infer_instance

/-- The base change of a Borel subgroup of an affine group scheme is connected. -/
theorem connectedSpace_baseChange [IsAffineHom G.X.hom] (hi : IsBorelSubgroup i) :
    ConnectedSpace ((GroupScheme.baseChange b).obj B).X.left := by
  have : IsAffineHom B.X.hom := isAffineHom_source hi.isClosedSubgroup
  have : Smooth B.X.hom := hi.smooth
  have : ConnectedSpace B.X.left := hi.connectedSpace
  exact B.connectedSpace_baseChange_of_smooth_affine b

/-- The base change of a Borel subgroup of an affine group scheme is solvable. -/
theorem isSolvableGroupScheme_baseChange [IsAffineHom G.X.hom] (hi : IsBorelSubgroup i) :
    IsSolvableGroupScheme ((GroupScheme.baseChange b).obj B) := by
  have : IsAffineHom B.X.hom := isAffineHom_source hi.isClosedSubgroup
  exact solvableFieldExtensionStatement k K b B hi.smooth hi.isSolvableGroupScheme

/-- The base change of a Borel inclusion of an affine group scheme is a Borel inclusion as soon
as it satisfies the maximality field of `IsBorelSubgroup` over the new base field. -/
theorem isBorelSubgroup_baseChange_of_maximal [IsAffineHom G.X.hom] (hi : IsBorelSubgroup i)
    (hmax : ∀ (B' : GroupScheme (Spec (CommRingCat.of K)))
      (i' : B' ⟶ (GroupScheme.baseChange b).obj G)
      (f : (GroupScheme.baseChange b).obj B ⟶ B'),
      IsClosedSubgroup i' → Smooth B'.X.hom → ConnectedSpace B'.X.left →
        IsSolvableGroupScheme B' → f ≫ i' = (GroupScheme.baseChange b).map i → IsIso f) :
    IsBorelSubgroup ((GroupScheme.baseChange b).map i) where
  isClosedSubgroup := isClosedSubgroup_baseChange b hi
  smooth := smooth_baseChange b hi
  connectedSpace := connectedSpace_baseChange b hi
  isSolvableGroupScheme := isSolvableGroupScheme_baseChange b hi
  maximal := hmax

end BorelFieldExtension
end Langlands.GroupScheme

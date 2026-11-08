import Langlands.GroupScheme.Reductive.GeometricRootReflectionIntrinsic
import Langlands.GroupScheme.Dynamic.CentralizerRestriction
import Langlands.GroupScheme.Rational.RepresentedLieUniqueness

/-! # Tangent containment for cocharacter centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace Dynamic

variable {k : Type u} [Field k]
    {G P : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    [Smooth P.X.hom] [ConnectedSpace P.X.left]

/-- A smooth connected closed subgroup containing a cocharacter contains its
ambient centralizer if it contains the latter's actual tangent submodule.
The intersection is smooth because it is the internal cocharacter centralizer. -/
theorem centralizer_le_range_of_tangentSubmodule_le
    (i : P ⟶ G) (hi : IsClosedSubgroup i)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ P)
    (hLie : RelativeRoot.tangentSubmodule (centralizer (χ ≫ i)) ≤
      RelativeRoot.tangentSubmodule (SubgroupFunctor.range i)) :
    centralizer (χ ≫ i) ≤ SubgroupFunctor.range i := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom P.X.hom := hi.isAffineHom_source
  let M := Affine.centralizerScheme (χ ≫ i)
  let m : M ⟶ G := Affine.centralizerHom (χ ≫ i)
  have hm : (centralizer (χ ≫ i)).IsRepresentedBy m :=
    Affine.isRepresentedBy_centralizerHom _
  have hmc : IsClosedSubgroup m := Affine.isClosedSubgroup_centralizerHom _
  have hQ := isRepresentedBy_intersectionSnd i hi χ m hmc hm
  let Q := subgroupIntersection m i
  let q : Q ⟶ G := subgroupIntersectionHom m i
  have hqc : IsClosedSubgroup q := isClosedSubgroup_subgroupIntersectionHom hmc hi
  have hq : (centralizer (χ ≫ i) ⊓ SubgroupFunctor.range i).IsRepresentedBy q := by
    rw [← hm.2]
    exact isRepresentedBy_subgroupIntersectionHom hmc hi
  have hMs : Smooth M.X.hom := (dynamicSmooth k G (χ ≫ i) M m).2.1 hm
  have hMc : ConnectedSpace M.X.left :=
    DynamicConnected.connectedSpace_of_isRepresentedBy_centralizer G (χ ≫ i) hm
  have hQs : Smooth Q.X.hom := (dynamicSmooth k P χ Q
    (subgroupIntersectionSnd m i)).2.1 hQ
  have hQc : ConnectedSpace Q.X.left :=
    DynamicConnected.connectedSpace_of_isRepresentedBy_centralizer P χ hQ
  have hLieEq : RelativeRoot.tangentSubmodule
      (centralizer (χ ≫ i) ⊓ SubgroupFunctor.range i) =
        RelativeRoot.tangentSubmodule (centralizer (χ ≫ i)) := by
    rw [RelativeRoot.tangentSubmodule_inf, inf_eq_left.mpr hLie]
  have heq := RelativeRoot.IsSmoothConnectedClosed.eq_of_le_of_hasLieImage
    (F := centralizer (χ ≫ i) ⊓ SubgroupFunctor.range i)
    (F' := centralizer (χ ≫ i))
    ⟨Q, q, hq, hqc, hQs, hQc⟩ ⟨M, m, hm, hmc, hMs, hMc⟩ (fun _ => inf_le_left)
    ((RelativeRoot.hasLieImage_iff_tangentSubmodule_eq _ _).mpr hLieEq)
    (RelativeRoot.hasLieImage_tangentSubmodule _)
  rw [← heq]
  exact fun _ => inf_le_right

end Dynamic

end Langlands.GroupScheme

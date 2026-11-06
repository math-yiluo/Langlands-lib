import Langlands.GroupScheme.Torus.RelativeCentralizerSmooth
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.CentralizerRestriction
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.IdentityComponent.Transport
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Relative cocharacter centralizers and actual identity components -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace Dynamic

section Ring

variable {R : CommRingCat.{u}} {G C : GroupScheme (Spec R)}
  [IsAffine G.X.left] (χ : (Gm (Spec R)).toGrp ⟶ G)

/-- Every actual cocharacter-centralizer representative is smooth over an
arbitrary ring when its ambient affine group is smooth. -/
theorem smooth_centralizer_overRing (hG : Smooth G.X.hom) (j : C ⟶ G)
    (hj : (centralizer χ).IsRepresentedBy j) : Smooth C.X.hom := by
  obtain ⟨D, d, -, hd, hrep⟩ :=
    splitTorusCentralizer_hasSmoothClosedRepresentative_overRing χ isSplitTorus_gm hG
  rw [torusCentralizer_gm_eq_dynamicCentralizer] at hrep
  exact smooth_of_over_iso
    ((Grp.forget _).mapIso (hj.isoOfIsRepresentedBy hrep)) hd

/-- The already constructed actual dynamic centralizer is smooth over any
commutative base ring. -/
theorem smooth_affineCentralizer_overRing (hG : Smooth G.X.hom) :
    Smooth (Affine.centralizerScheme χ).X.hom :=
  smooth_centralizer_overRing χ hG (Affine.centralizerHom χ)
    (Affine.isRepresentedBy_centralizerHom χ)

variable {R' : CommRingCat.{u}} (b : Spec R' ⟶ Spec R)
  [IsAffine ((GroupScheme.baseChange b).obj G).X.left]

/-- The actual affine cocharacter-centralizer construction commutes with
arbitrary affine base change, with no smoothness assumption. -/
def affineCentralizerBaseChangeIso :
    (GroupScheme.baseChange b).obj (Affine.centralizerScheme χ) ≅
      Affine.centralizerScheme (baseChangeCocharacter b χ) :=
  (isRepresentedBy_centralizer_baseChange b χ
    (Affine.isRepresentedBy_centralizerHom χ)).isoOfIsRepresentedBy
      (Affine.isRepresentedBy_centralizerHom (baseChangeCocharacter b χ))

@[reassoc (attr := simp)]
theorem affineCentralizerBaseChangeIso_hom_comp :
    (affineCentralizerBaseChangeIso χ b).hom ≫
      Affine.centralizerHom (baseChangeCocharacter b χ) =
        (GroupScheme.baseChange b).map (Affine.centralizerHom χ) :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end Ring

section Field

variable {k : Type u} [Field k]
  {G C : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  [Smooth C.X.hom] [IsAffineHom C.X.hom]
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ identityComponent G)
  (j : C ⟶ G)
  (hj : (centralizer (χ ≫ identityComponentι G)).IsRepresentedBy j)
  (hjc : IsClosedSubgroup j)

/-- The actual intersection of an ambient centralizer and the actual
identity component, as a group scheme. -/
abbrev identityCentralizerIntersection :=
  subgroupIntersection j (identityComponentι G)

include hj hjc

omit [Smooth C.X.hom] [IsAffineHom C.X.hom] in
private theorem intersection_represents :
    (centralizer χ).IsRepresentedBy
      (subgroupIntersectionSnd j (identityComponentι G)) :=
  isRepresentedBy_intersectionSnd (identityComponentι G)
    (IdentityComponent.isClosedSubgroup_identityComponentι G) χ j hjc hj

omit [Smooth C.X.hom] [IsAffineHom C.X.hom] in
private theorem intersection_connected :
    ConnectedSpace (identityCentralizerIntersection j).X.left :=
  DynamicConnected.connectedSpace_of_isRepresentedBy_centralizer
    (identityComponent G) χ (intersection_represents χ j hj hjc)

omit hj hjc [Smooth C.X.hom] [IsAffineHom C.X.hom] in
private theorem intersectionFst_isOpenImmersion :
    IsOpenImmersion (subgroupIntersectionFst j (identityComponentι G)).hom.hom.left :=
  MorphismProperty.of_isPullback
    (subgroupIntersection_isPullback_scheme j (identityComponentι G)).flip
    (inferInstance : IsOpenImmersion (identityComponentι G).hom.hom.left)

/-- The intersection with `G⁰` is precisely `C⁰`, as an isomorphism of
actual group schemes preserving the specified inclusion into `C`. -/
def identityCentralizerIntersectionIso :
    identityCentralizerIntersection j ≅ identityComponent C := by
  let : ConnectedSpace (identityCentralizerIntersection j).X.left :=
    intersection_connected χ j hj hjc
  let : IsOpenImmersion
      (subgroupIntersectionFst j (identityComponentι G)).hom.hom.left :=
    intersectionFst_isOpenImmersion j
  let : IsClosedImmersion
      (subgroupIntersectionFst j (identityComponentι G)).hom.hom.left :=
    isClosedSubgroup_subgroupIntersectionFst j
      (IdentityComponent.isClosedSubgroup_identityComponentι G)
  exact IdentityComponent.isoOfIsOpenImmersion C
    (subgroupIntersectionFst j (identityComponentι G))

@[reassoc (attr := simp)]
theorem identityCentralizerIntersectionIso_hom_comp :
    (identityCentralizerIntersectionIso χ j hj hjc).hom ≫ identityComponentι C =
      subgroupIntersectionFst j (identityComponentι G) := by
  let : ConnectedSpace (identityCentralizerIntersection j).X.left :=
    intersection_connected χ j hj hjc
  let : IsOpenImmersion
      (subgroupIntersectionFst j (identityComponentι G)).hom.hom.left :=
    intersectionFst_isOpenImmersion j
  let : IsClosedImmersion
      (subgroupIntersectionFst j (identityComponentι G)).hom.hom.left :=
    isClosedSubgroup_subgroupIntersectionFst j
      (IdentityComponent.isClosedSubgroup_identityComponentι G)
  exact IdentityComponent.isoOfIsOpenImmersion_hom_identityComponentι _ _

@[reassoc (attr := simp)]
theorem identityCentralizerIntersectionIso_hom_map :
    (identityCentralizerIntersectionIso χ j hj hjc).hom ≫ IdentityComponent.map j =
      subgroupIntersectionSnd j (identityComponentι G) := by
  apply (cancel_mono (identityComponentι G)).mp
  rw [Category.assoc, IdentityComponent.map_identityComponentι,
    identityCentralizerIntersectionIso_hom_comp_assoc,
    subgroupIntersection_condition]

/-- The specified inclusion differential and points of `C⁰ → G⁰` come
from the actual centralizer of the restricted cocharacter on every test. -/
theorem identityComponent_map_represents_centralizer :
    (centralizer χ).IsRepresentedBy (IdentityComponent.map j) := by
  let e := identityCentralizerIntersectionIso χ j hj hjc
  have he : e.hom ≫ IdentityComponent.map j =
      subgroupIntersectionSnd j (identityComponentι G) :=
    identityCentralizerIntersectionIso_hom_map χ j hj hjc
  have hclosed : IsClosedSubgroup (IdentityComponent.map j) := by
    apply IsClosedSubgroup.of_comp
      (IdentityComponent.isClosedSubgroup_identityComponentι G)
    rw [IdentityComponent.map_identityComponentι]
    let : IsClosedImmersion j.hom.hom.left := hjc
    change IsClosedImmersion
      ((identityComponentι C).hom.hom.left ≫ j.hom.hom.left)
    infer_instance
  let : IsClosedImmersion (IdentityComponent.map j).hom.hom.left := hclosed
  refine ⟨Over.mono_of_mono_left _, ?_⟩
  rw [← SubgroupFunctor.range_precomp_iso e (IdentityComponent.map j), he]
  exact (intersection_represents χ j hj hjc).2

variable {D : GroupScheme (Spec (CommRingCat.of k))}
  (d : D ⟶ identityComponent G) (hd : (centralizer χ).IsRepresentedBy d)

/-- The identity component of an actual ambient centralizer is canonically
the actual centralizer inside the ambient identity component. -/
def identityComponentCentralizerIso : identityComponent C ≅ D :=
  (identityComponent_map_represents_centralizer χ j hj hjc).isoOfIsRepresentedBy hd

@[reassoc (attr := simp)]
theorem identityComponentCentralizerIso_hom_comp :
    (identityComponentCentralizerIso χ j hj hjc d hd).hom ≫ d =
      IdentityComponent.map j :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

@[reassoc (attr := simp)]
theorem identityComponentCentralizerIso_hom_ambient :
    (identityComponentCentralizerIso χ j hj hjc d hd).hom ≫ d ≫ identityComponentι G =
      identityComponentι C ≫ j := by
  rw [identityComponentCentralizerIso_hom_comp_assoc,
    IdentityComponent.map_identityComponentι]

end Field

end Dynamic

end Langlands.GroupScheme

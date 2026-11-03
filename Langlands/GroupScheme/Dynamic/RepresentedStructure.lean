import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Structural transport for represented dynamic subgroups -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A closed subgroup of a locally finite-type group scheme is locally of finite type. -/
theorem IsClosedSubgroup.locallyOfFiniteType {S : Scheme.{u}} {H G : GroupScheme S}
    {j : H ⟶ G} (hj : IsClosedSubgroup j) [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType H.X.hom := by
  let : IsClosedImmersion j.hom.hom.left := hj
  rw [← Over.w j.hom.hom]
  infer_instance

namespace SubgroupFunctor.IsRepresentedBy

/-- Closedness of the inclusion depends only on the represented subgroup functor. -/
theorem isClosedSubgroup {S : Scheme.{u}} {G H H' : GroupScheme S}
    {F : SubgroupFunctor G} {i : H ⟶ G} {j : H' ⟶ G}
    (hi : F.IsRepresentedBy i) (hj : F.IsRepresentedBy j) (hclosed : IsClosedSubgroup j) :
    IsClosedSubgroup i := by
  rw [← hi.isoOfIsRepresentedBy_hom_comp hj]
  exact hclosed.iso_comp (hi.isoOfIsRepresentedBy hj)

end SubgroupFunctor.IsRepresentedBy

namespace Dynamic.Affine

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffine G.X.left]
    (χ : (Gm (Spec R)).toGrp ⟶ G) {H : GroupScheme (Spec R)} {j : H ⟶ G}

/-- Any representative of the dynamic parabolic is isomorphic to the affine representative. -/
def parabolicIso (hj : (parabolic χ).IsRepresentedBy j) : H ≅ parabolicScheme χ :=
  hj.isoOfIsRepresentedBy (isRepresentedBy_parabolicHom χ)

/-- Any representative of the dynamic centralizer is isomorphic to the affine representative. -/
def centralizerIso (hj : (centralizer χ).IsRepresentedBy j) : H ≅ centralizerScheme χ :=
  hj.isoOfIsRepresentedBy (isRepresentedBy_centralizerHom χ)

/-- Any representative of the dynamic unipotent is isomorphic to the affine representative. -/
def unipotentIso (hj : (unipotent χ).IsRepresentedBy j) : H ≅ unipotentScheme χ :=
  hj.isoOfIsRepresentedBy (isRepresentedBy_unipotentHom χ)

@[simp] theorem parabolicIso_hom_comp (hj : (parabolic χ).IsRepresentedBy j) :
    (parabolicIso χ hj).hom ≫ parabolicHom χ = j :=
  hj.isoOfIsRepresentedBy_hom_comp (isRepresentedBy_parabolicHom χ)

@[simp] theorem centralizerIso_hom_comp (hj : (centralizer χ).IsRepresentedBy j) :
    (centralizerIso χ hj).hom ≫ centralizerHom χ = j :=
  hj.isoOfIsRepresentedBy_hom_comp (isRepresentedBy_centralizerHom χ)

@[simp] theorem unipotentIso_hom_comp (hj : (unipotent χ).IsRepresentedBy j) :
    (unipotentIso χ hj).hom ≫ unipotentHom χ = j :=
  hj.isoOfIsRepresentedBy_hom_comp (isRepresentedBy_unipotentHom χ)

/-- Every inclusion representing the actual dynamic parabolic is a closed subgroup. -/
theorem isClosedSubgroup_of_isRepresentedBy_parabolic
    (hj : (parabolic χ).IsRepresentedBy j) : IsClosedSubgroup j :=
  hj.isClosedSubgroup (isRepresentedBy_parabolicHom χ) (isClosedSubgroup_parabolicHom χ)

/-- Every inclusion representing the actual dynamic centralizer is a closed subgroup. -/
theorem isClosedSubgroup_of_isRepresentedBy_centralizer
    (hj : (centralizer χ).IsRepresentedBy j) : IsClosedSubgroup j :=
  hj.isClosedSubgroup (isRepresentedBy_centralizerHom χ) (isClosedSubgroup_centralizerHom χ)

/-- Every inclusion representing the actual dynamic unipotent is a closed subgroup. -/
theorem isClosedSubgroup_of_isRepresentedBy_unipotent
    (hj : (unipotent χ).IsRepresentedBy j) : IsClosedSubgroup j :=
  hj.isClosedSubgroup (isRepresentedBy_unipotentHom χ) (isClosedSubgroup_unipotentHom χ)

end Dynamic.Affine
end Langlands.GroupScheme

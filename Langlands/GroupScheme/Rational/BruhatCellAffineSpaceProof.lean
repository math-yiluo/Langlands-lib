import Langlands.GroupScheme.Rational.BruhatCellAffineSpaceStatement
import Langlands.GroupScheme.Dynamic.SplitContractingSubgroup
import Langlands.GroupScheme.Dynamic.CommonTorusIntersections
import Langlands.GroupScheme.Rational.SplitSeriesDimension
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.GroupScheme.Rational.StandardLeviRootTransport
import Langlands.GroupScheme.SubgroupFunctor.IntersectionNormalizer
import Langlands.GroupScheme.Unipotent.SplitAffineSpaceProof

/-! # Affine-space coordinates for the unipotent Bruhat factor -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open Langlands.GroupScheme.Dynamic

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
/-- The intersection giving the unipotent Bruhat factor is the contracting
subgroup for a second cocharacter acting on the first one. -/
theorem rationalBruhatCellAffineSpace : RationalBruhatCellAffineSpaceStatement.{u} := by
  intro k _ G hG T i _ ν
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  dsimp only
  intro _ n
  let χ := CommGroupScheme.groupHom ν ≫ i
  let invGm := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1))
  let χminus := invGm ≫ χ
  let e := G.innerIso n.val
  let ξ := invGm ≫ CommGroupScheme.groupHom (cocharacterAut (normalizingAut i n) ν)
  have hξ : ξ ≫ i = χminus ≫ e.hom := by
    simp only [ξ, χminus, χ, e, Category.assoc, groupHom_cocharacterAut_comp]
  let u := Affine.unipotentHom χ
  let v := Affine.unipotentHom χminus
  let w := v ≫ e.hom
  let j := subgroupIntersectionHom w u
  let p := subgroupIntersectionSnd w u
  have hu := Affine.isRepresentedBy_unipotentHom χ
  have huc := Affine.isClosedSubgroup_unipotentHom χ
  have hvc := Affine.isClosedSubgroup_unipotentHom χminus
  have hwc : IsClosedSubgroup w := hvc.comp_iso e
  have hjc : IsClosedSubgroup j := isClosedSubgroup_subgroupIntersectionHom hwc huc
  have hw : SubgroupFunctor.range w = unipotent (ξ ≫ i) := by
    rw [hξ, SubgroupFunctor.range_comp_iso, (Affine.isRepresentedBy_unipotentHom χminus).2,
      unipotent_eq_comap_of_iso (χminus ≫ e.hom) e.symm, Iso.symm_hom,
      comp_hom_comp_inv]
  have hstable : (AutomorphicAction.conjugation (ξ ≫ i)).IsStable (unipotent χ) := by
    have h := (unipotent_isStable_conjugation i (CommGroupScheme.groupHom ν)).restrict ξ
    rwa [AutomorphicAction.restrict_conjugation] at h
  let a := (AutomorphicAction.conjugation (ξ ≫ i)).onRepresentedSubgroup u hu hstable
  have ha : a.IsEquivariant (AutomorphicAction.cocharacterAction (ξ ≫ i)) u := by
    rw [AutomorphicAction.cocharacterAction_eq_conjugation]
    intro X t x
    exact AutomorphicAction.onRepresentedSubgroup_act_comp _ _ _ _ t x
  let : Mono u.hom.hom := hu.1
  let : IsClosedImmersion p.hom.hom.left :=
    MorphismProperty.of_isPullback (subgroupIntersection_isPullback_scheme w u) hwc
  have hpMono : Mono p.hom.hom := Over.mono_of_mono_left _
  have hpRange : SubgroupFunctor.range (p ≫ u) =
      SubgroupFunctor.range u ⊓ unipotent (ξ ≫ i) := by
    rw [show p ≫ u = j from (subgroupIntersection_condition w u).symm]
    rw [show SubgroupFunctor.range j = SubgroupFunctor.range w ⊓ SubgroupFunctor.range u
      from range_subgroupIntersectionHom w u, hw]
    apply SubgroupFunctor.ext
    intro X
    exact inf_comm _ _
  have hp : a.unipotent.IsRepresentedBy p := by
    refine ⟨hpMono, ?_⟩
    rw [SubgroupFunctor.range_eq_comap_of_range_comp_eq_inf p u _ hpRange,
      ha.unipotent_eq_comap_of_isClosedSubgroup huc, AutomorphicAction.cocharacterAction_unipotent]
  let : Smooth (Affine.unipotentScheme χ).X.hom := (dynamicSmooth k G χ _ u).2.2 hu
  let : IsAffineHom (Affine.unipotentScheme χ).X.hom := huc.isAffineHom
  let model := a.splitContractingSubgroup
  let iso := model.isRepresentedBy.isoOfIsRepresentedBy hp
  let : IsAffineHom (subgroupIntersection w u).X.hom := hjc.isAffineHom
  let : ConnectedSpace (subgroupIntersection w u).X.left :=
    connectedSpace_of_over_iso ((Grp.forget _).mapIso iso.symm) model.connectedSpace
  obtain ⟨d, hd⟩ := model.isSplitUnipotent.of_iso iso
  exact ⟨d, hd, hd.smoothOfRelativeDimension, splitUnipotentAffineSpaceStatement k d _ inferInstance hd⟩

end Langlands.GroupScheme

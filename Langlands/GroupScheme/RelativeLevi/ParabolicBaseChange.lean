import Langlands.GroupScheme.RelativeLevi.Basic
import Langlands.GroupScheme.Absolute.ParabolicFieldExtensionProof
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Descent.Data

/-! # Presentation transport and base change of relative parabolic subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}} {P P' G G' : GroupScheme S} {i : P ⟶ G}

/-- A change of the source presentation preserves relative parabolicity. -/
theorem IsRelativeParabolicSubgroup.iso_comp (hi : IsRelativeParabolicSubgroup i)
    (e : P' ≅ P) : IsRelativeParabolicSubgroup (e.hom ≫ i) := by
  let : Smooth P.X.hom := hi.smooth
  let : IsAffineHom P.X.hom := hi.isAffineHom
  let : Mono i.hom.hom := hi.mono
  let : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom)
  refine ⟨?_, ?_, ?_, fun s => ?_⟩
  · rw [← Over.w e.hom.hom.hom]
    infer_instance
  · rw [← Over.w e.hom.hom.hom]
    infer_instance
  · have : IsIso e.hom.hom.hom :=
      (inferInstance : IsIso ((Grp.forget _).mapIso e).hom)
    change Mono (e.hom.hom.hom ≫ i.hom.hom)
    infer_instance
  · let r : Spec (CommRingCat.of (S.residueField s)) ⟶ S := S.fromSpecResidueField s
    change IsParabolicSubgroup ((GroupScheme.baseChange r).map (e.hom ≫ i))
    rw [Functor.map_comp]
    exact (hi.residueFiber s).iso_comp ((GroupScheme.baseChange r).mapIso e)

/-- An isomorphism of the ambient group preserves relative parabolicity. -/
theorem IsRelativeParabolicSubgroup.comp_iso (hi : IsRelativeParabolicSubgroup i)
    (e : G ≅ G') : IsRelativeParabolicSubgroup (i ≫ e.hom) := by
  let : Mono i.hom.hom := hi.mono
  let : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom)
  refine ⟨hi.smooth, hi.isAffineHom, ?_, fun s => ?_⟩
  · have : IsIso e.hom.hom.hom :=
      (inferInstance : IsIso ((Grp.forget _).mapIso e).hom)
    change Mono (i.hom.hom ≫ e.hom.hom.hom)
    infer_instance
  · let r : Spec (CommRingCat.of (S.residueField s)) ⟶ S := S.fromSpecResidueField s
    change IsParabolicSubgroup ((GroupScheme.baseChange r).map (i ≫ e.hom))
    rw [Functor.map_comp]
    exact (hi.residueFiber s).comp_iso ((GroupScheme.baseChange r).mapIso e)

/-- Relative parabolicity depends only on the subgroup functor among monic
presentations, with no closedness premise. -/
theorem IsRelativeParabolicSubgroup.of_range_eq (hi : IsRelativeParabolicSubgroup i)
    {i' : P' ⟶ G} (hi' : Mono i'.hom.hom)
    (h : SubgroupFunctor.range i = SubgroupFunctor.range i') :
    IsRelativeParabolicSubgroup i' := by
  let : Mono i.hom.hom := hi.mono
  let : Mono i'.hom.hom := hi'
  let hr : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  let hr' : (SubgroupFunctor.range i).IsRepresentedBy i' := ⟨inferInstance, h.symm⟩
  let e := hr.isoOfIsRepresentedBy hr'
  have he : e.hom ≫ i' = i := hr.isoOfIsRepresentedBy_hom_comp hr'
  have he' : e.inv ≫ i = i' := by rw [← he, Iso.inv_hom_id_assoc]
  simpa only [Iso.symm_hom, he'] using hi.iso_comp e.symm

/-- Equality of all-test subgroup functors preserves and reflects relative
parabolicity for monic presentations. -/
theorem isRelativeParabolicSubgroup_iff_of_range_eq {i' : P' ⟶ G}
    (hi : Mono i.hom.hom) (hi' : Mono i'.hom.hom)
    (h : SubgroupFunctor.range i = SubgroupFunctor.range i') :
    IsRelativeParabolicSubgroup i ↔ IsRelativeParabolicSubgroup i' :=
  ⟨fun hp => hp.of_range_eq hi' h, fun hp => hp.of_range_eq hi h.symm⟩

/-- Any field-valued point of the base of a relative parabolic in a reductive
group has parabolic pullback. -/
theorem IsRelativeParabolicSubgroup.isParabolicSubgroup_baseChange
    (hi : IsRelativeParabolicSubgroup i) (hG : IsReductive G)
    {k : Type u} [Field k] (f : Spec (CommRingCat.of k) ⟶ S) :
    IsParabolicSubgroup ((GroupScheme.baseChange f).map i) := by
  let s := f (IsLocalRing.closedPoint k)
  let φ : S.residueField s ⟶ CommRingCat.of k :=
    S.descResidueField (Scheme.stalkClosedPointTo f)
  let : Algebra (S.residueField s) k := φ.hom.toAlgebra
  have hκ := hi.residueFiber s
  have hk := parabolicFieldExtensionStatement (S.residueField s) k
    ((GroupScheme.baseChange (S.fromSpecResidueField s)).obj G)
    (hG.isConnectedReductive_residueFiber s)
    ((GroupScheme.baseChange (S.fromSpecResidueField s)).obj P)
    (RelativeLevi.residueFiberHom i s) hκ
  have hfactor : Spec.map φ ≫ S.fromSpecResidueField s = f :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k S f
  let eP := Descent.pullbackComparison (S.fromSpecResidueField s) (Spec.map φ) f hfactor P
  let eG := Descent.pullbackComparison (S.fromSpecResidueField s) (Spec.map φ) f hfactor G
  change IsParabolicSubgroup
    ((GroupScheme.baseChange (Spec.map φ)).map (RelativeLevi.residueFiberHom i s)) at hk
  have ht := (hk.iso_comp eP.symm).comp_iso eG
  have he : eP.inv ≫
      (GroupScheme.baseChange (Spec.map φ)).map (RelativeLevi.residueFiberHom i s) ≫
      eG.hom = (GroupScheme.baseChange f).map i := by
    rw [Descent.pullbackComparison_naturality, Iso.inv_hom_id_assoc]
  simpa only [Iso.symm_hom, Category.assoc, he] using ht

set_option backward.isDefEq.respectTransparency.types false in
/-- Relative parabolic subgroups of reductive group schemes remain relative
parabolic after arbitrary change of the base scheme. -/
theorem IsRelativeParabolicSubgroup.baseChange (hi : IsRelativeParabolicSubgroup i)
    (hG : IsReductive G) (b : S' ⟶ S) :
    IsRelativeParabolicSubgroup ((GroupScheme.baseChange b).map i) := by
  let : Smooth P.X.hom := hi.smooth
  let : IsAffineHom P.X.hom := hi.isAffineHom
  let : Mono i.hom.hom := hi.mono
  have hm : Mono ((GroupScheme.baseChange b).map i).hom.hom := by
    change Mono ((Over.pullback b).map i.hom.hom)
    infer_instance
  let : Mono ((GroupScheme.baseChange b).map i).hom.hom := hm
  refine ⟨?_, ?_, inferInstance, fun s' => ?_⟩
  · change Smooth (pullback.snd P.X.hom b)
    infer_instance
  · change IsAffineHom (pullback.snd P.X.hom b)
    exact MorphismProperty.pullback_snd _ _ hi.isAffineHom
  · let r : Spec (CommRingCat.of (S'.residueField s')) ⟶ S' := S'.fromSpecResidueField s'
    let eP := Descent.pullbackComparison b r (r ≫ b) rfl P
    let eG := Descent.pullbackComparison b r (r ≫ b) rfl G
    have ht := (hi.isParabolicSubgroup_baseChange hG (r ≫ b)).iso_comp eP
    have h := ht.comp_iso eG.symm
    have he : eP.hom ≫ (GroupScheme.baseChange (r ≫ b)).map i ≫ eG.inv =
        (GroupScheme.baseChange r).map ((GroupScheme.baseChange b).map i) := by
      rw [← Category.assoc, ← Descent.pullbackComparison_naturality,
        Category.assoc, Iso.hom_inv_id, Category.comp_id]
    change IsParabolicSubgroup
      ((eP.hom ≫ (GroupScheme.baseChange (r ≫ b)).map i) ≫ eG.inv) at h
    rw [Category.assoc, he] at h
    exact h

/-- The actual pullback of a reductive group with a relative parabolic subgroup,
retaining the subgroup and its parabolicity. -/
def relativeParabolicBaseChange (b : S' ⟶ S) (hG : IsReductive G) :
    {i : P ⟶ G // IsRelativeParabolicSubgroup i} →
      {j : (GroupScheme.baseChange b).obj P ⟶ (GroupScheme.baseChange b).obj G //
        IsRelativeParabolicSubgroup j} :=
  fun i => ⟨(GroupScheme.baseChange b).map i.val, i.property.baseChange hG b⟩

@[simp]
theorem relativeParabolicBaseChange_val (b : S' ⟶ S) (hG : IsReductive G)
    (j : {i : P ⟶ G // IsRelativeParabolicSubgroup i}) :
    (relativeParabolicBaseChange b hG j).val = (GroupScheme.baseChange b).map j.val := rfl

end Langlands.GroupScheme

import Langlands.GroupScheme.RelativeLevi.ParabolicPresheaf
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.SubgroupFunctor.ZariskiLocality

/-! # Locality and separatedness of actual relative parabolic subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}} {P G : GroupScheme S}

private theorem parabolic_baseChangeHom_isPullback (b : S' ⟶ S) (j : P ⟶ G) :
    IsPullback (pullback.fst P.X.hom b)
      ((GroupScheme.baseChange b).map j).hom.hom.left j.hom.hom.left (pullback.fst G.X.hom b) := by
  have houter : IsPullback
      (((GroupScheme.baseChange b).map j).hom.hom.left ≫ pullback.snd G.X.hom b)
      (pullback.fst P.X.hom b) b (j.hom.hom.left ≫ G.X.hom) := by
    change IsPullback (((Over.pullback b).map j.hom.hom).left ≫ _) _ _ _
    simpa only [Over.w j.hom.hom, Over.pullback_map_left, pullback.lift_snd] using
      (IsPullback.of_hasPullback P.X.hom b).flip
  exact (houter.of_right
    (show ((GroupScheme.baseChange b).map j).hom.hom.left ≫ pullback.fst G.X.hom b =
        pullback.fst P.X.hom b ≫ j.hom.hom.left by
      change ((Over.pullback b).map j.hom.hom).left ≫ _ = _
      simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback G.X.hom b).flip).flip

/-- Relative parabolicity in a reductive group is detected on any Zariski
open cover of the base. -/
theorem IsRelativeParabolicSubgroup.of_openCover (hG : IsReductive G)
    (𝒰 : Scheme.OpenCover.{u} S) (j : P ⟶ G)
    (h : ∀ k, IsRelativeParabolicSubgroup ((GroupScheme.baseChange (𝒰.f k)).map j)) :
    IsRelativeParabolicSubgroup j := by
  have hs : Smooth P.X.hom :=
    IsZariskiLocalAtTarget.of_openCover (P := @Smooth) 𝒰 fun k => (h k).smooth
  have ha : IsAffineHom P.X.hom :=
    IsZariskiLocalAtTarget.of_openCover (P := @IsAffineHom) 𝒰 fun k => (h k).isAffineHom
  have hm : Mono j.hom.hom.left := by
    apply IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.monomorphisms _)
      (𝒰.pullback₁ G.X.hom)
    intro k
    let : Mono ((GroupScheme.baseChange (𝒰.f k)).map j).hom.hom := (h k).mono
    have hp := parabolic_baseChangeHom_isPullback (𝒰.f k) j
    change Mono (pullback.snd j.hom.hom.left (pullback.fst G.X.hom (𝒰.f k)))
    rw [← hp.isoPullback_inv_snd]
    infer_instance
  refine ⟨hs, ha, Over.mono_of_mono_left _, fun s => ?_⟩
  let k := 𝒰.idx s
  let r : Spec (CommRingCat.of (S.residueField s)) ⟶ S := S.fromSpecResidueField s
  have hr : Set.range r ⊆ Set.range (𝒰.f k) := by
    intro x hx
    have hx' : x = s := by
      rcases hx with ⟨y, rfl⟩
      exact Scheme.fromSpecResidueField_apply s y
    subst x
    exact 𝒰.covers s
  let a : Spec (CommRingCat.of (S.residueField s)) ⟶ 𝒰.X k :=
    IsOpenImmersion.lift (𝒰.f k) r hr
  have har : a ≫ 𝒰.f k = r := IsOpenImmersion.lift_fac _ _ _
  let eP := Descent.pullbackComparison (𝒰.f k) a r har P
  let eG := Descent.pullbackComparison (𝒰.f k) a r har G
  have ht := ((h k).isParabolicSubgroup_baseChange (hG.baseChange (𝒰.f k)) a).iso_comp
    eP.symm
  have ht' := ht.comp_iso eG
  have he : eP.inv ≫
      (GroupScheme.baseChange a).map ((GroupScheme.baseChange (𝒰.f k)).map j) ≫ eG.hom =
        (GroupScheme.baseChange r).map j := by
    rw [Descent.pullbackComparison_naturality, Iso.inv_hom_id_assoc]
  simpa only [Iso.symm_hom, Category.assoc, he] using ht'

/-- Relative parabolicity in a reductive ambient group is Zariski local. -/
theorem isRelativeParabolicSubgroup_iff_openCover (hG : IsReductive G)
    (𝒰 : Scheme.OpenCover.{u} S) (j : P ⟶ G) :
    IsRelativeParabolicSubgroup j ↔
      ∀ k, IsRelativeParabolicSubgroup ((GroupScheme.baseChange (𝒰.f k)).map j) :=
  ⟨fun hj k => hj.baseChange hG (𝒰.f k), IsRelativeParabolicSubgroup.of_openCover hG 𝒰 j⟩

namespace ParabolicSubgroupModuli

open TorusSubgroupModuli

/-- Fpqc base change embeds actual parabolic subgroup functors. -/
def baseChangeEmbedding (hG : IsReductive G) (b : S' ⟶ S)
    [QuasiCompact b] [Flat b] [Surjective b] :
    ParabolicSubgroup G ↪ ParabolicSubgroup ((GroupScheme.baseChange b).obj G) where
  toFun F := ⟨F.val.baseChange b, F.property.baseChange hG b⟩
  inj' := by
    intro F F' h
    exact Subtype.ext (SubgroupFunctor.eq_of_isRepresentedBy_baseChange_eq b
      (parabolicRepresentative F).represents (parabolicRepresentative F').represents
      (congrArg Subtype.val h))

/-- Actual parabolic subgroup functors are determined on a Zariski cover. -/
theorem eq_of_baseChange_openCover (𝒰 : Scheme.OpenCover.{u} S)
    {F F' : ParabolicSubgroup G}
    (h : ∀ k, F.val.baseChange (𝒰.f k) = F'.val.baseChange (𝒰.f k)) : F = F' := by
  apply Subtype.ext
  let r := parabolicRepresentative F
  let r' := parabolicRepresentative F'
  let : Mono r.hom.hom.hom := r.parabolic.mono
  let : Mono r'.hom.hom.hom := r'.parabolic.mono
  rw [← r.represents.2, ← r'.represents.2] at h ⊢
  exact (SubgroupFunctor.range_eq_iff_baseChange_openCover 𝒰 r.hom r'.hom).mpr h

variable {M T : Over S}

/-- Restriction in the actual parabolic presheaf is injective along every
fpqc parameter morphism. -/
theorem restrict_injective (hG : IsReductive G) (a : T ⟶ M)
    [QuasiCompact a.left] [Flat a.left] [Surjective a.left] :
    Function.Injective (restrict hG a) := by
  intro F F' h
  let r := parabolicRepresentative F
  let r' := parabolicRepresentative F'
  have he : evaluate r.hom a = evaluate r'.hom a := congrArg Subtype.val h
  have hb : F.val.baseChange a.left = F'.val.baseChange a.left := by
    change SubgroupFunctor.range
      ((GroupScheme.baseChange a.left).map r.hom ≫
        (Descent.pullbackComparison M.hom a.left T.hom (Over.w a) G).hom) =
      SubgroupFunctor.range
      ((GroupScheme.baseChange a.left).map r'.hom ≫
        (Descent.pullbackComparison M.hom a.left T.hom (Over.w a) G).hom) at he
    have he' := (SubgroupFunctor.range_comp_iso_eq_iff _ _
      (Descent.pullbackComparison M.hom a.left T.hom (Over.w a) G)).mp he
    simpa only [SubgroupFunctor.range_baseChangeHom, r.represents.2, r'.represents.2]
      using he'
  exact (baseChangeEmbedding (hG.baseChange M.hom) a.left).injective (Subtype.ext hb)

/-- A monic representative is relatively parabolic if it is represented by
relative parabolics on every member of an open cover. -/
theorem isParabolic_of_isRepresentedBy_of_openCover (hG : IsReductive G)
    {F : SubgroupFunctor G} {j : P ⟶ G} (hj : F.IsRepresentedBy j)
    (𝒰 : Scheme.OpenCover.{u} S)
    (h : ∀ k, IsParabolic (F.baseChange (𝒰.f k))) : IsParabolic F := by
  refine ⟨P, j, IsRelativeParabolicSubgroup.of_openCover hG 𝒰 j ?_, hj⟩
  intro k
  let r := parabolicRepresentative ⟨F.baseChange (𝒰.f k), h k⟩
  let e := (hj.baseChange (𝒰.f k)).isoOfIsRepresentedBy r.represents
  have he : e.hom ≫ r.hom = (GroupScheme.baseChange (𝒰.f k)).map j :=
    (hj.baseChange (𝒰.f k)).isoOfIsRepresentedBy_hom_comp r.represents
  simpa only [he] using r.parabolic.iso_comp e

end ParabolicSubgroupModuli

end Langlands.GroupScheme

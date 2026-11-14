import Langlands.GroupScheme.RelativeLevi.BorelDynamicPresentationStatement
import Langlands.GroupScheme.Reductive.SteinbergBigCellGeometry
import Langlands.GroupScheme.SubgroupFunctor.ZariskiLocality
import Langlands.GroupScheme.Dynamic.OppositeBaseChange
import Langlands.GroupScheme.Dynamic.BaseRepresentabilityProof

/-! # The intersection in the local opposite Borel construction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace Dynamic

variable {S : Scheme.{u}} {G Z : GroupScheme S}

/-- If a cocharacter centralizer has a supplied representative, the two
opposite dynamic parabolics meet in that representative over any base. -/
theorem parabolic_inf_opposite_eq_range [IsAffineHom G.X.hom]
    (χ : (Gm S).toGrp ⟶ G) (z : Z ⟶ G)
    (hz : (centralizer χ).IsRepresentedBy z) :
    parabolic χ ⊓ parabolic (oppositeCocharacter χ) =
      SubgroupFunctor.range z := by
  let : Mono z.hom.hom := hz.1
  apply le_antisymm
  · apply (SubgroupFunctor.le_range_iff_baseChange_openCover
      S.affineOpenCover.openCover z).mpr
    intro a
    let b := S.affineOpenCover.f a
    let G' := (GroupScheme.baseChange b).obj G
    have : IsAffineHom G'.X.hom :=
      inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b))
    have : IsAffine G'.X.left := isAffine_of_isAffineHom G'.X.hom
    have hop : baseChangeCocharacter b (oppositeCocharacter χ) =
        oppositeCocharacter (baseChangeCocharacter b χ) := by
      simpa only [oppositeCocharacter] using baseChangeCocharacter_powerHom b χ (-1)
    change (parabolic χ ⊓ parabolic (oppositeCocharacter χ)).baseChange b ≤
      (SubgroupFunctor.range z).baseChange b
    rw [SubgroupFunctor.inf_baseChange, ← parabolic_baseChange,
      ← parabolic_baseChange, hop,
      parabolic_inf_opposite_eq_centralizer, centralizer_baseChange, ← hz.2]
  · rw [hz.2]
    intro U g hg
    refine ⟨centralizer_le_parabolic χ U hg, ?_⟩
    apply centralizer_le_parabolic (oppositeCocharacter χ) U
    rwa [centralizer_oppositeCocharacter]

end Dynamic

namespace SubgroupFunctor

/-- A monomorphic representative of a closed representable subgroup is closed. -/
theorem IsRepresentedBy.isClosedSubgroup_of_isClosedRepresentable
    {S : Scheme.{u}} {G H : GroupScheme S} {F : SubgroupFunctor G}
    {i : H ⟶ G} (hi : F.IsRepresentedBy i) (hF : F.IsClosedRepresentable) :
    IsClosedSubgroup i := by
  obtain ⟨K, j, hj, hjc⟩ := hF
  rw [← hi.isoOfIsRepresentedBy_hom_comp hj]
  exact (IsClosedSubgroup.of_iso (hi.isoOfIsRepresentedBy hj)).comp hjc

end SubgroupFunctor

/-- The dynamic presentation input supplies actual closed opposite Borels
on an étale cover, including the all-test intersection equality. -/
theorem exists_etaleLocal_oppositeBorel
    (hpresentation : RelativeBorelDynamicPresentationStatement.{u})
    {S : Scheme.{u}} {G B : GroupScheme S} (i : B ⟶ G)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G)
    (hG : IsReductive G) (hT : RelativeTorus.IsTorus T.toGrp)
    (ht : IsClosedSubgroup t) (hmax : IsFibrewiseMaximalTorus t)
    (hi : IsRelativeBorelSubgroup i)
    (hti : SubgroupFunctor.range t ≤ SubgroupFunctor.range i) :
    ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
      ∀ a : 𝒰.I₀,
        ∃ (C : GroupScheme (𝒰.X a))
          (j : C ⟶ (GroupScheme.baseChange (𝒰.f a)).obj G),
          IsRelativeBorelSubgroup j ∧ IsClosedSubgroup j ∧
            SubgroupFunctor.range j ⊓
                SubgroupFunctor.range ((GroupScheme.baseChange (𝒰.f a)).map i) =
              SubgroupFunctor.range ((GroupScheme.baseChange (𝒰.f a)).map t) := by
  obtain ⟨𝒰, h𝒰⟩ := hpresentation S G B i T t hG hT ht hmax hi hti
  refine ⟨𝒰, fun a => ?_⟩
  let b := 𝒰.f a
  let G' := (GroupScheme.baseChange b).obj G
  let t' := (GroupScheme.baseChange b).map t
  obtain ⟨_, ν, hpos, hcentral, C, j, hj, hneg⟩ := h𝒰 a
  let χ := CommGroupScheme.groupHom ν ≫ t'
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G'.X.hom :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) G.X.hom b hG.isAffineHom
  have : Smooth G'.X.hom :=
    inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b))
  have hjrep : (Dynamic.parabolic (Dynamic.oppositeCocharacter χ)).IsRepresentedBy j :=
    ⟨hj.isRelativeParabolicSubgroup.mono, hneg⟩
  have hjclosed : IsClosedSubgroup j := by
    obtain ⟨K, k, hkc, _, hkr⟩ :=
      (dynamicBaseRepresentability (𝒰.X a) G' (Dynamic.oppositeCocharacter χ)).1
    exact hjrep.isClosedSubgroup_of_isClosedRepresentable ⟨K, k, hkr, hkc⟩
  have : IsClosedImmersion t'.hom.hom.left := ht.baseChange b
  have htmono : Mono t'.hom.hom := Over.mono_of_mono_left _
  have htrep : (Dynamic.centralizer χ).IsRepresentedBy t' :=
    ⟨htmono, hcentral.symm⟩
  refine ⟨C, j, hj, hjclosed, ?_⟩
  rw [hneg, hpos]
  calc
    Dynamic.parabolic (Dynamic.oppositeCocharacter χ) ⊓ Dynamic.parabolic χ =
        Dynamic.parabolic χ ⊓ Dynamic.parabolic (Dynamic.oppositeCocharacter χ) := by
      apply SubgroupFunctor.ext
      intro U
      apply Subgroup.ext
      intro x
      exact and_comm
    _ = SubgroupFunctor.range t' := Dynamic.parabolic_inf_opposite_eq_range χ t' htrep

end Langlands.GroupScheme

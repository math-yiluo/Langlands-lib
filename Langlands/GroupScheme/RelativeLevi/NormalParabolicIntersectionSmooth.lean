import Langlands.GroupScheme.AutomorphicAction.ParabolicSmooth
import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalRigidity
import Langlands.GroupScheme.RelativeLevi.ParabolicClosedProof
import Langlands.GroupScheme.RelativeLevi.MultiplicationDescent
import Langlands.GroupScheme.SubgroupIntersectionKernelComparison

/-! # Smooth intersections of normal subgroups with relative parabolics -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}} {G N P : GroupScheme S}

/-- Intersection with a dynamic parabolic represents the parabolic of the
normalized conjugation action on a closed subgroup. -/
theorem intersection_represents_action_parabolic
    (n : N ⟶ G) (i : P ⟶ G) (χ : (Gm S).toGrp ⟶ G)
    (hnc : IsClosedSubgroup n) (hic : IsClosedSubgroup i)
    (hi : (Dynamic.parabolic χ).IsRepresentedBy i)
    (hn : (SubgroupFunctor.range n).IsNormalizedBy (SubgroupFunctor.range χ)) :
    let _ : IsClosedImmersion n.hom.hom.left := hnc
    let _ : Mono n.hom.hom := Over.mono_of_mono_left n.hom.hom
    (AutomorphicAction.ofNormalizedConjugation n χ hn).parabolic.IsRepresentedBy
      (subgroupIntersectionFst n i) := by
  let : IsClosedImmersion n.hom.hom.left := hnc
  let : Mono n.hom.hom := Over.mono_of_mono_left _
  let : IsClosedImmersion (subgroupIntersectionFst n i).hom.hom.left :=
    isClosedSubgroup_subgroupIntersectionFst n hic
  refine ⟨Over.mono_of_mono_left _, ?_⟩
  rw [range_subgroupIntersectionFst_eq_comap, hi.2,
    AutomorphicAction.IsEquivariant.parabolic_eq_comap_of_isClosedSubgroup
      (normalized_isEquivariant n χ hn) hnc,
    AutomorphicAction.cocharacterAction_parabolic]

/-- The actual intersection, bundled as a closed model of the parabolic of
normalized conjugation. -/
def normalizedParabolicIntersectionModel
    (n : N ⟶ G) (i : P ⟶ G) (χ : (Gm S).toGrp ⟶ G)
    (hnc : IsClosedSubgroup n) (hic : IsClosedSubgroup i)
    (hi : (Dynamic.parabolic χ).IsRepresentedBy i)
    (hn : (SubgroupFunctor.range n).IsNormalizedBy (SubgroupFunctor.range χ)) :
    let _ : IsClosedImmersion n.hom.hom.left := hnc
    let _ : Mono n.hom.hom := Over.mono_of_mono_left n.hom.hom
    Σ K : GroupScheme S, {j : K ⟶ N //
      (AutomorphicAction.ofNormalizedConjugation n χ hn).parabolic.IsRepresentedBy j ∧
        IsClosedSubgroup j} :=
  ⟨subgroupIntersection n i, subgroupIntersectionFst n i,
    intersection_represents_action_parabolic n i χ hnc hic hi hn,
    isClosedSubgroup_subgroupIntersectionFst n hic⟩

/-- A smooth affine closed subgroup normalized by a cocharacter has smooth
intersection with its dynamic parabolic, over any base. -/
theorem smooth_normalized_dynamicIntersection
    [IsAffineHom N.X.hom] [Smooth N.X.hom]
    (n : N ⟶ G) (i : P ⟶ G) (χ : (Gm S).toGrp ⟶ G)
    (hnc : IsClosedSubgroup n) (hic : IsClosedSubgroup i)
    (hi : (Dynamic.parabolic χ).IsRepresentedBy i)
    (hn : (SubgroupFunctor.range n).IsNormalizedBy (SubgroupFunctor.range χ)) :
    Smooth (subgroupIntersection n i).X.hom := by
  let : IsClosedImmersion n.hom.hom.left := hnc
  let : Mono n.hom.hom := Over.mono_of_mono_left _
  let : IsClosedImmersion (subgroupIntersectionFst n i).hom.hom.left :=
    isClosedSubgroup_subgroupIntersectionFst n hic
  let : IsAffineHom (subgroupIntersection n i).X.hom := by
    rw [← Over.w (subgroupIntersectionFst n i).hom.hom]
    infer_instance
  exact AutomorphicAction.smooth_of_isRepresentedBy_parabolic
    (AutomorphicAction.ofNormalizedConjugation n χ hn)
    (normalizedParabolicIntersectionModel n i χ hnc hic hi hn).2.2.1

/-- A smooth affine normal closed subgroup of a reductive group scheme has
smooth intersection with every relative parabolic subgroup. -/
theorem smooth_normal_parabolicIntersection
    [IsAffineHom N.X.hom] [Smooth N.X.hom]
    (hG : IsReductive G) (n : N ⟶ G) (hnc : IsClosedSubgroup n)
    (hn : (SubgroupFunctor.range n).IsNormal)
    (i : P ⟶ G) (hi : IsRelativeParabolicSubgroup i) :
    Smooth (subgroupIntersection n i).X.hom := by
  obtain ⟨𝒰, h𝒰⟩ := relativeParabolicEtaleLocalDynamic S G P i hG hi
  apply smooth_of_etaleCover 𝒰 (subgroupIntersection n i)
  intro k
  let b := 𝒰.f k
  let : IsAffineHom ((baseChange b).obj N).X.hom :=
    DynamicBaseSmoothConnected.isAffineHom_baseChange b
  let : Smooth ((baseChange b).obj N).X.hom :=
    DynamicBaseSmoothConnected.smooth_baseChange b
  obtain ⟨χ, hχ⟩ := h𝒰 k
  have hn' : (SubgroupFunctor.range ((baseChange b).map n)).IsNormal := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hn.baseChange b
  have hnorm : (SubgroupFunctor.range ((baseChange b).map n)).IsNormalizedBy
      (SubgroupFunctor.range χ) :=
    fun T g x _ hx => hn' T g x (Subgroup.mem_top _) hx
  have hs : Smooth (subgroupIntersection ((baseChange b).map n)
      ((baseChange b).map i)).X.hom :=
    smooth_normalized_dynamicIntersection ((baseChange b).map n)
      ((baseChange b).map i) χ (hnc.baseChange b)
      ((relativeParabolicClosed S G P i hG hi).baseChange b) hχ hnorm
  exact smooth_of_over_iso
    ((Grp.forget _).mapIso (subgroupIntersectionBaseChangeIso b n i)) hs

end Langlands.GroupScheme.RelativeLevi

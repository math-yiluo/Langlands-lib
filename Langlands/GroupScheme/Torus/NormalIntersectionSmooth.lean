import Langlands.GroupScheme.AutomorphicAction
import Langlands.GroupScheme.Rational.KernelCentralizerSmooth
import Langlands.GroupScheme.SubgroupIntersectionKernelComparison
import Langlands.GroupScheme.Torus.RelativeCentralizerSmooth
import Langlands.GroupScheme.SmoothProducts
import Langlands.GroupScheme.Torus.MaximalSelfCentralizingDescent
import Langlands.GroupScheme.RelativeLevi.BorelEtaleTransport

/-! # Smooth intersections with self-centralizing tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace AutomorphicAction

/-- Fixedness of normalized conjugation is ambient centralization, on every test. -/
theorem ofNormalizedConjugation_fixedSubgroup_eq_comap_torusCentralizer
    {S : Scheme.{u}} {G H : GroupScheme S} {T : CommGroupScheme S}
    (j : H ⟶ G) (t : T.toGrp ⟶ G) [Mono j.hom.hom]
    (hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range t)) :
    (ofNormalizedConjugation j t hn).fixedSubgroup = (torusCentralizer t).comap j := by
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro x
  rw [mem_fixedSubgroup, SubgroupFunctor.mem_comap, mem_torusCentralizer]
  have hact {V : Over S} (s : V ⟶ T.X) (y : V ⟶ H.X) :
      (ofNormalizedConjugation j t hn).act s y ≫ j.hom.hom =
        (s ≫ t.hom.hom) * (y ≫ j.hom.hom) * (s ≫ t.hom.hom)⁻¹ :=
    SubgroupFunctor.lift_comp_normalizedConjugation_comp j t hn s y
  constructor
  · intro hx V b s
    have he := congrArg (fun f => f ≫ j.hom.hom) (hx V b s)
    rw [hact] at he
    exact ((mul_inv_eq_iff_eq_mul).mp he).symm
  · intro hx V b s
    apply (cancel_mono j.hom.hom).mp
    rw [hact]
    have hc := hx V b s
    rw [← Category.assoc] at hc
    rw [hc.symm.eq, mul_inv_cancel_right]

/-- Fixed subgroups for split-torus actions on smooth affine groups over a ring
have a smooth closed representative. -/
theorem fixedSubgroup_hasSmoothClosedRepresentative_of_splitTorus_overRing
    {R : CommRingCat.{u}} {H : GroupScheme (Spec R)}
    [IsAffine H.X.left] {T : CommGroupScheme (Spec R)}
    (a : AutomorphicAction T.toGrp H) (hT : IsSplitTorus T.toGrp)
    (hH : Smooth H.X.hom) : a.fixedSubgroup.HasSmoothClosedRepresentative := by
  classical
  obtain ⟨I, hfin, ⟨eT⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  let e := Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ)) ≪≫ eT.symm
  have h := CharacterAction.fixedSubgroup_hasSmoothClosedRepresentative
    (a.restrict e.hom) hH
  rwa [fixedSubgroup_restrict_iso] at h

end AutomorphicAction

/-- A supplied closed self-centralizing commutative subgroup cuts out the
fixed subgroup of its normalized conjugation action on another subgroup. -/
theorem isRepresentedBy_subgroupIntersectionFst_normalizedFixed
    {S : Scheme.{u}} {G H : GroupScheme S} {T : CommGroupScheme S}
    (j : H ⟶ G) (t : T.toGrp ⟶ G) [Mono j.hom.hom]
    (ht : IsClosedSubgroup t)
    (hself : torusCentralizer t = SubgroupFunctor.range t)
    (hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range t)) :
    (AutomorphicAction.ofNormalizedConjugation j t hn).fixedSubgroup.IsRepresentedBy
      (subgroupIntersectionFst j t) := by
  let : IsClosedImmersion (subgroupIntersectionFst j t).hom.hom.left :=
    isClosedSubgroup_subgroupIntersectionFst j ht
  refine ⟨Over.mono_of_mono_left _, ?_⟩
  rw [AutomorphicAction.ofNormalizedConjugation_fixedSubgroup_eq_comap_torusCentralizer,
    hself, range_subgroupIntersectionFst_eq_comap]

/-- The actual intersection, bundled as a closed model of normalized fixedness. -/
def normalizedTorusIntersectionFixedModel
    {S : Scheme.{u}} {G H : GroupScheme S} {T : CommGroupScheme S}
    (j : H ⟶ G) (t : T.toGrp ⟶ G) [Mono j.hom.hom]
    (ht : IsClosedSubgroup t)
    (hself : torusCentralizer t = SubgroupFunctor.range t)
    (hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range t)) :
    Σ F : GroupScheme S, {f : F ⟶ H //
      (AutomorphicAction.ofNormalizedConjugation j t hn).fixedSubgroup.IsRepresentedBy f ∧
        IsClosedSubgroup f} :=
  ⟨subgroupIntersection j t, subgroupIntersectionFst j t,
    isRepresentedBy_subgroupIntersectionFst_normalizedFixed j t ht hself hn,
    isClosedSubgroup_subgroupIntersectionFst j ht⟩

/-- Over an arbitrary ring the intersection of a smooth affine normalized
subgroup with a closed self-centralizing split torus is smooth. -/
theorem subgroupIntersection_smooth_of_selfCentralizing_splitTorus_overRing
    {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
    [IsAffine H.X.left] {T : CommGroupScheme (Spec R)}
    (j : H ⟶ G) (t : T.toGrp ⟶ G) [Mono j.hom.hom]
    (hH : Smooth H.X.hom) (hT : IsSplitTorus T.toGrp)
    (ht : IsClosedSubgroup t)
    (hself : torusCentralizer t = SubgroupFunctor.range t)
    (hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range t)) :
    Smooth (subgroupIntersection j t).X.hom := by
  let a := AutomorphicAction.ofNormalizedConjugation j t hn
  obtain ⟨F, f, _, hF, hf⟩ :=
    a.fixedSubgroup_hasSmoothClosedRepresentative_of_splitTorus_overRing hT hH
  have hi := isRepresentedBy_subgroupIntersectionFst_normalizedFixed j t ht hself hn
  exact smooth_of_over_iso
    ((Grp.forget _).mapIso (hi.isoOfIsRepresentedBy hf)) hF

/-- The same smooth-intersection statement over any base scheme, with a
relatively affine normalized subgroup. -/
theorem subgroupIntersection_smooth_of_selfCentralizing_splitTorus
    {S : Scheme.{u}} {G H : GroupScheme S}
    [IsAffineHom H.X.hom] {T : CommGroupScheme S}
    (j : H ⟶ G) (t : T.toGrp ⟶ G) [Mono j.hom.hom]
    (hH : Smooth H.X.hom) (hT : IsSplitTorus T.toGrp)
    (ht : IsClosedSubgroup t)
    (hself : torusCentralizer t = SubgroupFunctor.range t)
    (hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range t)) :
    Smooth (subgroupIntersection j t).X.hom := by
  let : Smooth H.X.hom := hH
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := @Smooth)
    S.affineOpenCover.openCover).mpr
  intro k
  let b := S.affineOpenCover.f k
  let B := GroupScheme.baseChange b
  let : IsAffineHom (B.obj H).X.hom :=
    MorphismProperty.pullback_snd H.X.hom b inferInstance
  let : IsAffine (B.obj H).X.left := isAffine_of_isAffineHom (B.obj H).X.hom
  have hselfB : torusCentralizer (T := (CommGroupScheme.baseChange b).obj T) (B.map t) =
      SubgroupFunctor.range (B.map t) :=
    (torusCentralizer_baseChange b (T := T) t).trans
      ((congrArg (fun F : SubgroupFunctor G => F.baseChange b) hself).trans
        (SubgroupFunctor.range_baseChangeHom b t).symm)
  have hnB : (SubgroupFunctor.range (B.map j)).IsNormalizedBy
      (SubgroupFunctor.range (B.map t)) := by
    change (SubgroupFunctor.range ((GroupScheme.baseChange b).map j)).IsNormalizedBy
      (SubgroupFunctor.range ((GroupScheme.baseChange b).map t))
    rw [SubgroupFunctor.range_baseChangeHom b j, SubgroupFunctor.range_baseChangeHom b t]
    exact hn.baseChange b
  have hsm := subgroupIntersection_smooth_of_selfCentralizing_splitTorus_overRing
    (R := S.affineOpenCover.X k)
    (T := (CommGroupScheme.baseChange b).obj T) (B.map j) (B.map t)
    (inferInstanceAs (Smooth (pullback.snd H.X.hom b)))
    (hT.baseChange b) (ht.baseChange b) hselfB hnB
  exact smooth_of_over_iso
    ((Grp.forget _).mapIso (subgroupIntersectionBaseChangeIso b j t)) hsm

/-- Étale splitting extends smoothness of the actual intersection to a
self-centralizing relative torus over any scheme. -/
theorem subgroupIntersection_smooth_of_selfCentralizing_relativeTorus
    {S : Scheme.{u}} {G H : GroupScheme S}
    [IsAffineHom H.X.hom] {T : CommGroupScheme S}
    (j : H ⟶ G) (t : T.toGrp ⟶ G) [Mono j.hom.hom]
    (hH : Smooth H.X.hom) (hT : RelativeTorus.IsTorus T.toGrp)
    (ht : IsClosedSubgroup t)
    (hself : torusCentralizer t = SubgroupFunctor.range t)
    (hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range t)) :
    Smooth (subgroupIntersection j t).X.hom := by
  let : Smooth H.X.hom := hH
  obtain ⟨𝒰, h𝒰⟩ := hT
  apply RelativeLevi.smooth_of_etale_cover_pullbacks 𝒰
  intro k
  let b := 𝒰.f k
  let B := GroupScheme.baseChange b
  let : IsAffineHom (B.obj H).X.hom :=
    MorphismProperty.pullback_snd H.X.hom b inferInstance
  have hselfB : torusCentralizer (T := (CommGroupScheme.baseChange b).obj T) (B.map t) =
      SubgroupFunctor.range (B.map t) :=
    (torusCentralizer_baseChange b (T := T) t).trans
      ((congrArg (fun F : SubgroupFunctor G => F.baseChange b) hself).trans
        (SubgroupFunctor.range_baseChangeHom b t).symm)
  have hnB : (SubgroupFunctor.range (B.map j)).IsNormalizedBy
      (SubgroupFunctor.range (B.map t)) := by
    change (SubgroupFunctor.range ((GroupScheme.baseChange b).map j)).IsNormalizedBy
      (SubgroupFunctor.range ((GroupScheme.baseChange b).map t))
    rw [SubgroupFunctor.range_baseChangeHom b j, SubgroupFunctor.range_baseChangeHom b t]
    exact hn.baseChange b
  have hsm := subgroupIntersection_smooth_of_selfCentralizing_splitTorus
    (T := (CommGroupScheme.baseChange b).obj T) (B.map j) (B.map t)
    (inferInstanceAs (Smooth (pullback.snd H.X.hom b)))
    (h𝒰 k) (ht.baseChange b) hselfB hnB
  exact smooth_of_over_iso
    ((Grp.forget _).mapIso (subgroupIntersectionBaseChangeIso b j t)) hsm

/-- Intersecting a smooth affine closed normal subgroup of a reductive group
with a relative maximal torus gives a smooth group over the original base. -/
theorem normal_subgroupIntersection_relativeMaximalTorus_smooth
    {S : Scheme.{u}} {G H : GroupScheme S} (hG : IsReductive G)
    {T : CommGroupScheme S} (hT : RelativeTorus.IsTorus T.toGrp)
    (t : T.toGrp ⟶ G) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t)
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (hn : (SubgroupFunctor.range j).IsNormal)
    (hH : Smooth H.X.hom) (hAff : IsAffineHom H.X.hom) :
    Smooth (subgroupIntersection j t).X.hom := by
  let : IsAffineHom H.X.hom := hAff
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  exact subgroupIntersection_smooth_of_selfCentralizing_relativeTorus j t hH hT ht
    (relativeTorusCentralizer_eq_range_of_fibrewiseMaximal hG hT t ht hmax)
    (fun U s x _ hx => hn U s x (Subgroup.mem_top _) hx)

end Langlands.GroupScheme

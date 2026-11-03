import Langlands.GroupScheme.Dynamic.StableIntersection
import Langlands.GroupScheme.Dynamic.NormalizedLimits
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.Reductive.UnipotentQuotient

/-! # A split limit onto the centralizer intersection -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G H Z : GroupScheme S}
    (χ : (Gm S).toGrp ⟶ G) (j : H ⟶ G) (z : Z ⟶ G)

private theorem rangeRep (hj : IsClosedSubgroup j) :
    (SubgroupFunctor.range j).IsRepresentedBy j := by
  have : IsClosedImmersion j.hom.hom.left := hj
  exact ⟨Over.mono_of_mono_left _, rfl⟩

private theorem stableRange
    (hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range χ)) :
    (AutomorphicAction.conjugation χ).IsStable (SubgroupFunctor.range j) := by
  intro T t g hg
  rw [AutomorphicAction.conjugation_act]
  exact hn T _ g (SubgroupFunctor.mem_range.mpr ⟨t, rfl⟩) hg

variable [IsSeparated G.X.hom]

private def subgroupLimitPoints (hj : IsClosedSubgroup j)
    (hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range χ))
    (hp : SubgroupFunctor.range j ≤ parabolic χ) (T : Over S) :
    (SubgroupFunctor.range j).carrier T →*
      (SubgroupFunctor.range j ⊓ centralizer χ).carrier T :=
  (infParabolicLimitHom χ (rangeRep j hj) hj (stableRange χ j hn) T).comp
    (Subgroup.inclusion (show (SubgroupFunctor.range j).carrier T ≤
      (SubgroupFunctor.range j ⊓ parabolic χ).carrier T from
        fun _ hg => ⟨hg, hp T hg⟩))

private theorem subgroupLimitPoints_comp (hj : IsClosedSubgroup j)
    (hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range χ))
    (hp : SubgroupFunctor.range j ≤ parabolic χ)
    {T T' : Over S} (a : T' ⟶ T) (x : (SubgroupFunctor.range j).carrier T) :
    (subgroupLimitPoints χ j hj hn hp T'
      ⟨a ≫ x, (SubgroupFunctor.range j).comp_mem a x.2⟩ : T' ⟶ G.X) =
      a ≫ (subgroupLimitPoints χ j hj hn hp T x : T ⟶ G.X) :=
  infParabolicLimitHom_comp χ (rangeRep j hj) hj (stableRange χ j hn) a
    ⟨x, x.2, hp T x.2⟩

omit [IsSeparated G.X.hom] in
private theorem intersectionRep (hj : IsClosedSubgroup j)
    (hz : (centralizer χ).IsRepresentedBy z) (hzc : IsClosedSubgroup z) :
    (SubgroupFunctor.range j ⊓ centralizer χ).IsRepresentedBy
      (subgroupIntersectionHom j z) := by
  rw [← hz.2]
  exact isRepresentedBy_subgroupIntersectionHom hj hzc

/-- The limit of a point of a closed normalized subgroup contained in `P(χ)`,
as a morphism to its scheme-theoretic intersection with `Z(χ)`. -/
def subgroupCentralizerLimit (hj : IsClosedSubgroup j)
    (hz : (centralizer χ).IsRepresentedBy z) (hzc : IsClosedSubgroup z)
    (hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range χ))
    (hp : SubgroupFunctor.range j ≤ parabolic χ) :
    H ⟶ subgroupIntersection j z :=
  (rangeRep j hj).lift (intersectionRep χ j z hj hz hzc)
    (subgroupLimitPoints χ j hj hn hp)
    (subgroupLimitPoints_comp χ j hj hn hp)

/-- The constructed scheme morphism induces the existing limit on every test. -/
theorem subgroupCentralizerLimit_comp (hj : IsClosedSubgroup j)
    (hz : (centralizer χ).IsRepresentedBy z) (hzc : IsClosedSubgroup z)
    (hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range χ))
    (hp : SubgroupFunctor.range j ≤ parabolic χ)
    {T : Over S} (x : T ⟶ H.X) :
    (x ≫ (subgroupCentralizerLimit χ j z hj hz hzc hn hp).hom.hom) ≫
        (subgroupIntersectionHom j z).hom.hom =
      limit χ ⟨x ≫ j.hom.hom, hp T (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)⟩ :=
  (rangeRep j hj).lift_comp (intersectionRep χ j z hj hz hzc)
    (subgroupLimitPoints χ j hj hn hp)
    (subgroupLimitPoints_comp χ j hj hn hp) x

/-- Inclusion of the centralizer intersection is a section of the limit map. -/
theorem subgroupIntersectionFst_subgroupCentralizerLimit (hj : IsClosedSubgroup j)
    (hz : (centralizer χ).IsRepresentedBy z) (hzc : IsClosedSubgroup z)
    (hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range χ))
    (hp : SubgroupFunctor.range j ≤ parabolic χ) :
    subgroupIntersectionFst j z ≫ subgroupCentralizerLimit χ j z hj hz hzc hn hp =
      𝟙 (subgroupIntersection j z) := by
  apply (intersectionRep χ j z hj hz hzc).hom_ext
  apply (Grp.forget (Over S)).map_injective
  change ((subgroupIntersectionFst j z).hom.hom ≫
      (subgroupCentralizerLimit χ j z hj hz hzc hn hp).hom.hom) ≫
      (subgroupIntersectionHom j z).hom.hom =
    𝟙 _ ≫ (subgroupIntersectionHom j z).hom.hom
  rw [subgroupCentralizerLimit_comp]
  apply (limit_eq χ ?_).trans (Category.id_comp _).symm
  apply hasLimit_of_mem_centralizer
  rw [← hz.2]
  refine SubgroupFunctor.mem_range.mpr
    ⟨(subgroupIntersectionSnd j z).hom.hom, ?_⟩
  exact congrArg (Grp.forget (Over S)).map
    (subgroupIntersection_condition j z).symm

/-- The restricted limit is split epimorphic even as a morphism of schemes. -/
theorem subgroupCentralizerLimit_epi (hj : IsClosedSubgroup j)
    (hz : (centralizer χ).IsRepresentedBy z) (hzc : IsClosedSubgroup z)
    (hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range χ))
    (hp : SubgroupFunctor.range j ≤ parabolic χ) :
    Epi (subgroupCentralizerLimit χ j z hj hz hzc hn hp).hom.hom.left := by
  apply CategoryTheory.SplitEpi.epi
  refine ⟨(subgroupIntersectionFst j z).hom.hom.left, ?_⟩
  exact congrArg (fun f => f.hom.hom.left)
    (subgroupIntersectionFst_subgroupCentralizerLimit χ j z hj hz hzc hn hp)

/-- Connectedness of a normalized subgroup contained in `P(χ)` passes to its
centralizer intersection through the split limit. -/
theorem subgroupIntersection_connectedSpace (hj : IsClosedSubgroup j)
    (hz : (centralizer χ).IsRepresentedBy z) (hzc : IsClosedSubgroup z)
    (hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range χ))
    (hp : SubgroupFunctor.range j ≤ parabolic χ) [ConnectedSpace H.X.left] :
    ConnectedSpace (subgroupIntersection j z).X.left := by
  let q := subgroupCentralizerLimit χ j z hj hz hzc hn hp
  have he : (subgroupIntersectionFst j z).hom.hom.left ≫ q.hom.hom.left = 𝟙 _ :=
    congrArg (fun f => f.hom.hom.left)
      (subgroupIntersectionFst_subgroupCentralizerLimit χ j z hj hz hzc hn hp)
  have hs : Function.Surjective q.hom.hom.left := by
    intro x
    exact ⟨(subgroupIntersectionFst j z).hom.hom.left x,
      congrArg (fun f : (subgroupIntersection j z).X.left ⟶
        (subgroupIntersection j z).X.left => f x) he⟩
  exact hs.connectedSpace q.hom.hom.left.continuous

end Langlands.GroupScheme.Dynamic

namespace Langlands.GroupScheme.Dynamic

variable {k : Type u} [Field k]
    {G H Z : GroupScheme (Spec (CommRingCat.of k))} [IsSeparated G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (j : H ⟶ G) (z : Z ⟶ G)

/-- Unipotence passes to the centralizer intersection by the split limit. -/
theorem subgroupIntersection_isUnipotent (hj : IsClosedSubgroup j)
    (hz : (centralizer χ).IsRepresentedBy z) (hzc : IsClosedSubgroup z)
    (hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range χ))
    (hp : SubgroupFunctor.range j ≤ parabolic χ) (hH : IsUnipotent H) :
    IsUnipotent (subgroupIntersection j z) := by
  let := subgroupCentralizerLimit_epi χ j z hj hz hzc hn hp
  exact hH.of_epi (subgroupCentralizerLimit χ j z hj hz hzc hn hp)

end Langlands.GroupScheme.Dynamic

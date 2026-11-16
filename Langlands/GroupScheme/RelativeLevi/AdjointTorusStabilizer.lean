import Langlands.GroupScheme.RelativeLevi.AdjointBorelStabilizer
import Langlands.GroupScheme.RelativeLevi.BorelTorusProjection
import Langlands.GroupScheme.RelativeLevi.RightCosetProjection
import Langlands.GroupScheme.RelativeLevi.SelfNormalizerProof
import Langlands.GroupScheme.SubgroupFunctor.IntersectionNormalizer
import Langlands.GroupScheme.Absolute.BorelGmQuotients
import Langlands.GroupScheme.Torus.MaximalSelfCentralizingDescent

/-! # The actual maximal-torus stabilizer inside the adjoint Borel -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section GeneralBase

variable {S : Scheme.{u}} {G B : GroupScheme S} {i : B ⟶ G}
    (hi : IsRelativeBorelSubgroup i) (hG : IsReductive G)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ B)
    (hT : RelativeTorus.IsTorus T.toGrp)
    (htG : IsClosedSubgroup (t ≫ i))
    (hmax : IsFibrewiseMaximalTorus (t ≫ i))

include hi hG hT htG hmax in
/-- The ambient normalizer of a supplied maximal torus intersects the Borel
in exactly that torus, on every test scheme. -/
theorem IsRelativeBorelSubgroup.maximalTorus_normalizer_comap :
    ((SubgroupFunctor.range (t ≫ i)).normalizer).comap i =
      SubgroupFunctor.range t := by
  let : Mono i.hom.hom := hi.1.mono
  have hpre : (SubgroupFunctor.range (t ≫ i)).comap i =
      SubgroupFunctor.range t :=
    SubgroupFunctor.comap_range_of_factor i (t ≫ i) t rfl
  have hn : (SubgroupFunctor.range t).normalizer = SubgroupFunctor.range t :=
    relativeLeviSelfNormalizer S G B T.toGrp i t hG hi.1
      (hi.isRelativeLeviSubgroup_of_maximalTorus hG T t hT htG hmax)
  apply le_antisymm
  · exact (SubgroupFunctor.comap_normalizer_le i _).trans
      (by rw [hpre, hn])
  · rw [← hn]
    exact SubgroupFunctor.normalizer_range_le_comap t i

end GeneralBase

section OverRing

variable {R : Type u} [CommRing R]
    {G B A : GroupScheme (Spec (CommRingCat.of R))}
    {i : B ⟶ G} (hi : IsRelativeBorelSubgroup i) (hG : IsReductive G)
    (q : G ⟶ A) (hq : RelativeRoot.IsFppfQuotient (center G) q)
    (a : AutomorphicAction A G)
    (ha : a.restrict q = AutomorphicAction.conjugation (𝟙 G))
    (T : CommGroupScheme (Spec (CommRingCat.of R))) (t : T.toGrp ⟶ B)
    (hT : RelativeTorus.IsTorus T.toGrp)
    (htG : IsClosedSubgroup (t ≫ i))
    (hmax : IsFibrewiseMaximalTorus (t ≫ i))

include hi hG hq ha hT htG hmax in
private theorem adjointTorusStabilizerData_nonempty
    (d : SubgroupFunctor.QuotientSubgroupData i q
      (a.subgroupStabilizer (SubgroupFunctor.range i))) :
    Nonempty (SubgroupFunctor.QuotientSubgroupData t d.projection
      ((a.restrict d.inclusion).subgroupStabilizer
        (SubgroupFunctor.range (t ≫ i)))) := by
  let rd := hi.maximalTorusFppfRetractionData hG T t hT htG hmax
  let : Mono i.hom.hom := hi.1.mono
  let : Mono t.hom.hom :=
    (hi.isRelativeLeviSubgroup_of_maximalTorus hG T t hT htG hmax).isClosedSubgroup.mono_overHom
  let : Mono (t ≫ i).hom.hom := htG.mono_overHom
  let : Flat d.projection.hom.hom.left := d.flat
  let : Surjective d.projection.hom.hom.left := d.surjective
  let : LocallyOfFinitePresentation d.projection.hom.hom.left :=
    d.locallyOfFinitePresentation
  let : IsIso (subgroupMultiplication t rd.radicalInclusion) := rd.multiplication_isIso
  let : IsIso (subgroupMultiplication rd.radicalInclusion t) :=
    (isIso_subgroupMultiplication_reverse_iff t rd.radicalInclusion).mp inferInstance
  let : IsAffineHom B.X.hom := hi.1.isAffineHom
  let : IsClosedImmersion rd.radicalInclusion.hom.hom.left :=
    rd.isRelativeUnipotentRadical.isClosedSubgroup
  let : IsAffineHom rd.radical.X.hom := by
    rw [← Over.w rd.radicalInclusion.hom.hom]
    infer_instance
  let F := (a.restrict d.inclusion).subgroupStabilizer
    (SubgroupFunctor.range (t ≫ i))
  have hF : F.IsFppfLocal :=
    (a.restrict d.inclusion).isFppfLocal_subgroupStabilizer
      (SubgroupFunctor.isFppfLocal_range (t ≫ i))
  have hpre : F.comap d.projection = SubgroupFunctor.range t := by
    dsimp only [F]
    rw [AutomorphicAction.subgroupStabilizer_restrict,
      ← SubgroupFunctor.comap_comp, ← d.square, SubgroupFunctor.comap_comp,
      a.subgroupStabilizer_comap_of_restrict_eq_conjugation q ha]
    exact hi.maximalTorus_normalizer_comap hG T t hT htG hmax
  have hkernel : SubgroupFunctor.range (kernelι d.projection) ≤
      SubgroupFunctor.range t := by
    rw [d.kernel_eq, hq.2.2.2,
      ← SubgroupFunctor.comap_range_of_factor i (t ≫ i) t rfl]
    exact SubgroupFunctor.comap_mono
      (center_le_range_relativeMaximalTorus hG hT (t ≫ i) htG hmax)
  let projection := RelativeLevi.rightCosetProjection t rd.radicalInclusion
  have hfib := RelativeLevi.rightCosetProjection_fibers t rd.radicalInclusion
  let r := HomogeneousQuotientFactorization.desc d.projection
    (SubgroupFunctor.range t) projection hfib hkernel
  have hr : d.projection.hom.hom ≫ r = projection :=
    HomogeneousQuotientFactorization.fac_desc d.projection
      (SubgroupFunctor.range t) projection hfib hkernel
  exact ⟨SubgroupFunctor.quotientSubgroupDataOfCosetMap
    t d.projection F hF hpre projection hfib r hr⟩

/-- Construct the actual quotient of a supplied maximal torus by the ambient
center as its action stabilizer inside the actual adjoint Borel. -/
def IsRelativeBorelSubgroup.adjointTorusStabilizerData :
    let d := hi.adjointStabilizerData hG q hq a ha
    SubgroupFunctor.QuotientSubgroupData t d.projection
      ((a.restrict d.inclusion).subgroupStabilizer
        (SubgroupFunctor.range (t ≫ i))) :=
  Classical.choice (adjointTorusStabilizerData_nonempty
    hi hG q hq a ha T t hT htG hmax (hi.adjointStabilizerData hG q hq a ha))

end OverRing

end Langlands.GroupScheme

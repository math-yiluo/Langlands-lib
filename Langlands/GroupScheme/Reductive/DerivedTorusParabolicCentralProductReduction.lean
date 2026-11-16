import Langlands.GroupScheme.Derived.RelativeMaximalTorusIntersection
import Langlands.GroupScheme.Derived.RelativeMaximalTorusProduct
import Langlands.GroupScheme.Derived.RelativeMaximalTorusInverse
import Langlands.GroupScheme.Reductive.RelativeCentralProductParabolicDescent
import Langlands.GroupScheme.Reductive.DerivedCorrespondenceInjectivity
import Langlands.GroupScheme.Reductive.DerivedCentralIsogenyStatement

/-! # Derived torus and parabolic correspondence from the central-product isogeny -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace DerivedCorrespondence

/-- The four geometric correspondence clauses follow from a supplied central
product and the derived-factor hypotheses of the published target. -/
theorem geometricClauses_of_centralProduct
    {S : Scheme.{u}} {G D Z Q : GroupScheme S}
    (hG : IsReductive G) (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (hn : (SubgroupFunctor.range d).IsNormal) (hD : IsReductive D)
    (hss : ∀ s : S, IsSemisimple (geometricFiber D s))
    (q : G ⟶ Q) (hQ : RelativeTorus.IsTorus Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q)
    (z : Z ⟶ G) (hz : IsCentral z) (hZ : RelativeTorus.IsTorus Z)
    (hprod : IsCentralIsogeny (prodHom z d (hz.commute_values _))) :
    GeometricClauses d z hz := by
  let : IsClosedImmersion d.hom.hom.left := hd
  let : Mono d.hom.hom := Over.mono_of_mono_left _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T t hTmax
    obtain ⟨hT, ht, hmax⟩ := hTmax
    obtain ⟨A, a, hA, ha, hamax, hrange⟩ :=
      relativeDerivedMaximalTorusIntersection hG d hd hD hss q hQ hq t ht hmax hT hn
    refine ⟨⟨A, a, ⟨hA, ha, hamax⟩, hrange⟩, ?_⟩
    exact ⟨RelativeDerivedTorus.intersectionFactor hG z hz d hT t ht hmax,
      (RelativeDerivedTorus.isCentralIsogeny_intersectionFactor
        hG z hz d hT t ht hmax hprod).isIsogeny,
      RelativeDerivedTorus.intersectionFactor_comp hG z hz d hT t ht hmax⟩
  · intro A a hAmax
    obtain ⟨hA, ha, hmax⟩ := hAmax
    obtain ⟨T, t, e, hT, ht, htmax, he, heq, hInt⟩ :=
      RelativeDerivedTorus.exists_extension hG hD z hz hZ d hd hprod a hA ha hmax
    exact ⟨T, t, e, ⟨hT, ht, htmax⟩, he, heq, hInt⟩
  · intro P i hi
    exact ⟨CentralProductParabolic.isRelativeParabolicSubgroup_intersection
        hG hD d hd hn z hz hprod i hi,
      CentralProductParabolic.relativeIntersectionFactor hG i hi z hz d,
      CentralProductParabolic.isCentralIsogeny_relativeIntersectionFactor
        hG i hi z hz d hprod,
      CentralProductParabolic.relativeIntersectionFactor_comp hG i hi z hz d⟩
  · intro P' i' hi'
    exact CentralProductParabolic.exists_relative_inverse hG hD d hd z hz hprod i' hi'

end DerivedCorrespondence

/-- The published central-isogeny statement implies the unchanged published
maximal-torus and parabolic correspondence. -/
def ReductiveDerivedTorusParabolicCentralProductReductionStatement : Prop :=
  ReductiveDerivedCentralIsogenyStatement.{u} →
    ReductiveDerivedTorusParabolicCorrespondenceStatement.{u}

/-- Assemble the four geometric constructions and recover both injectivity
clauses using the published product reconstruction theorem. -/
theorem reductiveDerivedTorusParabolicCentralProductReduction :
    ReductiveDerivedTorusParabolicCentralProductReductionStatement.{u} := by
  intro hcentral
  apply DerivedCorrespondence.correspondence_of_geometric_clauses
  intro S G hG
  dsimp only
  intro D d hd hn hD hss hquot Z z hz hZ
  obtain ⟨Q, q, hQ, hq⟩ := hquot
  have hprod := ((hcentral S G hG).2 D d hd hn hD hss Q q hQ hq Z z hz hZ).1
  exact DerivedCorrespondence.geometricClauses_of_centralProduct
    hG d hd hn hD hss q hQ hq z hz hZ.2.2.1 hprod

end Langlands.GroupScheme

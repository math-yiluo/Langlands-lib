import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.GeneratorMatching
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.MatchingCoefficientLifts
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.RealizationAssembly
import Langlands.Geometry.Analytic.AtlasIntersectionFiniteRecognition

/-! # Effective realization from one locally module-generating matching tuple -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R : PresentedAffinoidAlgebra K}
  {c : Domain.FiniteCover (Domain.whole K R)} {F : LocalAlgebras c}

namespace GeneratorEvaluation

variable (t : PairTransitions F) {n : ℕ} (s : Fin n → t.MatchingAlgebra)
  (hs : ∀ i, Function.Surjective ((F.map i).coefficientMap fun k => t.projection i (s k)))

local notation "P" => matchingPresentation t s hs

private theorem matchingPresentation_baseMap : (P).baseMap = (quotientMap t s).comp (baseMap t s) := by
  apply BoundedAlgHom.ext
  intro a
  apply (matchingEquiv t s hs).toAlgEquiv.injective
  change (P).equiv ((P).equiv.symm (t.structuralMap a)) =
    matchingMap t s (quotientMap t s (baseMap t s a))
  rw [BoundedAlgEquiv.apply_symm_apply]
  exact ((congrArg (fun q => q (baseMap t s a)) (matchingMap_quotientMap t s)).trans
    (congrArg (fun q : BoundedAlgHom K R t.MatchingAlgebra => q a) (globalEvaluation_baseMap t s))).symm

private theorem matchingPresentation_localMap (i : Fin c.size) :
    (localQuotientComparison t s hs i).toBoundedAlgHom.comp ((quotientCover t s).obj i).baseMap =
      (P).localMap i := by
  apply BoundedAlgHom.ext
  intro x
  let e := localQuotientComparison t s hs i
  let f := ((quotientCover t s).obj i).baseMap
  change e (f x) = t.projection i (matchingMap t s x)
  calc
    _ = e (f (matchingInverse t s hs (matchingMap t s x))) :=
      congrArg (fun z => e (f z)) (matchingInverse_matchingMap t s hs x).symm
    _ = e (localInverse t s hs i (matchingMap t s x)) :=
      congrArg e (congrArg (fun h => h (matchingMap t s x)) (matchingInverse_restriction t s hs i))
    _ = _ := e.apply_symm_apply _

private theorem quotientCover_locus (i : Fin c.size) :
    ((quotientCover t s).obj i).locus = (P).preimageLocus i := by
  ext x
  change BanachSpectrum.comap (baseMap t s).toBoundedRingHom
      (BanachSpectrum.comap (quotientMap t s).toBoundedRingHom x) ∈ (c.obj i).locus ↔
    BanachSpectrum.comap (P).baseMap.toBoundedRingHom x ∈ (c.obj i).locus
  rw [matchingPresentation_baseMap t s hs]
  rfl

private def localComponentDomain (i : Fin c.size) : Domain K (P).algebra where
  algebra := F.algebra i
  baseMap := (P).localMap i
  locus := (P).preimageLocus i
  represents := by
    have h := ((quotientCover t s).obj i).represents.postcomp_equiv (localQuotientComparison t s hs i)
    exact (quotientCover_locus t s hs i) ▸ ((matchingPresentation_localMap t s hs i) ▸ h)

/-- The actual pushout along each original stored cover map is boundedly
equivalent to its supplied original finite Banach algebra. -/
def originalComparisonEquiv (i : Fin c.size) :
    BoundedAlgEquiv K ((P).originalBaseChange i) (F.algebra i) :=
  Domain.boundedEquivOfLocusEq ((P).originalDomain i) (localComponentDomain t s hs i) rfl

/-- The entire forward bounded map is the original two-leg comparison. -/
theorem originalComparisonEquiv_eq (i : Fin c.size) :
    (originalComparisonEquiv t s hs i).toBoundedAlgHom = (P).comparison i :=
  (Domain.boundedHom_eq_boundedEquivOfLocusEq ((P).originalDomain i)
    (localComponentDomain t s hs i) rfl ((P).comparison i) ((P).comparison_left i)).symm

end GeneratorEvaluation

/-- Construct every field of the effective original realization from a finite
matching tuple whose projections generate all original local modules. -/
def effectiveRealizationOfGenerators (d : DescentData F) {n : ℕ}
    (s : Fin n → d.toPairTransitions.MatchingAlgebra)
    (hs : ∀ i, Function.Surjective
      ((F.map i).coefficientMap fun k => d.toPairTransitions.projection i (s k))) : EffectiveRealization d :=
  effectiveRealizationOfComparisons d
    (GeneratorEvaluation.matchingPresentation d.toPairTransitions s hs)
    (d.toPairTransitions.structuralMap_isFiniteBanach_of_generators s hs)
    (GeneratorEvaluation.originalComparisonEquiv d.toPairTransitions s hs)
    (GeneratorEvaluation.originalComparisonEquiv_eq d.toPairTransitions s hs)

end Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent

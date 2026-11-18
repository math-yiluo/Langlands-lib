import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.GeneratorKernels
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBoundedMapGluing
import Langlands.Geometry.Analytic.SpecialCoverIntersectionQuotient

/-! # The global generator quotient and its original local comparisons -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent.GeneratorEvaluation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R : PresentedAffinoidAlgebra K}
  {c : Domain.FiniteCover (Domain.whole K R)} {F : LocalAlgebras c}
  (t : PairTransitions F) {n : ℕ} (s : Fin n → t.MatchingAlgebra)

local instance : IsClosed (globalKernel t s : Set (algebra t s)) := isClosed_globalKernel t s

/-- The actual global presented quotient by the effective evaluation kernel. -/
def quotientAlgebra : PresentedAffinoidAlgebra K :=
  ClosedQuotient.algebra (algebra t s) (globalKernel t s)

def quotientMap : BoundedAlgHom K (algebra t s) (quotientAlgebra t s) :=
  ClosedQuotient.map (algebra t s) (globalKernel t s)

/-- The matching-valued evaluation descends boundedly to this exact quotient. -/
def matchingMap : BoundedAlgHom K (quotientAlgebra t s) t.MatchingAlgebra :=
  ClosedQuotient.lift (algebra t s) (globalKernel t s) (globalEvaluation t s)
    (fun a ha => by
      have h : a ∈ RingHom.ker (globalEvaluation t s).toAlgHom.toRingHom :=
        (globalKernel_eq t s) ▸ ha
      exact h)

theorem matchingMap_quotientMap :
    (matchingMap t s).comp (quotientMap t s) = globalEvaluation t s :=
  ClosedQuotient.lift_comp_map _ _ _ _

/-- Kernel equality supplies injectivity of the entire descended algebra map. -/
theorem matchingMap_injective : Function.Injective (matchingMap t s) := by
  intro b d hbd
  obtain ⟨a, rfl⟩ := ClosedQuotient.map_surjective (algebra t s) (globalKernel t s) b
  obtain ⟨c, rfl⟩ := ClosedQuotient.map_surjective (algebra t s) (globalKernel t s) d
  have ha := congrArg (fun f => f a) (matchingMap_quotientMap t s)
  have hc := congrArg (fun f => f c) (matchingMap_quotientMap t s)
  have hval : globalEvaluation t s a = globalEvaluation t s c :=
    ha.symm.trans (hbd.trans hc)
  have hker : a - c ∈ RingHom.ker (globalEvaluation t s).toAlgHom.toRingHom :=
    (map_sub (globalEvaluation t s).toAlgHom a c).trans (sub_eq_zero.mpr hval)
  have hmem : a - c ∈ globalKernel t s := (globalKernel_eq t s).symm ▸ hker
  have hz := (ClosedQuotient.map_eq_zero_iff (algebra t s) (globalKernel t s) (a - c)).mpr hmem
  exact sub_eq_zero.mp ((map_sub (ClosedQuotient.map (algebra t s)
    (globalKernel t s)).toAlgHom a c).symm.trans hz)

/-- The same original base subdomain pulled back to the global quotient. -/
def quotientDomain (E : Domain K R) : Domain K (quotientAlgebra t s) :=
  Domain.pullback (quotientMap t s) (restrictedDomain t s E)

/-- Further restriction preserves local evaluation admissibility, with the
actual quotient norms and no open mapping theorem. -/
theorem restrictedEvaluation_isAdmissibleEpi
    (hs : ∀ i, Function.Surjective
      ((F.map i).coefficientMap fun k => t.projection i (s k)))
    (i : Fin c.size) (E : Domain K R) (hi : E.locus ⊆ (c.obj i).locus) :
    (restrictedEvaluation t s i E hi).IsAdmissibleEpi := by
  let e := restrictedPushoutEquiv t s i E hi
  have he : e.toBoundedAlgHom.IsAdmissibleEpi :=
    BoundedAlgHom.isAdmissibleEpi_of_bounded_section _ e.symm.toBoundedAlgHom
      (BoundedAlgHom.ext e.apply_symm_apply)
  have hright := AffinoidPushout.rightMap_isAdmissibleEpi (localEvaluation t s i)
    (sourceRestriction t s i E hi) (localEvaluation_isAdmissibleEpi t s hs i)
  have h := BoundedAlgHom.IsAdmissibleEpi.comp _ _ hright he
  exact (restrictedPushoutEquiv_right t s i E hi) ▸ h

/-- The further evaluation has exactly the closed extension of the global
kernel along the original weighted subdomain map. -/
theorem restrictedEvaluation_kernel_global
    (hs : ∀ i, Function.Surjective
      ((F.map i).coefficientMap fun k => t.projection i (s k)))
    (i : Fin c.size) (E : Domain K R) (hi : E.locus ⊆ (c.obj i).locus) :
    RingHom.ker (restrictedEvaluation t s i E hi).toAlgHom.toRingHom =
      (restrictedDomain t s E).baseMap.closedIdealMap (globalKernel t s) := by
  have hrestriction : (sourceRestriction t s i E hi).comp ((cover t s).map i).restriction =
      (restrictedDomain t s E).baseMap :=
    (Domain.pullbackRestriction (baseMap t s) (Domain.inclusionOfSubset E (c.obj i) hi)).comp_baseMap
  calc
    _ = (sourceRestriction t s i E hi).closedIdealMap (kernel t s i) :=
      kernel_restrictedEvaluation t s hs i E hi
    _ = (sourceRestriction t s i E hi).closedIdealMap
        (((cover t s).map i).restriction.closedIdealMap (globalKernel t s)) :=
      congrArg (sourceRestriction t s i E hi).closedIdealMap (globalKernel_local t s hs i).symm
    _ = ((sourceRestriction t s i E hi).comp ((cover t s).map i).restriction).closedIdealMap
        (globalKernel t s) := BoundedAlgHom.closedIdealMap_comp _ _ _
    _ = _ := congrArg (fun f => f.closedIdealMap (globalKernel t s)) hrestriction

/-- Over a full subdomain contained in a chosen original cover member, the
quotient pullback identifies with that member's original local base change. -/
def domainQuotientEquiv
    (hs : ∀ i, Function.Surjective
      ((F.map i).coefficientMap fun k => t.projection i (s k)))
    (i : Fin c.size) (E : Domain K R) (hi : E.locus ⊆ (c.obj i).locus) :
    BoundedAlgEquiv K (quotientDomain t s E).algebra (F.baseChange i E hi) :=
  ClosedQuotient.baseChangeEquivOfAdmissibleEpi (restrictedDomain t s E).baseMap (globalKernel t s)
    (restrictedEvaluation t s i E hi) (restrictedEvaluation_kernel_global t s hs i E hi)
    (restrictedEvaluation_isAdmissibleEpi t s hs i E hi)

theorem domainQuotientEquiv_right
    (hs : ∀ i, Function.Surjective
      ((F.map i).coefficientMap fun k => t.projection i (s k)))
    (i : Fin c.size) (E : Domain K R) (hi : E.locus ⊆ (c.obj i).locus) :
    (domainQuotientEquiv t s hs i E hi).toBoundedAlgHom.comp
      (Domain.pullbackMap (quotientMap t s) (restrictedDomain t s E)) =
        restrictedEvaluation t s i E hi :=
  ClosedQuotient.baseChangeEquivOfAdmissibleEpi_comp_rightMap _ _ _ _ _

/-- On every original weighted cover member the quotient is the entire
original local algebra, with its supplied norm. -/
def localQuotientComparison
    (hs : ∀ i, Function.Surjective
      ((F.map i).coefficientMap fun k => t.projection i (s k))) (i : Fin c.size) :
    BoundedAlgEquiv K
      (Domain.pullback (quotientMap t s) ((cover t s).obj i)).algebra (F.algebra i) :=
  ClosedQuotient.baseChangeEquivOfAdmissibleEpi ((cover t s).obj i).baseMap (globalKernel t s)
    (localEvaluation t s i) (globalKernel_local t s hs i).symm
    (localEvaluation_isAdmissibleEpi t s hs i)

theorem localQuotientComparison_right
    (hs : ∀ i, Function.Surjective
      ((F.map i).coefficientMap fun k => t.projection i (s k))) (i : Fin c.size) :
    (localQuotientComparison t s hs i).toBoundedAlgHom.comp
      (Domain.pullbackMap (quotientMap t s) ((cover t s).obj i)) =
        localEvaluation t s i := ClosedQuotient.baseChangeEquivOfAdmissibleEpi_comp_rightMap
          ((cover t s).obj i).baseMap (globalKernel t s) (localEvaluation t s i) _ _

end Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent.GeneratorEvaluation

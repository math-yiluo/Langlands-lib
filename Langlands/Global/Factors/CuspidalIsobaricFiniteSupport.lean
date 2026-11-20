import Langlands.Global.Factors.CuspidalSupportEveryPlaceStatement
import Langlands.Representation.Classification.IsobaricSumSubquotient
import Langlands.Representation.Unramified.SphericalIsobaricSum

/-! # Finite induced support of a cuspidal isobaric sum -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

universe u uQ

namespace Langlands.Global

open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation
  IrreducibleOperatorSubquotient)
open CompletionPadic (padicField)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

/-- The finite isobaric-sum witnesses in `Q` have induced support in the given
order and are spherical outside the union of the presentation exceptional sets. -/
theorem cuspidalIsobaricSum_finiteSupport {F : Type u} [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] {r k : ℕ} {m : Fin k → ℕ}
    (hm : ∑ i, (m i + 1) = r + 1) {T : ∀ i, CuspidalOperatorRealization F (m i)}
    {P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i)}
    {h : ∀ i, HasIrreducibleAdmissibleComponents (P i)}
    {Q : IrreducibleOperatorSubquotient F r} (hQ : Q.IsCuspidalIsobaricSum T P h) :
    IsFiniteInducedConstituent hm P h Q := by
  classical
  choose A hA using hQ.1
  let S := (Finset.univ : Finset (Fin k)).biUnion (fun i => (P i).exceptional)
  refine ⟨A, S, ?_, ?_, fun v => (hA v).2⟩
  · intro v
    exact (hA v).1.isSubquotient_normalizedProduct _ (Nat.succ_pos r)
      ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩
  · intro v hv
    refine Unramified.isSpherical_of_isIsobaricSum (padicField v) hm (hA v).1 ?_
    intro i
    have hvi : v ∉ (P i).exceptional := fun hi =>
      hv (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩)
    exact ((P i).hasSpectrum v hvi).1

end Langlands.Global

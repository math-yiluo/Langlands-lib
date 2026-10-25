import Langlands.Automorphic.CuspidalSpectralPresentation
import Langlands.Automorphic.Unramified.WeakInduction

/-!
# Weak automorphic induction of a Hecke character to a cuspidal class

Harris's weak automorphic induction (Definition 1.3(b), rank-one case) for actual
cuspidal classes: some actual spectral presentation of the class satisfies the
unramified matching condition `SpectralSystem.IsWeakInductionOf`.
No existence or uniqueness is asserted.
-/

noncomputable section

universe uE uE' uV

namespace Langlands.Unramified.SpectralSystem

open Langlands.Global

variable {E : Type uE} {E' : Type uE'} [Field E] [NumberField E] [Field E'] [NumberField E']
  [Algebra E E']

/-- Weak induction depends only on the Euler polynomials outside a finite set. -/
theorem IsWeakInductionOf.of_sameEulerPolynomials {n : ℕ}
    {s t : SpectralSystem (FinitePlace E) n} {χ : HeckeCharacter E'}
    (hs : s.IsWeakInductionOf χ) (hst : s.SameEulerPolynomials t) :
    t.IsWeakInductionOf χ := by
  refine ⟨hs.1, ?_⟩
  filter_upwards [hs.2, hst, s.exceptional.eventually_cofinite_notMem] with v hv hvst hvs
  intro hvt
  refine ⟨(hv hvs).1, fun ϖ hϖ => ?_⟩
  rw [← hvst hvs hvt]
  exact (hv hvs).2 ϖ hϖ

/-- Enlarging the exceptional set does not change weak induction. -/
theorem isWeakInductionOf_restrict_iff {n : ℕ} (s : SpectralSystem (FinitePlace E) n)
    (T : Finset (FinitePlace E)) (hT : s.exceptional ⊆ T) (χ : HeckeCharacter E') :
    (s.restrict T hT).IsWeakInductionOf χ ↔ s.IsWeakInductionOf χ :=
  ⟨fun h => h.of_sameEulerPolynomials (s.sameEulerPolynomials_restrict T hT).symm,
    fun h => h.of_sameEulerPolynomials (s.sameEulerPolynomials_restrict T hT)⟩

end Langlands.Unramified.SpectralSystem

namespace Langlands.Automorphic

open Langlands.Global Langlands.Unramified

variable {E : Type uE} {E' : Type uE'} [Field E] [NumberField E] [Field E'] [NumberField E']
  [Algebra E E'] [CompactSpace (AdeleQuotient E)]

namespace CuspidalOperatorRealization.IsoClass

variable {r : ℕ}

/-- Harris 1998 Definition 1.3(b) with `m = 1`: the cuspidal class `c` of rank `r + 1`
is a weak automorphic induction of the Hecke character `χ` of `E'` when an actual
spectral presentation of `c` has a system weakly induced from `χ`. -/
def IsWeakAutomorphicInductionOf (c : IsoClass E r) (χ : HeckeCharacter E') : Prop :=
  ∃ s : SpectralSystem (FinitePlace E) (r + 1),
    HasSpectralSystem.{uE, uV} c s ∧ s.IsWeakInductionOf χ

/-- The rank of a weak automorphic induction is the degree `[E' : E]`. -/
theorem IsWeakAutomorphicInductionOf.rank_eq {c : IsoClass E r} {χ : HeckeCharacter E'}
    (h : IsWeakAutomorphicInductionOf.{uE, uE', uV} c χ) :
    r + 1 = Module.finrank E E' := by
  obtain ⟨s, -, hs⟩ := h
  exact hs.1

/-- At any actual representative, weak automorphic induction is witnessed by a
presentation of that representative. -/
theorem isWeakAutomorphicInductionOf_iff (S : CuspidalOperatorRealization E r)
    (χ : HeckeCharacter E') :
    IsWeakAutomorphicInductionOf.{uE, uE', uV} S.isoClass χ ↔
      ∃ P : CuspidalSpectralPresentation.{uE, uV} S, P.spectralSystem.IsWeakInductionOf χ := by
  constructor
  · rintro ⟨s, hc, hs⟩
    obtain ⟨P, rfl⟩ := (hasSpectralSystem_iff S s).mp hc
    exact ⟨P, hs⟩
  · rintro ⟨P, hP⟩
    exact ⟨P.spectralSystem, (hasSpectralSystem_iff S _).mpr ⟨P, rfl⟩, hP⟩

/-- Any attached system with the same Euler polynomials almost everywhere as a
weakly induced one witnesses weak automorphic induction. -/
theorem isWeakAutomorphicInductionOf_of_hasSpectralSystem {c : IsoClass E r}
    {χ : HeckeCharacter E'} {s t : SpectralSystem (FinitePlace E) (r + 1)}
    (hc : HasSpectralSystem.{uE, uV} c t) (hs : s.IsWeakInductionOf χ)
    (hst : s.SameEulerPolynomials t) :
    IsWeakAutomorphicInductionOf.{uE, uE', uV} c χ :=
  ⟨t, hc, hs.of_sameEulerPolynomials hst⟩

end CuspidalOperatorRealization.IsoClass

namespace PositiveRankCuspidalClass

/-- The mixed-rank form of `IsoClass.IsWeakAutomorphicInductionOf`. -/
def IsWeakAutomorphicInductionOf (c : PositiveRankCuspidalClass E)
    (χ : HeckeCharacter E') : Prop :=
  CuspidalOperatorRealization.IsoClass.IsWeakAutomorphicInductionOf.{uE, uE', uV} c.2 χ

@[simp] theorem isWeakAutomorphicInductionOf_ofFixedRank {r : ℕ}
    (c : CuspidalOperatorRealization.IsoClass E r) (χ : HeckeCharacter E') :
    IsWeakAutomorphicInductionOf.{uE, uE', uV} (ofFixedRank c) χ ↔
      CuspidalOperatorRealization.IsoClass.IsWeakAutomorphicInductionOf.{uE, uE', uV} c χ :=
  Iff.rfl

/-- The rank of a weak automorphic induction is the degree `[E' : E]`. -/
theorem IsWeakAutomorphicInductionOf.rank_eq {c : PositiveRankCuspidalClass E}
    {χ : HeckeCharacter E'} (h : IsWeakAutomorphicInductionOf.{uE, uE', uV} c χ) :
    c.rank = Module.finrank E E' :=
  CuspidalOperatorRealization.IsoClass.IsWeakAutomorphicInductionOf.rank_eq h

end PositiveRankCuspidalClass

end Langlands.Automorphic

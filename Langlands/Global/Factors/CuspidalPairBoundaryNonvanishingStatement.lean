import Langlands.Global.Factors.CuspidalPairFactorData
import Langlands.Automorphic.AssociatedFactorStatement
import Mathlib.Analysis.Meromorphic.Order

/-!
# Nonvanishing of partial cuspidal pair L-functions on the line `Re s = 1`

Shahidi (1981), Theorem 5.2, for actual cuspidal realizations of `GL_(r+1)` and
`GL_(t+1)` over a number field with unitary central characters. The partial
L-function is the Euler product of the unramified pair factors over the finite places
outside a finite set `S` containing both exceptional sets, in the vocabulary of
`CuspidalPairFactorData`. See the paired Markdown for sources, normalizations and the
scope.
-/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

open NumberField CuspidalPairFunctionalEquation
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)
open Langlands.ClassField.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

namespace CuspidalPairBoundaryNonvanishing

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}

/-- The unramified pair Euler factor
`L(s, Π_v × Π'_v) = 1 / ∏_(i,j) (1 - a_i b_j q_v^(-s))` at a finite place `v ∉ S`,
from the supplied Satake spectra `a`, `b` of the two presentations. -/
def partialEulerFactor (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T') {S : Finset (FinitePlace F)}
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (v : {v : FinitePlace F // v ∉ S}) (s : ℂ) : ℂ :=
  ((pairEulerPolynomial (P.spectralSystem.eigenvalues v.1 fun h => v.2 (hP h))
      (P'.spectralSystem.eigenvalues v.1 fun h => v.2 (hP' h))).eval
    (RankinSelberg.spectralPoint (residueCardinality v.1) s))⁻¹

/-- `L` is the partial L-function `L^S(s, Π × Π') = ∏_(v ∉ S) L(s, Π_v × Π'_v)`: it is
meromorphic on `ℂ`, and on some right half-plane the Euler product over the finite
places outside `S` converges absolutely with value `L s`. -/
def IsPartialPairLFunction (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T') {S : Finset (FinitePlace F)}
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S) (L : ℂ → ℂ) : Prop :=
  MeromorphicOn L Set.univ ∧
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Summable (fun v => ‖partialEulerFactor P P' hP hP' v s - 1‖) ∧
        HasProd (fun v => partialEulerFactor P P' hP hP' v s) (L s)

end CuspidalPairBoundaryNonvanishing

open CuspidalPairBoundaryNonvanishing

/-- **Shahidi (1981), Theorem 5.2**, for actual cuspidal realizations.

For a number field `F`, actual cuspidal realizations `T`, `T'` of `GL_(r+1)`,
`GL_(t+1)` with unitary central characters, spectral presentations `P`, `P'` of them
and a finite set `S` of finite places containing both exceptional sets: the partial
L-function `L^S(s, Π × Π')` exists as a meromorphic function on `ℂ`, and every
meromorphic function represented by the partial Euler product has nonpositive order,
that is, no zero, at every point `1 + iy` with `y` real. -/
def CuspidalPairBoundaryNonvanishingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    HasUnitaryCentralCharacter T → HasUnitaryCentralCharacter T' →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (S : Finset (FinitePlace F)) (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S),
    (∃ L : ℂ → ℂ, IsPartialPairLFunction P P' hP hP' L) ∧
      ∀ L : ℂ → ℂ, IsPartialPairLFunction P P' hP hP' L →
        ∀ y : ℝ, meromorphicOrderAt L (1 + y * Complex.I) ≤ 0

end Langlands.Global

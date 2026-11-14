import Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingStatement
import Langlands.Automorphic.Contragredient

/-!
# Absolute convergence of partial cuspidal pair Euler products for `Re s > 1`

Jacquet–Shalika (1981), *On Euler products and the classification of automorphic
representations I*, Lemma (5.2) and Theorem (5.3), for actual cuspidal realizations of
`GL_(r+1)` and `GL_(t+1)` over a number field with unitary central characters. The partial
Euler product is that of `CuspidalPairBoundaryNonvanishing.partialEulerFactor`, over the
finite places outside a finite set `S` containing both exceptional sets.

* `CuspidalSelfPairContinuationStatement` (Lemma (5.2)): `L^S(s, π × π̃)` continues
  holomorphically to `Re s > 1`.
* `CuspidalPairAbsoluteConvergenceStatement` (Theorem (5.3), with the double series of its
  proof): for `Re s > 1` the double series of `log L^S(s, π × π')` and the Euler product
  converge absolutely, and the product is the exponential of the series, hence nonzero.
* `CuspidalPairAbsoluteConvergenceReductionStatement`: Lemma (5.2) implies Theorem (5.3),
  the route of the proof of Theorem (5.3).

See the paired Markdown for sources, normalizations and the scope.
-/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

open NumberField CuspidalPairFunctionalEquation CuspidalPairBoundaryNonvanishing
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)
open Langlands.ClassField.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

namespace CuspidalPairAbsoluteConvergence

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}

/-- The term `tr(A_v^k) tr(A'_v^k) q_v^(-ks) / k`, `k = n + 1`, of the double series
`∑_(v ∉ S) ∑_(k ≥ 1) tr(A_v^k) tr(A'_v^k) q_v^(-ks) / k` for `log L^S(s, Π × Π')`, where
`A_v`, `A'_v` are the Satake spectra of the two presentations at `v`. -/
def logEulerTerm (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T') {S : Finset (FinitePlace F)}
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (v : {v : FinitePlace F // v ∉ S}) (n : ℕ) (s : ℂ) : ℂ :=
  P.spectralSystem.powerTrace v.1 (fun h => v.2 (hP h)) (n + 1) *
      P'.spectralSystem.powerTrace v.1 (fun h => v.2 (hP' h)) (n + 1) *
      RankinSelberg.spectralPoint (residueCardinality v.1) s ^ (n + 1) /
    ((n : ℂ) + 1)

end CuspidalPairAbsoluteConvergence

open CuspidalPairAbsoluteConvergence

/-- **Jacquet–Shalika (1981), I, Lemma (5.2)**, for actual cuspidal realizations.

For a number field `F`, an actual cuspidal realization `T` of `GL_(r+1)` with unitary
central character, an actual cuspidal realization `Td` realizing its contragredient,
spectral presentations `P`, `Pd` of them and a finite set `S` of finite places containing
both exceptional sets: some function `L`, holomorphic on the half-plane `Re s > 1`, is the
value of the absolutely convergent partial Euler product `L^S(s, π × π̃)` on some right
half-plane. -/
def CuspidalSelfPairContinuationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T Td : CuspidalOperatorRealization F r),
    HasUnitaryCentralCharacter T → Td.realization.IsContragredientOf T.realization →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T)
    (Pd : CuspidalSpectralPresentation.{u, uQ} Td)
    (S : Finset (FinitePlace F)) (hP : P.exceptional ⊆ S) (hPd : Pd.exceptional ⊆ S),
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L {s : ℂ | 1 < s.re} ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        Summable (fun v => ‖partialEulerFactor P Pd hP hPd v s - 1‖) ∧
          HasProd (fun v => partialEulerFactor P Pd hP hPd v s) (L s)

/-- **Jacquet–Shalika (1981), I, Theorem (5.3)**, for actual cuspidal realizations, with the
double series of its proof.

For a number field `F`, actual cuspidal realizations `T`, `T'` of `GL_(r+1)`, `GL_(t+1)`
with unitary central characters, spectral presentations `P`, `P'` of them, a finite set `S`
of finite places containing both exceptional sets, and `s` with `1 < Re s`:

1. the double series `∑_(v ∉ S) ∑_(k ≥ 1) tr(A_v^k) tr(A'_v^k) q_v^(-ks) / k` converges
   absolutely;
2. the partial Euler product `L^S(s, π × π') = ∏_(v ∉ S) L(s, π_v × π'_v)` converges
   absolutely: `∑_(v ∉ S) ‖L(s, π_v × π'_v) - 1‖` converges;
3. the product converges unconditionally to the exponential of the sum of the double
   series; in particular `L^S(s, π × π') ≠ 0`. -/
def CuspidalPairAbsoluteConvergenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    HasUnitaryCentralCharacter T → HasUnitaryCentralCharacter T' →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (S : Finset (FinitePlace F)) (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (s : ℂ), 1 < s.re →
      Summable (fun x : {v : FinitePlace F // v ∉ S} × ℕ =>
          ‖logEulerTerm P P' hP hP' x.1 x.2 s‖) ∧
        Summable (fun v => ‖partialEulerFactor P P' hP hP' v s - 1‖) ∧
        HasProd (fun v => partialEulerFactor P P' hP hP' v s)
          (Complex.exp (∑' x : {v : FinitePlace F // v ∉ S} × ℕ,
            logEulerTerm P P' hP hP' x.1 x.2 s))

/-- The route of the proof of Jacquet–Shalika (1981), I, Theorem (5.3): Lemma (5.2) implies
Theorem (5.3), at the same universes. -/
def CuspidalPairAbsoluteConvergenceReductionStatement : Prop :=
  CuspidalSelfPairContinuationStatement.{u, uQ} →
    CuspidalPairAbsoluteConvergenceStatement.{u, uQ}

end Langlands.Global

import Langlands.Global.Factors.CuspidalPairEisensteinOpenCell
import Langlands.Global.RankinSelberg.PartialEulerProductConvergence
import Langlands.Global.RankinSelberg.UnequalAnalyticStatement

/-! # The local numerator of the open-cell integral of a cuspidal-pair Eisenstein series

One enlargement `S₀` of the omitted set works for every point `s₀` of the imaginary axis: at
`s₀` there is a section whose open-cell integral, multiplied by the partial Euler product
`L^(S₀)(1 + s, π × π')`, is on a right half-plane a meromorphic function regular and nonzero at
`s₀`. This is the local part of the proof of Shahidi (1981), Theorem 5.1, pp. 351–352: the
factorization into local Jacquet integrals, the unramified computation of Casselman–Shalika,
and the choice of local vectors with nonzero Jacquet integral at the omitted places. See the
paired Markdown. -/

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

open NumberField CuspidalPairBoundaryNonvanishing CuspidalPairEisenstein
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)
open RankinSelbergGlobal (IsStandardAdditiveCharacter partialEulerProduct)
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

/-- For actual cuspidal realizations `T`, `T'` with unitary central characters, spectral
presentations `P`, `P'`, a finite set `S` containing both exceptional sets and a standard
additive character `ψ`, there is one finite `S₀ ⊇ S` such that for every `s₀` with
`Re s₀ = 0` there are a section `φ` and a function `c`, meromorphic on `ℂ`, analytic and
nonzero at `s₀`, with `c s = L^(S₀)(1 + s, π × π') · openCellIntegral ψ φ s` on some right
half-plane. Here `L^(S₀)` is the value `partialEulerProduct` of the Euler product of the two
original presentations over the finite places outside `S₀`. -/
def CuspidalPairEisensteinLocalNumeratorStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    HasUnitaryCentralCharacter T → HasUnitaryCentralCharacter T' →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (S : Finset (FinitePlace F)) (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
  ∃ (S₀ : Finset (FinitePlace F)) (hS : S ⊆ S₀),
    ∀ s₀ : ℂ, s₀.re = 0 →
      ∃ φ, IsSection T T' φ ∧
        ∃ c : ℂ → ℂ, MeromorphicOn c Set.univ ∧ AnalyticAt ℂ c s₀ ∧ c s₀ ≠ 0 ∧
          ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
            c s = partialEulerProduct P P' (hP.trans hS) (hP'.trans hS) (1 + s) *
              openCellIntegral ψ φ s

end Langlands.Global

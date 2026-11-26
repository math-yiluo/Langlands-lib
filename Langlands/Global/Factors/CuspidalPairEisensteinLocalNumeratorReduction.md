# The local numerator from convergence, unramified factorization and the semilocal numerator

Module `Langlands.Global.Factors.CuspidalPairEisensteinLocalNumeratorReduction`.

## Content

- `CuspidalPairEisensteinLocalNumeratorReductionStatement.{u,uQ}`, in namespace
  `Langlands.Global`, is the proposition

  ```text
  CuspidalPairEisensteinOpenCellConvergenceStatement.{u} →
    CuspidalPairEisensteinUnramifiedFactorizationStatement.{u,uQ} →
      CuspidalPairEisensteinSemilocalNumeratorStatement.{u} →
        CuspidalPairEisensteinLocalNumeratorStatement.{u,uQ}
  ```

  The premises are stated in
  [CuspidalPairEisensteinOpenCellConvergenceStatement.md](CuspidalPairEisensteinOpenCellConvergenceStatement.md),
  [CuspidalPairEisensteinUnramifiedFactorizationStatement.md](CuspidalPairEisensteinUnramifiedFactorizationStatement.md)
  and
  [CuspidalPairEisensteinSemilocalNumeratorStatement.md](CuspidalPairEisensteinSemilocalNumeratorStatement.md);
  the conclusion is
  [CuspidalPairEisensteinLocalNumeratorStatement.md](CuspidalPairEisensteinLocalNumeratorStatement.md).
- `cuspidalPairEisensteinLocalNumeratorReduction` proves it.
- In namespace `Langlands.Global.CuspidalPairEisensteinLocalNumerator`:
  `unitaryCharacter ψ hψ`, the standard additive character `ψ : AddChar (Adeles F) ℂ` as a
  `HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)` (values in the unit circle by the
  norm clause of `IsStandardAdditiveCharacter`, continuous and nontrivial by its other
  clauses); `unitaryCharacter_complex`, `(unitaryCharacter ψ hψ).complex = ψ`; and
  `unitaryCharacter_diagonal`, triviality on `F`.

The module is a reduction: it does not prove any premise, and so it does not by itself prove
`CuspidalPairEisensteinLocalNumeratorStatement`.

## Proof

Fix the data of the target: `F`, `r`, `t`, `T`, `T'` with unitary central characters, `P`,
`P'`, `S` with `hP : P.exceptional ⊆ S`, `hP' : P'.exceptional ⊆ S`, and a standard `ψ`.

1. Put `ψ_u = unitaryCharacter ψ hψ`. It is trivial on `F`, so the Library theorem
   `CuspidalPairFunctionalEquation.exists_finiteAdditiveSupport` gives a finite set `S_ψ` of
   finite places with `FiniteAdditiveSupport ψ_u S_ψ`.
2. The Library theorem `Automorphic.cuspidalDualPresentationExistence`, applied to `T'`, to
   its contragredient realization `dualRealization T'` (which is a contragredient by
   `Automorphic.cuspidalContragredientExistence`) and to `P'`, gives a presentation `Pd` of
   `dualRealization T'` in the universe `uQ`.
3. Apply the semilocal numerator to `T`, `T'`, `ψ` and the finite set
   `S ∪ S_ψ ∪ Pd.exceptional`. It gives `S₀` containing this set. This `S₀` is the set of
   the target; `S ⊆ S₀`.
4. Let `Re s₀ = 0`. The semilocal numerator gives `φ` with `IsSection T T' φ`, built from
   cusp forms spherical outside `S₀`, and `c`, meromorphic on `ℂ`, analytic and nonzero at
   `s₀`, with `c s = I_(S₀)(φ, s)` for `σ_N < Re s`.
5. `FiniteAdditiveSupport ψ_u S₀` holds by monotonicity
   (`CuspidalPairFunctionalEquation.finiteAdditiveSupport_mono`), since `S_ψ ⊆ S₀`, and
   `Pd.exceptional ⊆ S₀`. Apply the unramified factorization to `P`, `P'`, `Pd`, `S₀` with
   the inclusions `hP.trans hS`, `hP'.trans hS`, to `ψ_u` and to `φ`; it gives `σ_U`.
   Apply the convergence statement to `ψ` and `φ`; it gives `σ_C`.
6. For `max(σ_N, σ_U, σ_C) < Re s`, the open-cell integrand of `ψ = ψ_u.complex` is
   integrable, so the unramified factorization gives
   `L^(S₀)(1 + s) · I(φ, s) = I_(S₀)(φ, s)`, where `I` is
   `openCellIntegral ψ_u.complex = openCellIntegral ψ`. Hence
   `c s = I_(S₀)(φ, s) = L^(S₀)(1 + s) · I(φ, s)`, which is the identity of the target with
   the same section `φ` and the same `c`.

## Provenance

The decomposition follows the proof of Shahidi (1981), Theorem 5.1, pp. 351–352
(`shahidi-1981-certain-l`): the coefficient of a factorizable section converges absolutely
and is `∏_(v ∈ S) W_v(e_v) · ∏_(v ∉ S) W_v(e_v)` for `Re s` large; for `v ∉ S` Shahidi
normalizes the spherical inducing vector `φ_v` so that the Levi Whittaker value is
`⁰W_v(e_v) = 1` (p. 352), and then the unramified product is
`∏_(v ∉ S) L(1 + s, π_v × π'_v)⁻¹` by Casselman–Shalika (1980), Theorem 5.4, and the
semilocal product continues by Propositions 3.1 and 3.2 and is made nonzero at a given
point by choosing the local section vectors `φ_v` at the places of `S` (p. 352). Here the semilocal product is the partial open-cell integral `I_(S₀)`, and the
order of choices (first `S₀`, then `s₀`, then the section) is that of the target statement.
The unramified factorization compares the integral `I` and the partial integral `I_(S₀)` of
the same section, so it does not depend on a normalization of the spherical data: scalar
multiples of the spherical components multiply both sides by the same constant.
The splitting into these three premises is internal.

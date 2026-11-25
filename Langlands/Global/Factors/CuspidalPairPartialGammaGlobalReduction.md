# Reduction of the partial gamma equation of cuspidal pairs to the global Rankin–Selberg theory

Module `Langlands.Global.Factors.CuspidalPairPartialGammaGlobalReduction`.

## 1. Content and provenance

The published statement `Langlands.Global.CuspidalPairPartialGammaEquationStatement.{u, uQ}`
(module [`CuspidalPairPartialGammaReduction`](CuspidalPairPartialGammaReduction.md), called
(G') there and here) is the partial functional equation of a pair of cuspidal realizations
`T`, `T'` of ranks `r + 1`, `t + 1`. It concerns `Λ = L_∞ · L^S` and
`Λd = L∨_∞ · L∨^S`, with the integral gamma factors of the actual local components at the
finite places of `S`. This module contains:

* the statement `Langlands.Global.CuspidalPairPartialGammaGlobalReductionStatement.{u, uQ}`:
  ten statements of the global Rankin–Selberg theory (Section 2) together imply (G');
* the theorem `Langlands.Global.cuspidalPairPartialGammaGlobalReduction`, which proves it;
* in the namespace `Langlands.Global.CuspidalPairPartialGammaGlobal`, the lemmas the proof uses
  and two auxiliary Prop-valued definitions, `UnequalPackageStatement` and
  `EqualPackageStatement` (Section 3). The module proves both of them from the premises.

The theorem is a reduction. It does not prove (G'). Section 5 says which of its ten premises
the Library proves.

**Source.** J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004)
(`cogdell-2004-analytic-theory-gln`; PDF page = printed page + 3), proof of Theorem 4.1,
printed pp.219–220 (PDF pp.222–223). For `m < n` it combines three identities:

* the global functional equation of the integrals, `I(s; φ, φ') = Ĩ(1 - s; φ̃, φ̃')`
  (Theorem 2.1, printed p.207);
* the Euler factorizations of both sides for suitable `φ`, `φ'` and `Re(s) ≫ 0`, obtained by
  unfolding (§2.2, printed pp.205–207) and the unramified computation (Theorem 3.3, printed
  p.215), with the places of `S` kept as local integrals;
* the local functional equations: Theorem 3.2, printed p.214, at the finite places of `S`, and
  Theorem 3.6, printed p.217, at the archimedean places.

The case `m = n` is "entirely analogous" (p.220). There the global functional equation is
Theorem 2.2, printed p.211, and the integrals involve a Schwartz–Bruhat function `Φ` and its
Fourier transform `Φ̂`. How (G') follows from this argument, with the local L-factors at `S`
kept and the signs `ω'_v(-1)^(n-1)` cancelled, is explained in §1 of
[`CuspidalPairPartialGammaReduction`](CuspidalPairPartialGammaReduction.md).

**Provenance (internal).** The split into ten premises is ours. The premises are the Library's
formal versions of these three identities, one set for `t < r` and one for `t = r`. Seven of
them are stated with the definition of the global Rankin–Selberg integrals. The other three
are ported together with this module:

* `EqualDualEulerFactorizationStatement` is the Euler factorization of the dual integral for
  `t = r`, the companion of `UnequalDualEulerFactorizationStatement`.
* `UnequalSemilocalEquationStatement` and `EqualSemilocalEquationStatement` are the product,
  over `S` and the infinite places, of the local functional equations. Each is stated for the
  partial Whittaker integrals of the Library. It uses the archimedean L- and ε-expressions of
  (G') and the gamma-factor hypothesis on `G` of (G'), copied unchanged.

The case `t > r` has no premises of its own: it is reduced to `t < r` by exchanging the two
realizations (Section 4).

## 2. The statement

`CuspidalPairPartialGammaGlobalReductionStatement.{u, uQ}` is the implication

```text
UnequalAnalyticStatement.{u} → UnequalUnfoldingStatement.{u} →
UnequalEulerFactorizationStatement.{u, uQ} → UnequalDualEulerFactorizationStatement.{u, uQ} →
UnequalSemilocalEquationStatement.{u, uQ} →
EqualAnalyticStatement.{u} → EqualUnfoldingStatement.{u} →
EqualEulerFactorizationStatement.{u, uQ} → EqualDualEulerFactorizationStatement.{u, uQ} →
EqualSemilocalEquationStatement.{u, uQ} →
CuspidalPairPartialGammaEquationStatement.{u, uQ}
```

All premises are in the namespace `Langlands.Global.RankinSelbergGlobal`, in modules
`Langlands.Global.RankinSelberg.<name>`. In summary (`W`, `W'` are the global Whittaker
functions of `x ∈ T.Space`, `x' ∈ T'.Space` for `ψ` and `ψ⁻¹`; a tilde denotes
`dualFunction`):

* [`UnequalAnalyticStatement`](../RankinSelberg/UnequalAnalyticStatement.md) (`t < r`): the
  global integral `I = unequalIntegral` is entire and bounded in vertical strips, and
  `I(s) = dualUnequalIntegral(1 - s)` (Cogdell Theorem 2.1).
* [`UnequalUnfoldingStatement`](../RankinSelberg/UnequalUnfoldingStatement.md): there is
  `C ≥ 0` such that `I(s)` is the Whittaker integral for `Re s > C`, and the dual integral at
  `1 - s` is the dual Whittaker integral for `Re s < -C`.
* [`UnequalEulerFactorizationStatement`](../RankinSelberg/UnequalEulerFactorizationStatement.md)
  and its dual
  [`UnequalDualEulerFactorizationStatement`](../RankinSelberg/UnequalDualEulerFactorizationStatement.md):
  for `x`, `x'` spherical outside `S` and `Re s` large, the Whittaker integral is
  `partialUnequalWhittakerIntegral S W W' s * p` with
  `HasProd (fun v => partialEulerFactor P P' hP hP' v s) p`; likewise on the dual side with
  `partialDualWhittakerIntegral` and the factors of `Pd`, `Pd'`.
* [`UnequalSemilocalEquationStatement`](../RankinSelberg/UnequalSemilocalEquationStatement.md):
  there are `x`, `x'` spherical outside `S`, `σ`, and `A`, `B` meromorphic on `ℂ` and
  nonzero off a discrete set, equal to the two partial Whittaker integrals for `Re s > σ`.
  For all `ψv`, `νv`, `G` as in (G'), off a discrete set,
  `infiniteL s * B (1 - s) = (∏_(v ∈ S) G_v(q_v^(-s))) * infiniteEpsilon s * dualInfiniteL (1 - s) * A s`.
* [`EqualAnalyticStatement`](../RankinSelberg/EqualAnalyticStatement.md) (`t = r`, central
  characters `ω`, `ω'`, Schwartz–Bruhat `Φ`): continuations `I`, `Idual` of `equalIntegral`
  and of the dual integral (with `Φ̂`), equal to them on a right half-plane. They are
  holomorphic outside `equalPoleSet (r + 1) (ω ω')`, respectively
  `equalPoleSet (r + 1) (ω ω')⁻¹`, with at most simple poles there, and
  `I(s) = Idual(1 - s)` outside the first pole set (Cogdell Theorem 2.2).
* [`EqualUnfoldingStatement`](../RankinSelberg/EqualUnfoldingStatement.md),
  [`EqualEulerFactorizationStatement`](../RankinSelberg/EqualEulerFactorizationStatement.md),
  [`EqualDualEulerFactorizationStatement`](../RankinSelberg/EqualDualEulerFactorizationStatement.md)
  and [`EqualSemilocalEquationStatement`](../RankinSelberg/EqualSemilocalEquationStatement.md):
  the equal-rank versions of the unfolding, the two Euler factorizations (also for `Φ` equal to
  `1_(O_v^n)` outside `S`) and the semi-local equation (with `partialEqualWhittakerIntegral`).

## 3. Auxiliary definitions and lemmas

Namespace `Langlands.Global.CuspidalPairPartialGammaGlobal`.

**Analytic helpers.**

* `eventually_codiscrete_one_sub`: a property that holds off a discrete set holds at `1 - s`
  off a discrete set. `s ↦ 1 - s` maps punctured neighbourhoods of `x` into punctured
  neighbourhoods of `1 - x` (`eventually_codiscrete_iff_forall_eventually_nhdsNE`).
* `meromorphicOn_univ_of_eventually_eq`: a function equal off a discrete set to a function
  meromorphic on `ℂ` is meromorphic on `ℂ` (`MeromorphicAt.congr`).
* `meromorphicOn_prod_inv_denominator`: a finite product of reciprocals of the entire
  denominators of `LocalFactor.ReciprocalEntire` factors is meromorphic on `ℂ`.
* `meromorphicOn_of_hasAtMostSimplePolesIn`: if `P` is finite and
  `HasAtMostSimplePolesIn f P`, then `f` is meromorphic on `ℂ`. Off `P`, `f` is analytic. At
  `x ∈ P`, `(z - x)^2 f(z)` is differentiable on a punctured neighbourhood. It tends to `0` at
  `x`, being bounded by `max C 0 · ‖z - x‖`. Hence it is analytic at `x`
  (`Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`), with order `2`
  in the definition of `MeromorphicAt`.
* `exists_patch` (patching): let `L`, `I`, `A` be meromorphic on `ℂ`, with `A ≠ 0` off a
  discrete set. Suppose that for `Re s > σ` there is `p` with `HasProd (f · s) p` and
  `I s = A s * p`. Then some `Λ`, meromorphic on `ℂ`, satisfies `Λ s = L s * p` for all
  `Re s > σ` and every value `p` of the product, and `Λ = L I / A` off a discrete set. The
  witness is `L s * ∏' v, f v s` for `Re s > σ` and `L s * I s / A s` elsewhere. It equals
  `L I / A` wherever `A s ≠ 0`, so it is meromorphic by the previous lemma.
* `exists_partialEquation` (the abstract partial equation): let `L`, `Ld`, `I`, `J`, `A`, `B`
  be meromorphic, with `A`, `B` nonzero off a discrete set and `I(s) = J(1 - s)` off a
  discrete set. Suppose `I = A ∏ f` and `J = B ∏ fd` hold for `Re s > σ` in the sense of
  `exists_patch`. Then `exists_patch` gives `Λ`, `Λd` with the product identities. If
  `L(s) B(1 - s) = c(s) Ld(1 - s) A(s)` off a discrete set, then
  `Λ(s) = c(s) Λd(1 - s)` off a discrete set. Indeed, there `Λ(s) = L(s) I(s)/A(s)`,
  `Λd(1 - s) = Ld(1 - s) J(1 - s)/B(1 - s)` and `I(s) = J(1 - s)` (`field_simp`,
  `linear_combination`).

**Symmetry of the pair factors** (used for `t > r`).

* `pairEulerPolynomial_comm`: `pairEulerPolynomial a b = pairEulerPolynomial b a`, by
  `Multiset.map_swap_product` and commutativity of multiplication. Hence
  `partialEulerFactor_comm`: `partialEulerFactor P P' hP hP' = partialEulerFactor P' P hP' hP`.
* Real places. `realPairBlocks xs ys` is the list of blocks `x.tensor y`. The tensor of two
  characters is commutative (`realCharacterData_mul_comm`). The tensor of a character and an
  induced block is the same on both sides. The tensor of `Ind(d)` and `Ind(e)` consists of
  `Ind(d e)` and `Ind(d ē)`, against `Ind(e d)` and `Ind(e d̄)`.
  `Ind(d ē)` and `Ind(e d̄)` have the same `|weight|` (`natAbs_weight_mul_conj`), the same
  exponent (`exponent_mul_conj`) and the same determinant character on `ℝˣ`
  (`character_mul_conj_realToComplex`). So they have the same L-factor
  (`lFactor_induced_mul_conj`) and the same ε-factor (`epsilon_induced_mul_conj`).
  `prod_map_realPairBlocks_comm` exchanges the double product (`prod_map_flatMap`,
  `prod_map_prod_map_comm`, `prod_map_tensor_comm`). This gives
  `realPairLFactor_denominator_comm` and `realPairEpsilon_comm`.
* Complex places. `complexPairBlocks xs ys` is the list of products `x.mul y`, which commute
  (`complexCharacterData_mul_comm`). This gives `prod_map_complexPairBlocks_comm`,
  `complexPairLFactor_denominator_comm` and `complexPairEpsilon_comm`.

**The pole set is finite.**

* `detPower_injective`: if `|det z|^(w₁) = |det z|^(w₂)` for all `z` in the adelic points of
  `GL_1`, then `w₁ = w₂`. Every positive real `e^L` is the norm of a scalar idele
  (`Automorphic.OperatorDeterminantSlice.exists_scalar_determinantNorm`). Hence
  `exp((w₁ - w₂) L) = 1` for all real `L`. Taking `L = 1` gives `w₁ - w₂ = 2πik` for an
  integer `k`, and `L = 1/(2k)` excludes `k ≠ 0`.
* `equalPoleSet_finite`: `equalPoleSet n χ` has at most two elements. If `χ = |·|^(w₀)` it is
  contained in `{-w₀/n, 1 - w₀/n}` by `detPower_injective`. Otherwise it is empty.

**The packages.**

* `isStandardAdditiveCharacter_complex`: for a unitary additive character `ψ` of the adeles
  that is trivial on `F`, `ψ.complex` is a standard additive character in the sense of the
  premises.
* `UnequalPackageStatement` (Prop-valued definition). It takes the binders and hypotheses of
  (G') with `t < r` (without `HasIrreducibleAdmissibleComponents` for `Pd`, `Pd'`), with the
  same `classical` elaboration and the same `let`-definitions of `infiniteL`, `dualInfiniteL`
  and `infiniteEpsilon`. It asserts: there are `σ` and `I J A B : ℂ → ℂ` meromorphic on `ℂ`,
  with `A`, `B` nonzero off a discrete set and `I(s) = J(1 - s)` off a discrete set, such that
  for `Re s > σ` there are values `p` of the products of
  `partialEulerFactor P P' hP hP' · s` with `I s = A s * p`, and of
  `partialEulerFactor Pd Pd' hPd hPd' · s` with `J s = B s * p`. Moreover the semi-local
  equation of `UnequalSemilocalEquationStatement` holds for all `ψv`, `νv`, `G` as in (G').
  It is the hypothesis list of `exists_partialEquation`, packaged; it is internal to this
  module.
* `unequalPackage`: the five unequal-rank premises imply `UnequalPackageStatement`. Take
  `x`, `x'`, `σS`, `A`, `B` from the semi-local premise. Take `I` to be the global integral of
  `x`, `x'`, entire by `UnequalAnalyticStatement`, and `J(u) = I(1 - u)`. Let
  `σ = max(C, σE, 1 + C, σD, σS)`, where `C` is the unfolding bound and `σE`, `σD` are the
  half-planes of the two Euler factorizations. For `Re s > σ`, unfolding and the Euler
  factorization give `I s = A s * p`. For `Re u > σ`, `Re(1 - u) < -C`, so
  `J(u) = I(1 - u)` equals the dual global integral at `u` (`UnequalAnalyticStatement`), which
  equals the dual Whittaker integral (dual unfolding) and then `B u * p` (dual Euler
  factorization).
* `EqualPackageStatement` and `equalPackage`: the same for `t = r`. The central characters
  `ω`, `ω'` of `T`, `T'` come from `OperatorRealization.existsUnique_hasCentralCharacter`. The
  semi-local premise also supplies `Φ`. `I` and `J = Idual` are the continuations of
  `EqualAnalyticStatement`. They are meromorphic by `meromorphicOn_of_hasAtMostSimplePolesIn`
  and `equalPoleSet_finite`, and `I(s) = J(1 - s)` holds off the finite set
  `equalPoleSet (r + 1) (ω ω')`. The bound is `σ = max(σ₀, 1 + C, σE, σD, σS)`, where `σ₀` is
  the half-plane on which `I`, `Idual` equal the integrals. On the dual side,
  `Idual u` is the dual integral for `Re u > σ₀`. That equals the dual Whittaker integral by
  dual unfolding, since `Re(1 - u) < -C`, and then `B u * p`.

## 4. The proof of the reduction

`cuspidalPairPartialGammaGlobalReduction` builds both packages from the ten premises and
introduces the binders of (G'). `infiniteL` and `dualInfiniteL` are meromorphic on `ℂ` by
`meromorphicOn_prod_inv_denominator`. It then splits by `lt_trichotomy t r`.

* `t < r`: apply `UnequalPackageStatement` to the data, and `exists_partialEquation` to its
  output. The witnesses of (G') are `σ`, `Λ`, `Λd`. Item 4 of (G') is the conclusion of
  `exists_partialEquation`, with
  `c(s) = (∏_(v ∈ S) G_v(q_v^(-s))) * infiniteEpsilon s` and the semi-local equation.
* `t = r`: the same, with `EqualPackageStatement` after `subst`.
* `t > r`: apply `UnequalPackageStatement` with the two realizations exchanged: `T'`, `Td'`,
  `P'`, `Pd'` of rank `t + 1` first, then `T`, `Td`, `P`, `Pd`, and correspondingly exchanged
  parameter lists. `partialEulerFactor_comm` turns its Euler factors into those of (G'). The
  package's gamma-factor hypothesis is `IsPadicSymmetricGammaFactor ρ'_v ρ_v (G v)`. By the
  definition of `IsPadicSymmetricGammaFactor` this is `IsPadicPairGammaFactor ρ'_v ρ_v (G v)`
  when `r ≤ t`, which is also what the hypothesis `IsPadicSymmetricGammaFactor ρ_v ρ'_v (G v)`
  of (G') means when `¬ t ≤ r`. The package's semi-local equation involves
  `realPairLFactor (dR' v) (dR v)`, `complexPairLFactor (dC' v) (dC v)`, their dual versions,
  `realPairEpsilon (dR' v) (dR v) …` and `complexPairEpsilon (dC' v) (dC v) …`. The symmetry
  lemmas of Section 3 rewrite it into the equation with the expressions of (G'), and
  `exists_partialEquation` concludes as before.

The witnesses `Λ`, `Λd` are produced by `exists_patch`. On `Re s > σ` they are
`infiniteL s * ∏' v, partialEulerFactor P P' hP hP' v s` and the dual product. Elsewhere they
are `infiniteL · I / A` and `dualInfiniteL · J / B`.

## 5. The retained premises

The proof uses no hypothesis other than the ten premises. An unconditional proof of (G') by
this route needs proofs of all ten. The Library proves the eight premises other than the two
semi-local equations: `UnequalAnalyticStatement` and `EqualAnalyticStatement`
(`unequalAnalyticStatement_proof`, `equalAnalyticStatement_proof`), `UnequalUnfoldingStatement`
and `EqualUnfoldingStatement` (`unequalUnfoldingStatement_proof`,
`equalUnfoldingStatement_proof`), `UnequalEulerFactorizationStatement` and
`EqualEulerFactorizationStatement` (`unequalEulerFactorization`, `equalEulerFactorization`),
and `UnequalDualEulerFactorizationStatement` and `EqualDualEulerFactorizationStatement`
(`unequalDualEulerFactorization`, `equalDualEulerFactorization`), each in the module
`Langlands.Global.RankinSelberg.<name>Proof` of its statement. `UnequalSemilocalEquationStatement`
is derived from a further premise in `Langlands.Global.RankinSelberg.UnequalSemilocalEquationReduction`.

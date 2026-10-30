# Multiplicativity of the factors of pairs

Author: Worker 11. This module, in namespace `Langlands.RankinSelberg`, states
Theorem (3.1) of Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg
convolutions*, Amer. J. Math. 105 (1983): the gamma factor of a pair is
multiplicative under parabolic induction in the second variable, and the
L-factor of the induced pair divides the product of the L-factors of the
blocks. The factors are the rank-symmetric relations
`IsPadicSymmetricGammaFactor` and `IsPadicSymmetricLPolynomial` of the module
`PadicPairFactors`. The induced representation is the published normalized
block induction `PadicField.canonicalNormalizedProductInduced` of
`Induction/BlockFactors`. The module defines `succBlockShape` and three
statements, none of them proved.

## Source

JPSS 1983 (printed page = PDF page + 365).

- **Section 1, printed pages 376-377.** `δ_G` is the module of `G`: if
  `d_r(g)` is a right Haar measure, then `δ^{-1}(g) d_r(g)` is a left Haar
  measure. For a closed subgroup `H` and a representation `σ` of `H`,
  `Ind(G, H; σ)` (display (8)) acts by right translation (display (10)) on
  functions `f` with values in the space of `σ` such that (display (9))
  `f(hg) = δ_H^{1/2}(h) δ_G^{-1/2}(h) σ(h) f(g)`. An `m`-tuple of smooth
  representations `σ_i` of the diagonal blocks defines the representation
  `g ↦ σ_1(g_1) ⊗ ⋯ ⊗ σ_m(g_m)` of the parabolic (display (11)), and
  `Ind(G, Q, σ_1, …, σ_m)` consists of all right-smooth functions satisfying
  (9). The character `θ_ψ` of `N_r` is `θ(n) = ∏_{i=1}^{r-1} ψ(n_{i,i+1})`.
- **(2.12), printed page 403.** For `r > t` the factors with the smaller rank
  first are defined by `L(s, σ × π) = L(s, π × σ)` and
  `ε(s, σ × π, ψ) = ε(s, π × σ, ψ)`.
- **(3.1), printed pages 404-405.** As in Section 2 the representations are of
  Whittaker type. Let `r, t ≥ 0`, `(t_1, …, t_p)` a partition of `t`, `π`
  (resp. `σ_i`) a representation of Whittaker type of `G_r` (resp. `G_{t_i}`),
  `Q` the *lower* standard parabolic subgroup of `G_t` of type
  `(t_1, …, t_p)`, and (display (1)) `σ = Ind(G_t, Q; σ_1, …, σ_p)`. By
  Proposition (2.3), `σ` is of Whittaker type if and only if each `σ_i` is.
  For `π`, `σ` of Whittaker type the factors `L(s, π × σ)` and
  `ε(s, π × σ, ψ)` are those of Theorem 2.7, and (display (2))
  `γ(s, π × σ, ψ) = ε(s, π × σ, ψ) L(1 - s, π^ι × σ^ι)/L(s, π × σ)`.
  **Theorem.** Let `π` and `σ` be representations of Whittaker type of `G_r`
  and `G_t`, with `σ` of the form (1). Then
  (i) `γ(s, π × σ, ψ) = ∏_{1 ≤ i ≤ p} γ(s, π × σ_i, ψ)`, and
  (ii) `L(s, π × σ) ∈ ∏_{1 ≤ i ≤ p} L(s, π × σ_i) ℂ[q^{-s}, q^{s}]`.
- **(3.2), printed page 405.** The proof occupies Sections 3 to 7, and the
  case `p = 2` implies the general case by induction on `p`.

## Definitions

Throughout, `F : PadicField p` carries its canonical topological data (residue
cardinality `q`, normalized absolute value), `ψ` is a
`UnitaryAdditiveCharacter` of `F`, and `ν` is in the published
`LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ`.

- `succBlockShape m h`, for `m : Fin k → ℕ` and `h : ∑ i, (m i + 1) = t + 1`,
  is the block shape of rank `t + 1` with `k` blocks of sizes `m i + 1`, in
  this order. Every block shape of rank `t + 1` with `k` blocks has this form.
- `GammaMultiplicativityStatement` (Theorem (3.1)(i)): for all `r`, `t`, `k`,
  `m`, `h`, every representation `π` of `GL_{r+1}(F)` (carrier in universe
  `uV`) and every family `σ i` of representations of `GL_{m i + 1}(F)`
  (carriers in universe `uW`) such that `π` and every `σ i` satisfy the
  published `IsOfWhittakerType` for `standardCharacter ψ`, there are rational
  functions `G i` with `IsPadicSymmetricGammaFactor F ψ ν.val π (σ i) (G i)`
  for every `i` and
  `IsPadicSymmetricGammaFactor F ψ ν.val π
  (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) (∏ i, G i)`.
- `LFactorMultiplicativityStatement` (Theorem (3.1)(ii)): under the same
  hypotheses there are polynomials `P` and `Pi i` with
  `IsPadicSymmetricLPolynomial F ψ ν.val π (induced) P`,
  `IsPadicSymmetricLPolynomial F ψ ν.val π (σ i) (Pi i)` for every `i`, and
  some polynomial `Q` and `e : ℕ` with `X ^ e * ∏ i, Pi i = Q * P`.
- `MultiplicativityStatement` is the conjunction of the two statements.

The symmetric relations are the published pair relations read with the larger
rank first: for `t ≤ r` the candidate is `π` with `ψ`-Whittaker functionals and
the test is the other representation with `ψ̄`-functionals; otherwise the roles
are exchanged. The gamma witness `G` is evaluated at `q^{-s}`; the L-witness `P`
has constant term `1` and `L(s) = 1/P(q^{-s})`.

## Interpretation

- **Ranks and partitions.** The ranks are `r + 1`, `t + 1` and the block sizes
  `m i + 1`, all positive; JPSS allow the value `0` in their notation, but the
  factors of Theorem 2.7 concern positive ranks, and the relations are
  only defined for these. The hypothesis `h` forces `k ≥ 1`. For `k = 1` the
  parabolic is all of `GL_{t+1}(F)` and the statements compare `σ 0` with its
  induction to itself.
- **Factor (ii).** With `X = q^{-s}`, `L(s, π × σ) = 1/P(X)` and
  `L(s, π × σ_i) = 1/P_i(X)`, membership in
  `∏ L(s, π × σ_i) ℂ[q^{-s}, q^{s}]` says `∏ P_i / P` is a Laurent
  polynomial `Q/X^e`, which is `X^e ∏ P_i = Q P`. The statement keeps this
  cleared form of the paper. With `A = ∏ P_i` it is equivalent to `P ∣ A` by
  two published proofs in `RankinSelberg/LaurentDivisibilityProof`.
  `reciprocalLaurentSpanClearing` shows, for nonzero `P` and `A`, that `1/P`
  lies in the Laurent span of `1/A` if and only if `X^e A = Q P` for some
  polynomial `Q` and `e : ℕ`. `normalizedReciprocalLaurentSpanDivisibility`
  shows, for `P.coeff 0 = 1` and `A ≠ 0`, that the same membership holds if
  and only if `P ∣ A`; its proof uses that `X` is coprime to `P`. The
  certified polynomials meet these conditions: `P` and every `Pi i` have
  constant coefficient `1` (`IsPadicSymmetricLPolynomial.coeff_zero`), so
  `∏ i, Pi i` has constant coefficient `1` and is nonzero. These algebraic
  criteria do not prove that the factors exist or that (ii) holds.
- **Parabolic.** JPSS induce from the lower standard parabolic `Q` of type
  `(t_1, …, t_p)`. The statements induce from the standard upper block
  parabolic. For a block shape `B`, the Library's normalized induction from
  the lower block parabolic is
  `T.normalizedOppositeParabolicInduced B (B.blockTensor σ)` of
  `Induction/OppositeParabolic`. Its normalizing character is the inverse of
  the upper half modulus, which is JPSS's `δ_Q^{1/2}`: the exponent of
  `|det m_i|` in `δ_Q` is `∑_{j<i} t_j - ∑_{j>i} t_j`, the negative of its
  exponent in the upper modulus of the same type. The published proof
  `glOppositeProductReversal` (`Induction/OppositeProductReversalProof`)
  compares the two inductions. For every supplied `T`, every block shape `B`
  and every family of smooth block representations `σ i`, it gives a
  representation equivalence `E` from this opposite induction to the upper
  induction `T.normalizedProductInduced B.reverse (fun i => σ i.rev)` of the
  reversed family. It satisfies
  `Induction.eval (E f) x = R (Induction.eval f (w * x))`, with
  `w = B.reverseMatrix F.Carrier` and
  `R = PiTensorProduct.reindex ℂ V Fin.revPerm`, and the corresponding
  inverse formula. Representations of Whittaker type are admissible, hence
  smooth, so it applies with `T = F.canonicalTopologicalData`, whose upper
  induction is `canonicalNormalizedProductInduced`. The statements quantify
  over all families, the product `∏ G_i` and the condition in (ii) do not
  depend on the order of the blocks, and the relations are invariant under
  equivalence (`IsPadicSymmetricGammaFactor.congr_equiv`,
  `IsPadicSymmetricLPolynomial.congr_equiv`). So the statement for all
  families is the paper's statement for all families. The reversal
  equivalence only compares induced representations. It does not prove
  multiplicativity, the existence of factors or Proposition (2.3).
- **Normalization.** JPSS's display (9) with `G = GL_t(F)` unimodular is
  `f(hg) = δ_Q^{1/2}(h) σ(h) f(g)`, and their module `δ_Q` is the standard
  modulus `|det Ad(m)|` on the Lie algebra of the unipotent radical (check with
  the Borel subgroup of `GL_2`: `δ(a, x; 0, d) = |a/d|`). The Library's
  normalized induction uses the square root of the published `leviModulus`
  `∏_{i<j} |det m_i|^{n_j} / |det m_j|^{n_i}`, the same modulus for the upper
  parabolic. Both act by right translation on right-smooth functions, and both
  induce the algebraic tensor product `σ_1 ⊗ ⋯ ⊗ σ_k` of display (11). The
  Library's function space consists of covariant functions fixed under right
  translation by some open subgroup (`Induction.SmoothFunctions`).
- **Whittaker type.** The hypotheses are JPSS's: `π` and each `σ_i` are of
  Whittaker type. The published `IsOfWhittakerType` is admissibility, finite
  generation and a one-dimensional space of functionals for the character,
  here `standardCharacter ψ`, which is `θ_ψ`. That the induced representation
  is of Whittaker type is Proposition (2.3); it is not a hypothesis and not
  proved in the Library. The relations pair `ψ`-functionals of the
  representation of larger rank with `ψ̄`-functionals of the other, as in
  JPSS. For representations of Whittaker type the `ψ̄`-functionals also form
  a line: `Whittaker.characterChangeFunctionalEquiv` at `a = -1`, together
  with `standardCharacter_scale_neg_one`, identifies the two functional
  spaces by a linear equivalence, preserving their dimension (JPSS §2.1,
  printed page 385). This transports the given one-dimensionality; it does
  not prove preservation of Whittaker type under induction.
- **Existence of factors.** The conclusions assert that all factors exist, as
  well as the identities: the nonvacuity parts of the relations (a compatible
  quotient measure, nonzero functionals and, for gamma, a nonzero integral) and
  the functional equations or ideal generators of JPSS Theorem 2.7, which JPSS
  prove for representations of Whittaker type. Compatible quotient measures
  already exist in every positive rank by `unipotent_compatibleMeasureExists`
  in `RankinSelberg/UnipotentQuotient` and the p-adic statement proof
  `quotientHaarExistence` in `RankinSelberg/QuotientHaarExistence`.
  The character equivalence above transports existing nonzero functionals.
  Induction preservation, the analytic inputs and multiplicativity itself
  remain separate proof obligations. Each relation has at most one solution
  (`IsPadicSymmetricGammaFactor.unique`,
  `IsPadicSymmetricLPolynomial.unique`), so (i) says that the gamma factor of
  `π` against the induced representation is the product of the gamma factors
  of the blocks.
- **Gamma factor.** The gamma relation of the published `GammaFactor` is the
  functional equation `Ψ(1 - s, W̃, W̃') = ζ^{n-1} γ Ψ(s, W, W')`, with `n`
  the larger rank and `ζ` the minus-one scalar of the coefficient model of the
  other representation (`ω(-1)`). By Theorem 2.7(iii) this determines JPSS's
  `γ = ε L(1 - s, π^ι × σ^ι)/L(s, π × σ)` of display (2). For `t > r` the
  paper's `γ(s, π × σ, ψ)` is formed from the factors of (2.12), so it equals the gamma factor of `(σ, π)`; this is the
  convention of `IsPadicSymmetricGammaFactor` (derived, see `PadicPairFactors`).
- **Measures.** The additive measure is the self-dual `ν.val`. The statements
  do not assert that it exists (the separate published `SelfDualMeasureExists`)
  and hold vacuously without it. Every compatible quotient measure is
  quantified in the relations.
- **Field.** `F` is a p-adic field (a finite extension of `Q_p`), not an
  arbitrary nonarchimedean local field: the canonical topological data and the
  self-dual measures are published only for `PadicField`.
- **Universes.** `π` lives in universe `uV`, the `σ i` in `uW`, and the induced
  representation on its function space in `max uF uW`. The relations are
  invariant under equivalences between universes, so fixed universes lose
  nothing for representations of countable dimension, though that reduction is
  not proved in the Library.
- **Not stated.** Proposition (2.13) and the remarks after the theorem are
  not part of this module.

## Lean checks

The module compiles with `lean_check` in environment `3b864ddf` with no errors
or warnings. `MultiplicativityStatement` was inspected: it returns `Prop`, has
universe parameters `uF uV uW`, and uses only `propext`, `Classical.choice` and
`Quot.sound`. There is no `sorry` and no new axiom.

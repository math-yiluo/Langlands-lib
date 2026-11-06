# Whittaker completeness against normalized products of supercuspidals

This module states a completeness property of Whittaker functions on
`GL_(n+1)(F)`, for `F` a p-adic field. It is the input to the graph argument
in Henniart's proof of the supercuspidal local converse theorem
(`SupercuspidalLocalConverseStatement`). The module contains two definitions,
one `rfl` lemma and one proposition definition. It proves nothing about the
proposition.

## Source

Henniart 1993 (`henniart-1993-epsilon-pairs`), printed page 342, Lemme 2.1.
Henniart attributes it to Jacquet–Shalika [JS, lemme 3.2] (see also JPSS
GL(3) II, lemme 3.5). In translation:

> Let `H` be a smooth complex function on `G_r` satisfying
> `H(ng) = ψ_r(n) H(g)` for `g ∈ G_r` and `n ∈ N_r`, and compactly supported
> modulo `N_r`. Suppose that for every irreducible admissible (generic)
> representation `τ` of `G_r` and every `W ∈ W(τ, ψ̄)`, the integral
> `∫_{N_r \ G_r} H(g) W(g) dg` vanishes. Then `H = 0`.

Here `N_r` is the upper unipotent subgroup and `ψ_r(n) = ψ(Σ n_(i,i+1))`.
`dg` is any `G_r`-invariant measure on `N_r \ G_r`.

## The Lean declarations

All declarations live in namespace `Langlands.RankinSelberg`.

- `whittakerProductIntegrand ψ H f` is the function `N g ↦ H(g) f(g)` on
  `LeftUnipotentQuotient n F = N_(n+1) \ GL_(n+1)(F)`. Here
  `H : WhittakerFunctions ψ n` (so `H(ug) = ψ_(n+1)(u) H(g)`, with Library
  character `standardCharacter ψ n`, the same as Henniart's `ψ_r`) and
  `f : InverseWhittakerFunctions ψ n` (so `f(ug) = ψ_(n+1)(u)⁻¹ f(g)`). The
  product is left `N`-invariant by `whittaker_product_invariant`, and it is
  descended along the quotient map. `whittakerProductIntegrand_mk` evaluates
  it on cosets.
- `IsCompactWhittakerTestFunction ψ n H` says that `H` is smooth and
  compactly supported modulo `N`, in two clauses:
  1. some open subgroup `K` of `GL_(n+1)(F)` satisfies `H(gk) = H(g)` for all
     `g` and all `k ∈ K`;
  2. some compact set `C` has the property that `H(g) ≠ 0` implies
     `g = u c` with `u ∈ N` and `c ∈ C`.

  Clause 1 is the usual definition of smoothness as uniform right invariance.
  Under clause 2 and left `(N, ψ)`-equivariance it is equivalent to local
  constancy.
- `SupercuspidalProductCompletenessStatement.{uF, uW}` is the proposition.
  It quantifies over every prime `p`, every p-adic field `F` in universe
  `uF` with its canonical topology, every unitary additive character `ψ`,
  and every `n`. It also takes Borel structures on `GL_(n+1)(F)`, `N_(n+1)`
  and the quotient, and a right-invariant `unipotentHaar F n`. It then
  quantifies over every quotient measure `μ` compatible with
  `generalLinearHaar F n` and `unipotentHaar F n` (`IsCompatible`: nonzero,
  regular, right invariant, and satisfying the Weil integration formula).
  These measure conventions are the ones used by the Library's gamma factor
  relation `IsUnequalRankGammaFactor`. The proposition says the following.
  Let `H` be a compact Whittaker test function for `ψ`, and suppose that
  `∫ whittakerProductIntegrand ψ H f dμ = 0` for:
  - every block shape `(m_1 + 1, …, m_k + 1)` of `n + 1`
    (`succBlockShape m h`);
  - every family of smooth, irreducible, supercuspidal representations
    `τ_i` of `GL_(m_i + 1)(F)` on complex vector spaces in universe `uW`;
  - every inverse-character Whittaker functional `ℓ'` on the normalized
    upper block induction `F.canonicalNormalizedProductInduced (succBlockShape m h) τ`;
  - every `f` in the coefficient model `{g ↦ ℓ'(Π(g) x)}` of `ℓ'`.

  Then `H = 0`.

## Relation to the source

The Lean proposition differs from Lemme 2.1 only in its family of test
representations. Henniart tests against the Whittaker models
`W(τ, ψ̄)` of irreducible generic `τ`. The Lean statement tests against the
coefficient models of all `ψ̄`-Whittaker functionals on normalized products
of supercuspidal representations. The graph argument of Henniart's proof
needs exactly these tests: the epsilon hypothesis together with gamma
multiplicativity gives equal gamma factors against exactly these
representations.

The Lean proposition follows from Lemme 2.1, as follows. An irreducible
generic `τ` embeds in some normalized product
`Π = Ind(ρ_1 ⊗ ⋯ ⊗ ρ_k)` of irreducible supercuspidals `ρ_i`, by Jacquet's
subrepresentation theorem (the cuspidal support). The functor
`V ↦ V_(N, ψ̄)` is exact (Bernstein–Zelevinsky). Hence the nonzero
`ψ̄`-functional `λ` of `τ` extends to a `ψ̄`-functional `λ'` on `Π`. Then
`W(τ, ψ̄) = {g ↦ λ(τ(g)v)}` is contained in the coefficient model of `λ'`.
So the Lean hypothesis implies Henniart's hypothesis. Irreducible smooth
representations of `GL_m(F)` have countable dimension, so they can be
realized on carriers in any universe `uW`. Zero functionals contribute
only zero test functions, and integrability is automatic because
`H · f` is locally constant with compact support on the quotient.

Two further conventions agree with the source. The quotient measure is any
compatible one, and every such measure is right invariant, matching "any
`G_r`-invariant measure". The vanishing of each integral does not depend on
the normalization of `μ`.

## Provenance

The statement is derived from Henniart 1993, Lemme 2.1, with the test family
changed as explained above. Worker 1718 wrote the module.

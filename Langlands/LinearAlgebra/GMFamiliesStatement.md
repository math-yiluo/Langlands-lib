# Statements of Arthur's lemmas on `(G, M)`-families

Module `Langlands.LinearAlgebra.GMFamiliesStatement`, namespace `Langlands.GMFamily`. Worker 128,
Task 5536, item 2. The objects are those of `Langlands.LinearAlgebra.GMFamilies` (see its
Markdown for the model: a Euclidean space `E = 𝔞_0` with a root set `R`, Levi spaces `a = 𝔞_M`,
and `λ = iΛ`). The module states four propositions and their conjunction. It proves none of them.

## Source

J. Arthur, *An introduction to the trace formula*, in the volume registered as
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura` (PDF page = printed page + 12), §17:
Lemma 17.1 (p.94), Lemma 17.4 with (17.8) (pp.97–98), Lemma 17.5 with (17.13) (pp.99–100) and
Lemma 17.6 with (17.14) (p.101). J. Arthur, *The invariant trace formula. I. Local theory*
(1988), registered as `arthur-1988-invariant-trace-formula-I` (PDF page = printed page − 322),
§7, printed pp.355–358: Proposition 7.1 (descent for special subspaces) and Corollary 7.4 (the
alternate splitting formula, with `c_M^{Q₁} d_M^{Q₂}`).

Each statement quantifies over a universe `u`, a finite-dimensional real inner product space
`E : Type u`, a root set `R` (`IsRootSet R`) and a Levi space `a` (`IsLeviSpace R a`), as in
Arthur's setting of a Levi subgroup `M` of `G`.

## Statements

- `SmoothExtensionStatement` (Lemma 17.1): for a `(G, M)`-family `c` (`IsFamily R a c`) there is
  a smooth `f : StrongDual ℝ a → ℂ` equal to `cM R a c` at every `Λ` where all `θ_P(iΛ)` are
  nonzero. These `Λ` are the complement of finitely many hyperplanes, so `f` is the smooth
  extension of `c_M`, unique by continuity.
- `SplittingFormulaStatement` (Lemma 17.4): for two families `c, d`,
  `(cd)_M(λ) = ∑_{Q ∈ 𝓕(M)} c_M^Q(λ) d'_Q(λ_Q)`, with `c_M^Q = cQM R a c Q`,
  `d'_Q = dPrime R a d Q` and `λ_Q = paramProj a (faceSpace R a Q) Λ`.
- `DescentFormulaStatement` (Lemma 17.5): see below.
- `AlternateSplittingFormulaStatement` (Lemma 17.6): for two families `c, d` and `ξ ∈ 𝔞_M^G` in
  general position (for every `L₁, L₂ ∈ 𝓛(M)` with `d_M^G(L₁, L₂) ≠ 0`, the points `ξᵢ ∈ 𝔞_{Lᵢ}^G`
  with `2ξ = ξ₁ − ξ₂` are regular in `𝔞_{Lᵢ}`),
  `(cd)_M(λ) = ∑_{L₁, L₂ ∈ 𝓛(M)} d_M^G(L₁, L₂) c_M^{Q₁}(λ) d_M^{Q₂}(λ)`, with
  `(Q₁, Q₂) = splittingSection R ξ L₁ L₂`.
- `GMFamilyStatement`: the conjunction.

### How the identities are stated

Lemmas 17.4–17.6 are identities of smooth functions on `i𝔞_M^*`: the functions `c_M^Q`, `d'_Q` and
`c_M` are the smooth extensions of their defining formulas (Lemmas 17.1 and 17.3). The statements
here assert that there is a finite set `E₀` of nonzero vectors of `a` such that the identity of
the defining formulas holds at every `Λ` with `Λ(e) ≠ 0` for all `e ∈ E₀`. Off finitely many
hyperplanes every term is given by its formula. Since the smooth extensions are continuous and the
complement of finitely many hyperplanes is dense, this is equivalent to Arthur's identities given
Lemmas 17.1 and 17.3 (Lemma 17.3 is not stated here). Arthur also records the values at `λ = 0`,
(17.8), (17.13) and (17.14); these are the values of the smooth extensions and are not stated
separately.

### Lemma 17.5

Arthur takes a Levi subgroup `M₁ ⊆ M` of `G` over an extension `k₁` of the field `k` of `M`. The
statement covers the case `k₁ = k`: `a₁ = 𝔞_{M₁}` and `a = 𝔞_M` are Levi spaces of the same root
set `R`, with `a ≤ a₁`, and `𝔞_G = centralSpace R`. For a `(G, M₁)`-family `c₁` and
`ξ ∈ 𝔞_{M₁}^M = a₁ ⊓ aᗮ` in general position (for every `L₁ ∈ 𝓛(M₁)` with `d_{M₁}^G(M, L₁) ≠ 0`, the
point of `(ξ + 𝔞_M^G) ∩ 𝔞_{L₁}^G` is regular in `𝔞_{L₁}`), it asserts
`c_M(λ) = ∑_{L₁ ∈ 𝓛(M₁)} d_{M₁}^G(M, L₁) c_{M₁}^{Q₁}(λ)` for the induced family
`inducedFamily R a a₁ c₁`, with `Q₁ = descentSection R a 𝔞_G ξ L₁` and `λ` extended to
`i𝔞_{M₁}^*` by `extendParam`. This is also Arthur 1988, Proposition 7.1 (printed p.357) for the
special subspace `b = 𝔞_M` of `𝔞_{M₁}`.

Arthur takes `ξ` small. The chambers `Q₁` depend only on the ray of `ξ` (the point of
`(ξ + 𝔞_M^G) ∩ 𝔞_{L₁}^G` is linear in `ξ`), so the statement is made for every `ξ` in general
position.

**The case `k₁ ⊋ k` is not stated.** There `𝔞_M ⊆ 𝔞_{M₁}` need not be a Levi space of the roots
of `G` over `k₁`, and the inclusion `i𝔞_M^* ⊆ i𝔞_{M₁}^*` is the inclusion of rational characters.
(It can be one: for split `G = SL₂` and `M` the diagonal torus, the Levi space `𝔞_M` is the same
full rank-one space over every extension; then the statement above applies.) A first version of
this unit modelled the general case by a subspace `b` whose projected roots form a root set and
by the orthogonal projection `𝔞_{M₁} → 𝔞_M`. Its reviewer showed that this does not give a general
interface for extensions: for `G = Res_{K/k} SL₂`, `M` the diagonal torus and `M₁ = M_K`, a
Weyl-invariant inner product on `𝔞_{M₁} = ℝ²` that is not invariant under `Gal(K/k)` sends the norm
character to a different functional on `𝔞_{M₁}`, and the induced family changes. Arthur's general
formulation (Arthur 1988, §7) uses special subspaces, defined by a condition on the root fibres
weighted by root multiplicities, which the present root-set model does not record. Stating the
extension case in general needs that data or the relative root systems of `G` over `k` and `k₁`;
it is left open.

## Qualifications

- The model is Euclidean and abstract; see the Markdown of `GMFamilies`.
- Lemma 17.5 is stated for Levi subgroups over the same field only (see above).
- The coefficient `d_M^G(L₁, L₂)` of Lemma 17.6 is the direct factor for
  `𝔞_M^{L₁} ⊕ 𝔞_M^{L₂} → 𝔞_M^G` with Euclidean measures, as in Arthur 1988, Corollary 7.4 (printed
  p.358), which is the source of the two-family summand `c_M^{Q₁} d_M^{Q₂}`. Arthur 2005, p.101,
  has two misprints in this lemma: the first display has `c` in both factors, and (17.14) repeats
  `Q₁`. The relation `d_{𝐌}^{𝐆}(M, 𝐋) = 2^{n/2} d_M^G(L₁, L₂)`, `n = dim 𝔞_M^G`, printed on p.101
  (and in the corresponding comparison of Arthur 1988, p.358) was not confirmed: with product
  Euclidean measures the ratio is `2^{−n/2}` if the antidiagonal carries its Euclidean measure, and
  `2^{−n}` with the quotient convention of Arthur 2005, p.100. See the normalization note under
  `dCoeff` in the Markdown of `GMFamilies`, with a rank-one check. The statement uses the direct
  coefficient and does not depend on this relation.

## Provenance

Source: Arthur 2005, Lemmas 17.1, 17.4, 17.5 (for `k₁ = k`), 17.6; Arthur 1988, §7,
Proposition 7.1 and Corollary 7.4. The hyperplane-complement form of the identities is a derived
formulation, explained above.

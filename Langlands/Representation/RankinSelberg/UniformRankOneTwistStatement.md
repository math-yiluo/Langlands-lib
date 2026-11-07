# Rank-one factors after highly ramified twists, uniformly in the level

Authors: Worker 1721 and Worker 1813.

`Langlands.RankinSelberg.UniformRankOneTwistStatement.{uF,uV}` states a
level-uniform consequence of Jacquet and Shalika, *A Lemma on Highly Ramified
ε-Factors*, Math. Ann. 271 (1985), 319–332 (JS85), Proposition (2.2).
The module defines this proposition and `HasPrincipalLevelVector`; it supplies
no proof of the proposition.

## Source and derived scope

The registered source is `jacquet-shalika-1985-ramified-factors`, SHA256
`0864a6633c3cf430f576f91eadd05a7f11d88eea1b47095943d3ea76f7c9946b`,
at `/home/taskhub/central-library/Jacquet-Shalika--A Lemma on Highly Ramified epsilon-Factors--1985.pdf`.
Printed page numbers equal one-based PDF page numbers plus 318.

In §1.1 (printed 319), JS85 fixes a nonarchimedean local field and an additive
character whose largest trivial ideal is its ring of integers `O`. It uses the
Godement–Jacquet standard factors
`L(s, π) = P(q^(-s))⁻¹` and `ε(s, π, ψ) = c q^(-fs)`.
Proposition (2.2) (printed 320) says that, for an irreducible admissible
representation of rank `N` with central character `ω` and characters
`χ₁, …, χ_N` whose product is `ω`, sufficiently ramified `χ` satisfy
`L(s, π ⊗ χ) = 1` and
`ε(s, π ⊗ χ, ψ) = ∏ᵢ ε(s, χᵢχ, ψ)`.

The explicit level-uniform quantifier is derived from the proof in
§§2.3–2.7 (printed 320–323), rather than quoted as the printed proposition.
Section 4.2 (printed 326) identifies the pair factors against a character
`σ` of `GL₁` with the standard factors of `π ⊗ σ`; in particular `σ = 1`
gives the standard factors themselves. This is the source comparison used
here to formulate the conclusion directly with the Library's JPSS relations.
The module does not assume supplied factors or define substitute
Godement–Jacquet factors.

## The principal-level predicate

`HasPrincipalLevelVector F π m` means
`Langlands.fixedVectors π (Conductor.principalLevelSubgroup F.Carrier r m) ≠ ⊥`,
using the valuation in `F.canonicalTopologicalData`. Thus some nonzero vector
is fixed by the actual principal congruence subgroup. For positive `m` this
is `1 + ϖ^m M_(r+1)(O)`. At `m = 0` the published subgroup is
`GL_(r+1)(O)`, including integrality of the inverse. No uniformizer is chosen
by this predicate: the subgroup is defined using a power of the maximal ideal.
This is principal congruence on the entire matrix, distinct from the
last-row subgroup used for newvectors.

## Quantifiers and conclusions

The proposition quantifies over every prime `p`, every `F : PadicField.{uF} p`
with its canonical structures, every `UnitaryAdditiveCharacter ψ`, and every
supplied `LocalFactor.PadicAbelian.SelfDualHaar` measure `ν` for `ψ`.
It assumes `additiveConductor ψ = 0`, the source's normalization that the
largest trivial ideal is `O`. For every `r m : ℕ` it asserts one `B : ℕ`.
The positive rank is `N = r + 1`, so rank one and level zero are included.
For these fixed field and character/measure data, `B` depends only on `N`
and `m`; it precedes and is independent of all representation carriers,
representations and twisting characters below.

The first conjunct ranges over every `V : Type uV` with its complex
vector-space structure and every actual representation `π` on `V`.
`Whittaker.IsGeneric ψ r π` includes irreducibility and admissibility and
requires a nonzero standard Whittaker functional. For every such `π` with
`HasPrincipalLevelVector F π m`, and every continuous quasicharacter `χ`
with `a = multiplicativeConductor χ ≥ B`, it asserts:

1. `IsPadicSymmetricLPolynomial` for the twisted pair against
   `rankOneCharacter 1`, with polynomial `1`, hence `L(s) = 1`;
2. an element `c : ℂˣ` with `IsPadicSymmetricEpsilonFactor` for that pair
   and parameter `(c, ((N * a : ℕ) : ℤ))`, hence `ε(s) = c q^(-N a s)`.

Here `q` is the canonical residue cardinality. The epsilon exponent is
the natural product `N * a` cast to an integer. A unit of `ℂ` means a
nonzero scalar; no absolute-value-one condition is imposed. The witness
`c` may depend on `π` and `χ`. Quasicharacters need not be unitary.
The twist is exactly
`Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π`,
whose action is `g ↦ χ(det g) π(g)`.

The second conjunct uses the same `B` and ranges over two such representations
on carriers `V₁ V₂ : Type uV`. The published
`SameGLCentralCharacter F π₁ π₂` requires one homomorphism `ω` to give the
scalar-matrix action on both. For every `χ` of conductor at least `B`, some
single `G : RationalFunctions` satisfies `IsPadicSymmetricGammaFactor`
for both twisted pairs against `rankOneCharacter 1`.
Both field and carrier universes are unrestricted and independent.
All three factor relations retain their published definitions, including
the compatible-measure conditions of the L-polynomial relation.

## Why the depth bound is uniform

For the supercuspidal calculation, §2.5 chooses a matrix coefficient `f`
with `f(1) ≠ 0` that is bi-invariant under a principal subgroup `K_i`.
A nonzero `K_m`-fixed vector permits such a coefficient at
`i = max 1 m`: average a dual functional over this compact subgroup and
pair it with the fixed vector. Thus the invariance depth can be fixed
before choosing the representation. In the Fourier calculation the
representation enters through this depth and its central character.
With `k = a` and `j = ⌈k/2⌉`, the depth requirement in §2.5 is that
`k - j` be at least `i`; Lemma (2.6) imposes additional rank-dependent
depth requirements. Sections 2.5–2.7 then give an epsilon monomial of
exponent `N a` whose coefficient depends on `χ`, `ω` and `N`, but no
further representation data.

For the general case, §§2.3 and 2.7 use multiplicativity under parabolic
induction. Retaining level-uniformity in this passage uses the standard
bounded-level observation: if an irreducible subquotient of a
supercuspidally induced representation has `K_m`-invariants, its
supercuspidal support blocks have principal-level invariants at that
level. Exactness of compact-open invariants over `ℂ`, Iwasawa
decomposition, and normality of `K_m` in the maximal integral compact
group give this observation. The block ranks are at most `N`; taking a
maximum of their depth bounds gives a bound depending only on `N,m`.
At level zero one can use `K_1` throughout.
This explains the derived uniform formulation; these arguments and their
JPSS comparison remain proof obligations for a subsequent proof task.

Finally, a representation with `K_m`-invariants has central character of
conductor at most `m`: scalar matrices from the corresponding unit
subgroup fix a nonzero vector. One may therefore use the source's
comparison characters `(ω, 1, …, 1)`, whose conductors are bounded by
the level, and enlarge `B` beyond this bound. Each `χᵢχ` then has conductor
`a`. The sum of their rank-one epsilon exponents is `N a`, explaining
the exponent required in the first conjunct without imposing a bound
depending on arbitrarily chosen comparison characters.
For two representations with the same `ω`, use this same tuple in the
product formula. Apply L-vanishing also to their smooth contragredients
and `χ⁻¹`, which retain the principal-level condition and conductor
bound. Both L-factors in
`γ(s) = ε(s) L(1-s, π̃ ⊗ χ⁻¹) / L(s, π ⊗ χ)`
are then trivial, giving the common gamma factor asserted in the
second conjunct.

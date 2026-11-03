# Finite sampling of the actual Hecke action

This is an internal construction from the published finite Schwartz expansion
and actual algebraic integrated action. It makes no additional literature claim.

`FiniteActionSamples G` records a finite size, points of the actual group, and
complex coefficients. `fixedLevelActionSamples μ K f hf` constructs this data
from a measure finite on compact sets, an open subgroup `K`, and a
Schwartz–Bruhat test function `f` invariant under right multiplication by `K`.
The choice is independent of the representation, its carrier universe, and its
vectors. The subgroup need not be compact and the measure need not be Haar.

The private auxiliary family consists of all right `K` invariant scalar
functions `a`, with no other regularity condition. The function-valued map
`g ↦ (a ↦ f(g) * a(g))` is constant on the open coset `gK`. Its support is
contained in the compact support of `f`. The published
`Langlands.HarmonicAnalysis.finiteSchwartzExpansion` therefore gives finite
Schwartz–Bruhat functions `φᵢ` and sample points `rᵢ` that reconstruct this whole
family simultaneously. The chosen weights are
`cᵢ = (∫ g, φᵢ(g) dμ) * f(rᵢ)`.

`fixedLevelActionSamples_integral` proves
`∫ g, f(g) * a(g) dμ = ∑ i, cᵢ * a(rᵢ)` for every right `K` invariant
scalar function. Each summand in the expansion is integrable because its
Schwartz factor is integrable under a measure finite on compact sets.
The proof uses the published Schwartz integrability lemma, the Bochner integral
of a finite sum, and extraction of a constant scalar factor.

`fixedLevelActionSamples_action` proves that for every smooth complex
representation `ρ` and every `K` fixed vector `v`,
`integratedAction μ ρ hρ f v = ∑ i, cᵢ • ρ(rᵢ)v`. For every algebraic linear
functional `L`, the function `a(g) = L(ρ(g)v)` is right `K` invariant by the
representation multiplication law and the fixed-vector property. The published
`Langlands.Hecke.integratedAction_dual` and the scalar integral identity prove
equality after applying `L`. Algebraic dual separation then proves vector
equality. No continuity of `L` and no topology, finite dimension, or admissibility
of the representation carrier is used. The group and carrier universes remain
independent.

The construction uses the existing `SchwartzBruhat`, `fixedVectors`, and
`integratedAction` objects. It introduces no surrogate action and assumes no
finite presentation of the action integrand. It is a supporting construction
for fixed-level induced-character calculations; it does not assert regularity
of a varying induced character or a same-Levi comparison.

# Anti-invariant distributions supported on finitely many orbits vanish

`Langlands.HarmonicAnalysis.Distribution.FiniteOrbitAntiInvariantVanishingStatement.{uG, uX}`
is the following unproved proposition. This module defines the proposition and
supplies no proof.

## Statement

Let `G : Type uG` be a group with a topology making it a nonarchimedean
topological group (Mathlib's `NonarchimedeanGroup`). Assume `G` is locally
compact and sigma-compact. Let `X : Type uX` be a Hausdorff, locally compact,
totally disconnected topological space with a jointly continuous action of `G`
(`ContinuousSMul G X`). The action need not be transitive.

Let `σ : X ≃ₜ X` be a homeomorphism, `Z ⊆ X` a set and `s` a finite set of
points of `X` (a `Finset X`). Assume:

1. `Z` is closed.
2. `Z` is the union of the `G`-orbits `MulAction.orbit G x` of the points
   `x ∈ s`.
3. For every `z ∈ Z`, both `σ z` and `σ⁻¹ z` lie in the orbit of `z`.

Let `D` be a distribution on `X` such that:

1. `D` is supported in `Z`: `D f = 0` for every test function `f` vanishing at
   every point of `Z`.
2. `(g •)_* D = D` for every `g : G`, where `g •` is `Homeomorph.smul g`.
3. `σ_* D = -D`.

Then `D = 0`. The universes of `G` and `X` are independent, and `s` may be
empty or contain points in the same orbit.

## Exact meaning of the imported objects

`Distribution X` is the Library's `Module.Dual ℂ (SchwartzBruhat X)`: all
complex linear functionals on the locally constant, compactly supported
complex functions on `X`, with no continuity requirement. For a homeomorphism
`e`, `pushforward e` satisfies `(e_* D)(f) = D(f ∘ e)`.

## Provenance

The registered original is Bernstein and Zelevinsky, *Representations of the
group GL(n,F), where F is a non-Archimedean local field (survey)* (1976),
`bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.

Theorem 6.9 (printed p.54) shows that, for a constructive action, the absence
of invariant distributions on every orbit implies their absence on the whole
space. Its proof shrinks the space to the support of a distribution and uses an
open invariant subset on which the action is regular. Theorem 6.10
(printed pp.54–55) and Theorem 6.13 (printed p.56) apply it to deduce
`σ`-invariance of invariant distributions.

The present proposition is an internal variant of this orbit-by-orbit step for
a closed invariant set made of finitely many orbits. It is designed for the
proof of `Langlands.GeneralLinearConjugationDistributionTransposeStatement`,
where `Z` will be a fiber of the characteristic-polynomial map. It differs
from the source in these ways:

- Constructiveness of the action is replaced by the hypothesis that `Z` is a
  finite union of orbits.
- The conclusion is the vanishing of anti-invariant distributions, the form
  used after replacing `T` by `T - σ_* T`.
- Each `σ` and `σ⁻¹` is only assumed to preserve the orbits contained in `Z`,
  matching condition d) of Theorem 6.13 on `Z`. No analogue of conditions b)
  or c) is assumed, because invariance of `D` is a hypothesis.

## Why the proposition is true

This sketch is a plan for the separate proof, not a claimed Lean theorem.
The closed set `Z` is locally compact and Hausdorff, and `G` acts on it with
finitely many orbits. The published `Langlands.Topology.FiniteOrbitOrdering`
orders these orbits so that the union of the first `k` of them is open in `Z`
for each `k`. Remove the orbits one at a time in this order; at each stage
the next orbit is open in the union of the remaining ones.

Suppose `D` is supported in a closed invariant union `Z'` of orbits, and let
`O ⊆ Z'` be an orbit open in `Z'`. The set `W = X \ (Z' \ O)` is open in `X`,
invariant under `G` and, by the orbit hypothesis, under `σ`. Its intersection
with `Z'` is `O`, and `O` is closed in `W`. By the extension of test functions
from a closed subset of an l-space (Bernstein–Zelevinsky, Proposition 1.8,
printed p.7), `D` defines an invariant, `σ`-anti-invariant distribution on the
locally compact Hausdorff orbit `O`. Then
`Langlands.HarmonicAnalysis.Distribution.HomogeneousAntiInvariantVanishingStatement`
shows that this distribution is zero. Hence `D` vanishes on test functions
supported in `W`, so `D` is supported in the smaller closed invariant set
`Z' \ O`. After finitely many steps `D` is supported in the empty set and is
zero.

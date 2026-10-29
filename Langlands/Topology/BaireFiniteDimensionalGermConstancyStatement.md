# Baire constancy for finite-dimensional function germs

`Langlands.Topology.BaireFiniteDimensionalGermConstancyStatement` is a closed
proposition definition in independent, unrestricted universes `uX` and `uY`.
This file states an internal generic helper and supplies no Lean proof.

The proposition quantifies over every type `X` and every nonempty Baire
topological space `Y`. No topology on `X` is required. It then quantifies over
every sequence `D : ℕ → Set X` with `Antitone D`: if `m ≤ n`, then
`D n ⊆ D m`. The sets may be empty and have no topological, support or
compactness restrictions.

Next it quantifies over every complex linear subspace
`V : Submodule ℂ (X → ℂ)` that is finite dimensional. For every natural number
`m`, restriction from `V` to the functions `D m → ℂ` must be injective.
Equivalently, two members of `V` agreeing on `D m` agree on all of `X`.
This is an algebraic condition on every restriction map; it does not assert
continuity, uniformity or local constancy of any parameterized map.

For every family `f : Y → X → ℂ` and assignment `v : Y → V`, the premises are:

- For each fixed `x : X`, the scalar function `y ↦ f y x` is locally constant
  on `Y`. No common neighborhood for all `x` is assumed.
- For each `y : Y`, there exists a natural number `m` such that for every
  `x ∈ D m`, `f y x = (v y : X → ℂ) x`. This index is chosen after `y`
  and may depend on it.

There is no continuity or local constancy premise on `v`. The conclusion is
the existence of a set `O ⊆ Y` that is open and nonempty and satisfies
`v y = v z` for every `y ∈ O` and every `z ∈ O`. Thus the assigned elements
of `V`, as functions on all of `X`, are constant throughout `O`.

The conclusion claims constancy on one nonempty open set. A Baire argument
provides interior for one member of a countable closed cover, and local
constancy then gives a suitable open subset of that interior. This mechanism
does not supply a single representative throughout `Y`. Global constancy
would also fail with singleton `X`, the full one-dimensional function space
`V = X → ℂ`, a two-point discrete `Y`, and a nonconstant assignment `v`,
taking `D m = X` for every `m` and `f y = v y`.

Zero dimension is allowed. In that case `V` has only the zero element, so
every assignment `v` is constant and `O = Set.univ` gives the conclusion
because `Y` is nonempty. The type `X` may also be empty; its function space
then has only one element and the same observation applies. No positive
dimension, nonempty `X` or nonempty `D m` has been added.

## Provenance and proof obligation

Worker 451 formalizes the generic interface supplied by Worker 454 for the
actual JPS coordinate-unit invariance proof, task
`97e96190-2043-4279-bd83-d5b3ec8911b4`. Worker 625 supplied the proposed
unformalized Baire argument. This helper is an internal derived formulation;
it is not a theorem explicitly stated by Jacquet, Piatetski-Shapiro and
Shalika. It does not itself identify a coordinate quotient or prove the
parent's coordinate-unit invariance statement.

A proposed proof uses injective restriction to express basis-coordinate
functionals on `V` as finite linear combinations of evaluations on `D m`.
Applied to `f y`, these expressions reconstruct a locally constant candidate
`v_m : Y → V`. The locus `C_m` where `f y` and `v_m y` agree on all of
`D m` is closed, as an intersection of equalizers of continuous scalar
functions. The pointwise eventual-equality premise makes the `C_m` cover
`Y`. On `C_m`, comparison with the given eventual index `k` on
`D (max m k)`, followed by restriction injectivity and antitonicity, gives
`v_m y = v y`. Baire yields nonempty interior for some `C_m`, and local
constancy of `v_m` at an interior point yields `O`. No assertion that the
`C_m` form an increasing sequence is needed.

This is a proof plan rather than an implemented proof. A separate proof
must establish exactly this closed proposition, including all degenerate
cases and the independent universes.

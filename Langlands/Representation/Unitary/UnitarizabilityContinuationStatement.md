# Continuation of unitarizability along a connected parameter set

Author: Worker 1023.

`Langlands.UnitarizabilityContinuationStatement.{uG,uV}` is a proposition
definition. It names the soft analytic step of the reducibility sketch in
Zelevinsky 1980, Proposition 1.11, proof, printed p.175 (PDF p.12): positivity of
the invariant Hermitian forms `B_s` propagates from `s = 0` to every parameter.
This module proves no theorem.

## Exact statement

The data are:

- a group `G : Type uG` with a topology making it a topological group
  (`IsTopologicalGroup G`);
- a complex vector space `V : Type uV`, with no norm, topology or
  finite-dimensionality assumption;
- a family `π : ℝ → Representation ℂ G V` of actual algebraic representations
  on this one carrier;
- a set of parameters `J : Set ℝ`, assumed preconnected (`IsPreconnected J`;
  for example an interval or a half-line);
- an open subgroup `K : OpenSubgroup G` whose underlying set is compact.

The hypotheses are:

1. The family is constant on `K` over `J`: `π s k = π t k` for all
   `s t ∈ J` and `k ∈ K`.
2. Every `π s` with `s ∈ J` is admissible in the Library sense (`IsAdmissible`:
   every vector is fixed by an open subgroup, and every open-subgroup fixed
   space is a finite complex module).
3. Every `π s` with `s ∈ J` is irreducible in Mathlib's sense
   (`Representation.IsIrreducible`: the lattice of subrepresentations is a
   simple order; in particular `V` is nonzero).
4. For every `s ∈ J` there is a nonzero sesquilinear form
   `b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ` (conjugate-linear in the first variable,
   complex-linear in the second) with `b (π s g v) (π s g w) = b v w` for all
   `g, v, w`. It need not be Hermitian or positive.
5. Weak continuity: for every `g : G`, `v : V` and every linear functional
   `ℓ : Module.Dual ℂ V`, the scalar function `s ↦ ℓ (π s g v)` is continuous
   on `J` (`ContinuousOn`).

The conclusion is: if `π s₀` is unitarizable for one `s₀ ∈ J`, then `π s` is
unitarizable for every `s ∈ J`. Unitarizability is the Library's
`IsUnitarizable` (existence of an `InvariantPositiveForm`: a positive definite
Hermitian form, conjugate-linear in the first variable, preserved by every
action operator). No chosen form or analytic dependence of forms is part of the
data; the conclusion asks only for existence at each parameter. The universes
`uG` and `uV` are independent.

## Provenance

This is an internal, derived formulation, not a transcription of a numbered
theorem. Zelevinsky 1980 (literature `zelevinsky-1980-induced-ii`), proof of
Proposition 1.11, printed p.175 (PDF p.12), realizes the family
`π_s = ν^{-s} ρ₀ × ν^{s} ρ₀` on one space by restriction to the maximal
compact subgroup, asserts existence and uniqueness up to scalar of invariant
Hermitian forms `B_s` with analytic dependence on `s` (citing his reference
[13], §4), takes `B_0` positive by unitarity of `π_0`, notes that all `B_s` are
nondegenerate by irreducibility, and concludes: "One can derive from these
facts that all `B_s` are positive hence all `π_s` are unitary." The present
proposition isolates that derivation for a general family. It replaces
analytic dependence of a chosen form by weak continuity of the action and
replaces the maximal compact subgroup by any compact open subgroup on which the
family is constant. Existence of a nonzero invariant form at each parameter is
a hypothesis; uniqueness and nondegeneracy are to be derived in the proof.
In the intended application `G = GL_{2k}(F)`, `J = (-∞, 0]`, and the family is
the common compact realization of `ν^s ρ₀ × ν^{-s} ρ₀`.

## Proposed proof route (not part of the statement)

For a compact open subgroup `K' ≤ K`, the fixed space `W = V^{K'}` is the same
finite-dimensional space for all `s ∈ J`, and the averaging projection
`P : V → W` over finite `K'`-orbits is independent of `s`. The operators
`P π_s(g) P` on `W` act irreducibly when `W ≠ 0`, every invariant form is
determined by its restriction to `W`, and a finite-dimensional Schur argument
shows that the space of `W`-forms with `β(P π_s(g) u, w) = β(u, P π_s(g⁻¹) w)`
is one-dimensional, its nonzero elements nondegenerate. Hence each `π_s` has a
nonzero invariant Hermitian form `h_s`, unique up to a real scalar. By
continuity of the finite matrices of `P π_s(g) P` and compactness of the unit
sphere of forms on `W`, the set of `s ∈ J` where `h_s` is definite on `W` is
open and closed in `J`, hence all of `J`. Consistency of signs over the
directed system of such `K'` gives a positive definite invariant form on `V`.
This paragraph describes an intended proof, not an assumption.

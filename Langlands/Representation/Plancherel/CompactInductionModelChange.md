# Actual changes between compact models of normalized induction

Author: Worker 200.

## Provenance and purpose

This is an internal construction from the published normalized compact-picture
equivalences, actual ambient actions, and polynomial fixed-vector machinery.
It claims no new translation of a numbered literature theorem. Its purpose is
to provide actual parameter-dependent changes of compact subgroup for later
continuation and scalar comparisons.

## Data and construction

Fix a locally compact nonarchimedean group `G`, actual subgroups `P`, `M`, `U`,
a semidirect decomposition `h` of `P` with Levi `M` and radical `U`, closed
`P` and `U`, and the displayed radical unimodularity premise. Choose compact
open subgroups `K₀` and `K₁` with separate actual factorizations `G = P Kᵢ`.
The projection of `h` is continuous. Let `ν` be any continuous positive
norm-character family and `A` a canonical complex `SmoothRep` of `M`.
The ambient-group, character-index and inducing-carrier universes are independent.

`unramifiedCompactModelEquiv` extends a section on `K₀` to the actual
positive-normalized unramified induction at `χ`, then restricts it to `K₁`.
Its type is an equivalence of the full `G` representations on the two compact
carriers. The action on each carrier is the published actual transported
ambient action. The transition may depend on `χ`.

`unramifiedCompactModelEquiv_apply` gives this extension/restriction formula.
`unramifiedCompactModelEquiv_eval` reads its value at `k₁` as the first model's
ambient extension evaluated at that point. With a supplied factorization
`k₁ = p k₀`, `unramifiedCompactModelEquiv_eval_factor` gives the value by the
actual twisted normalized inducing action of `p` on `f(k₀)`. There is no
assumed comparison map or factorization-independent scalar here.

`unramifiedCompactModelEquiv_restrict` states compatibility with direct
restriction of the same ambient induced section.
`unramifiedCompactModelEquiv_symm` identifies the inverse with the construction
with the subgroups exchanged; `unramifiedCompactModelEquiv_self` gives the
identity when both choices coincide.

## Polynomial transition and inverse

`unramifiedCompactModelEquiv_mem_compactFixed` starts with an open ambient
subgroup `H ≤ K₀` fixing a section. The actual extension is fixed by `H`;
restriction to `K₁` is therefore fixed by the subgroup `H ∩ K₁`, interpreted
as the comap of `H` to `K₁`. This uses the published fixed-vector equivalence
and the actual restriction/translation identity. No inclusion `H ≤ K₁` is
needed.

`unramifiedCompactModelEquiv_polynomial` proves the published
`IsPolynomialOperatorOn` predicate on every parameter subset `Ω`.
For each input section, smoothness gives one such `H ≤ K₀`, independent
of `χ`. The transferred sections lie in the same `H ∩ K₁` fixed subspace.
Each point evaluation is polynomial by the published ambient extension
evaluation formula. The finite compact quotient evaluation embedding then
gives polynomiality of the vector family in that fixed subspace; composing
with its inclusion gives the claimed operator predicate.

`unramifiedCompactModelEquiv_symm_polynomial` exchanges the two compact
subgroups to prove the same predicate for the inverse. Neither result assumes
admissibility, finite length, irreducibility or finite-dimensionality of `A`.
The predicate allows a finite regular expansion depending on each input; it
does not assert a global finite-dimensional endomorphism algebra.

## Actual ambient intertwiners

For a second displayed semidirect decomposition `h'` with the same `M`,
and both factorizations `G = P' Kᵢ`, the theorem
`compactIntertwiningOperator_modelChange` identifies the two compact
conjugations of any actual ambient intertwiner `J`. Transition of its source
commutes with transition of its output. The proof cancels the inverse
restriction/extension equivalences. It assumes no further naturality square.

## Scope

This construction compares compact models for fixed literal subgroup data,
normalization, norm characters and inducing object. The hypotheses are generic
and contain no characteristic or splitness restriction, but the result does
not construct them for every reductive rational-point group. It proves no
initial convergence or rational continuation of standard integrals, no
comparison of independent continuations or canonical scalars, no parabolic
or measure independence, and no source-normalized `j`, `mu`, positivity,
nonvanishing or Plancherel theorem. Those remain separate obligations.

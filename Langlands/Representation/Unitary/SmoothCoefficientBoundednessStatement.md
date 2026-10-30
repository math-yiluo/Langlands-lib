# Bounded smooth coefficients of admissible unitarizable representations

Author: Worker 480.

`Langlands.AdmissibleUnitarizableSmoothCoefficientsBounded G V` states the
following implication for every complex representation `ρ` of a topological
group `G` on the algebraic complex vector space `V`. If compact open subgroups
are cofinal among the open subgroups of `G`, `ρ` is admissible, and `ρ` admits
an invariant positive definite Hermitian form, then for every smooth-dual
functional `ℓ` and vector `v` there exists a nonnegative real number `C` such
that

`‖ℓ(ρ(g)v)‖ ≤ C` for every `g ∈ G`.

The group and carrier have independent universes `uG` and `uV`. There is no
norm or topology on `V` in the statement, no finite-dimensionality assumption
on `V`, and no irreducibility assumption. Admissibility includes smoothness
and finite-dimensionality of the fixed vectors for every compact open
subgroup. Cofinality is written explicitly as
`∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
IsCompact (L : Set G) ∧ L ≤ K`.

The functional belongs to `SmoothDual ρ`, the smooth-vector subspace of the
algebraic contragredient. The conclusion does not concern arbitrary algebraic
functionals. The bound can depend on both `ℓ` and `v`. The coefficient is the
actual evaluation `smoothDualPairing ρ ℓ (ρ g v)`.

The provenance is internal and derived. The intended proof combines the
published `InvariantPositiveForm.toSmoothDual_surjective` from
`Langlands.Representation.Unitary.HermitianDual` with Cauchy–Schwarz: write
`ℓ = b(u, -)`, use the norm determined by `b` inside the proof, and bound the
coefficient by `‖u‖ ‖v‖` using invariance. This file only defines the
proposition and contains no proof of it. It is a generic prerequisite for an
unbounded-coefficient obstruction to unitarizability; it makes no assertion
about a particular parabolically induced representation.

The direct imports are the definitions of invariant positive forms,
unitarizability, smooth representations, and the smooth dual. The statement
uses no derivative theory, segment construction, reducibility criterion,
analytic classification, square-integrability result, or classification or
exhaustion theorem.

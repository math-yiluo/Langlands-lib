# Cohomology of the actual horizontal full-group differential

This internal algebraic construction forms the kernel-image quotient of the
published actual horizontal full-group-equivariant coefficient differential.
Its namespace is `Langlands.Cohomology.Lie.Horizontal`.

The scalar field `K` has characteristic zero, `L` is a `K`-Lie algebra, `M`
is a coefficient Lie module, and `G` is a group. The field, Lie algebra,
coefficient module and group have independent universes. There is no dimension,
topology, connectedness or rank assumption.

## Inputs and the differential

The inputs are an actual submodule `H : Submodule K L`, representations
`σ : Representation K G L` and `ρ : Representation K G M`, and the following
compatibilities:

* `hσ`: `σ g [x,y] = [σ g x, σ g y]`.
* `hρ`: `ρ g [x,m] = [σ g x, ρ g m]`.
* `hι`: in every natural degree `q`, every horizontal full-group-equivariant
  cochain `f` satisfies
  `[y, f(x)] = sum_i f(update x i [y,x_i])` for all `y ∈ H`.

The final hypothesis is the explicit infinitesimal insertion identity used by
the published horizontal differential. It is not inferred from arbitrary
algebraic group equivariance. A concrete application must prove it; the
published actual automorphic construction already does so using compact
differentiation for its actual actions.

In degree `q`, the cochain module is exactly
`Langlands.HorizontalAlternating.submodule H σ ρ q`: alternating maps from
`L` into `M`, vanishing whenever any argument belongs to `H`, and equivariant
under every element of `G`. No stability or bracket-closure assumption on `H`
is imposed. No arbitrary cochain carrier or differential is supplied.

`differential q` abbreviates the published
`horizontalEquivariantDifferential H σ ρ hσ hρ q (hι q)`. Its underlying
cochain is the actual coefficient Chevalley–Eilenberg differential.
`differential_differential` proves that successive differentials give zero:
subtype extensionality reduces the claim to the already published
`Langlands.Cohomology.Lie.differential_differential` on the underlying
alternating map. Thus square zero is proved rather than assumed.

## Cycles and actual boundaries

`cycles q` is the kernel of this differential. `boundaries 0` is the
bottom submodule, while `boundaries (q + 1)` is the actual range of the
degree-`q` differential. The membership lemmas expose closedness, the zero
condition in degree zero, and actual differential preimages in successor
degree. Every natural degree is covered.

`boundaries_le_cycles q` proves boundary inclusion. The degree-zero case
uses the bottom submodule; a differential preimage and the proved square-zero
identity give the successor case.

`boundariesInCycles q` is the range of the actual `Submodule.inclusion`
from boundaries to cycles, using this inclusion proof.
`mem_boundariesInCycles` proves that a cycle belongs to this submodule exactly
when its underlying horizontal cochain belongs to `boundaries q`. No boundary
is added or lost by the subtype representation.

## Quotient and classes

`HorizontalCohomology q` is the Mathlib `K`-module quotient of `cycles q` by
`boundariesInCycles q`. Its parameters include the actual actions and the
three stated compatibility proofs. `cohomologyClass q` is the quotient
projection; `cohomologyClass_surjective` proves that every class has an actual
closed horizontal representative.

`cohomologyClass_eq_zero` identifies zero classes exactly with actual
boundaries. `cohomologyClass_eq_iff` identifies equality of classes exactly
with boundary membership of the difference of their underlying horizontal
cochains. Both follow from Mathlib's quotient criteria and the preceding
boundary membership lemma.

`coboundaryToCycles q` restricts the codomain of the same horizontal
differential to cycles, using square zero. Its value lemma identifies its
underlying horizontal cochain with that differential. The theorem
`cohomologyClass_coboundary` proves its class zero using the original cochain
as an explicit differential preimage.

## Provenance and scope

This is a source-free internal construction on the published
`HorizontalAlternating` submodule and `HorizontalDifferential`, with the
published actual coefficient square-zero proof and Mathlib kernels, ranges,
submodule inclusion and module quotients. No new external-literature
identification is asserted.

The construction retains the full acting group. It does not replace group
equivariance by Lie invariance, assume connectedness or assert any analytic
or sheaf comparison. Instantiation at actual automorphic actions, induced
finite adelic action and coefficient transport on the quotient, general
algebraic tensor coefficients and a cohomological infinity criterion remain
separate constructions. In particular no nonvanishing theorem is asserted.

Authorship: Worker 2.

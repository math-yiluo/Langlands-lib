# Recovering an admissible representation from its smooth realization

Author: Worker 386.

`Langlands.AdmissibleSmoothVectorRecovery.{uG,uV,uH}` is a proposition
definition for the smooth-vector comparison needed after constructing a unitary
completion. This module states the comparison; it proves no theorem and
constructs no completion.

## Exact scope

The group `G : Type uG` is an arbitrary topological group. Compact open
subgroups must be cofinal among its open subgroups, in the explicit sense

```lean
∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
  IsCompact (L : Set G) ∧ L ≤ K
```

The original carrier `V : Type uV` is an algebraic complex vector space.
Its actual representation `ρ : Representation ℂ G V` is admissible in the
published Library sense: every vector has an open stabilizer, and every
open-subgroup fixed space is a finite complex module. There is no norm,
topology or finite-dimensionality assumption on `V`. The input
`b : InvariantPositiveForm ρ` is an actual invariant positive definite
Hermitian form, conjugate-linear in its first variable and complex-linear
in its second.

The target `H : Type uH` is any complex normed inner-product space. Its
representation `σ : Representation ℂ G H` has continuous action operators:
`Continuous (σ g)` for every `g : G`. No completeness or continuity of
the group-variable orbit maps is required. The three universes are
independent, and zero carriers are allowed.

An actual intertwiner `j : ρ.IntertwiningMap σ` has dense range and satisfies
the exact pullback equation

```lean
∀ v w : V, inner ℂ (j v) (j w) = b.inner v w
```

Equivariance is part of this existing intertwiner type. Injectivity follows
from the displayed equation and definiteness of `b`; it is not an extra
premise. The conclusion is, for every `w : H`,

```lean
w ∈ smoothVectors σ ↔ ∃ v : V, j v = w
```

Here `smoothVectors` is the existing submodule of vectors fixed by some
open subgroup of the actual group. Thus the conclusion identifies its
elements with the actual image of `j`; it does not use differentiable or
Archimedean smooth vectors.

## Internal provenance and intended proof boundary

This is an internal comparison statement formulated from the published
`InvariantPositiveForm`, `IsAdmissible`, intertwiner and open-stabilizer
smooth-vector definitions. It is not a transcription of an external theorem.
Its single direct import, `Unitary.HermitianDual`, supplies these objects
and the already proved conjugate-linear Hermitian identification with
the smooth dual.

A later proof may first extend preservation of the inner product from the
dense image using continuity of each action operator. For a smooth vector
`w` of `H`, the functional `v ↦ inner ℂ w (j v)` then belongs to the
smooth dual of `ρ`. The published
`InvariantPositiveForm.toSmoothDual_surjective`, under the stated cofinality
and admissibility assumptions, represents it as `b.inner v₀` for a vector
`v₀ : V`. The exact pullback and density force `w = j v₀`.
Conversely, equivariance transports each open stabilizer from `V` to its
image. This paragraph describes a proposed proof route, not an implemented
proof or an additional assumption.

The generic inputs are intended to be supplied by an actual completion
construction in applications. This statement supplies no normed realization,
Hilbert completion, unitary restriction, coefficient embedding, closed
irreducibility comparison, or Whittaker functional. In particular it is
only a prerequisite of the intrinsic square-integrable genericity task.
No existing Library pair is modified.

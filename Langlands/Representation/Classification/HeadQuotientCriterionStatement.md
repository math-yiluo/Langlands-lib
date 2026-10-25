# Two irreducible quotients and a strong head

Author: Worker 16.

This module states an internal algebraic criterion for a strong irreducible
head. It defines propositions only; it does not formalize their proofs or
assert that every representation has an irreducible quotient.

## Setting and declarations

All declarations are in `Langlands.Classification`, with independent universe
parameters `uG` and `uV`. They quantify an arbitrary group `G : Type uG`.
Every representation is an actual complex representation on a carrier in
`Type uV`, with its actual `AddCommGroup` and `Module ℂ` instances quantified.
The source, individual quotient targets, and the two product factors share
this carrier universe. Their product also lies in `Type uV`. This is exactly
the universe convention of the published `HasIrreducibleHead` and
`IsIrreducibleHead`; no comparison with targets in other universes is asserted.

There are no finite-length, finite-dimensionality, smoothness, admissibility,
Jacquet, or topology hypotheses.

- `UnequalIrreducibleQuotientKernelsStatement.{uG,uV}` states that if
  `q₁ : ρ.IntertwiningMap π₁` and `q₂ : ρ.IntertwiningMap π₂` are surjective,
  both targets are irreducible, and
  `LinearMap.ker q₁.toLinearMap ≠ LinearMap.ker q₂.toLinearMap`, then
  `Function.Surjective (q₁.prod q₂)`. This is Mathlib's actual intertwiner
  from `ρ` to `π₁.prod π₂`, sending `v` to `(q₁ v, q₂ v)`.
- `IrreducibleHeadProductCriterionStatement.{uG,uV}` states, for every `ρ`,
  that `HasIrreducibleHead ρ` is equivalent to the conjunction of existence
  of a carrier, its additive/module instances, and a representation `π`
  satisfying `IsIrreducibleQuotient ρ π`, and absence of a surjective
  intertwiner `ρ → π₁.prod π₂` for every pair of irreducibles `π₁`, `π₂`.
  The absence clause quantifies every actual intertwiner into that product.
- `HeadQuotientCriterionStatement.{uG,uV}` is the conjunction of those two
  universally quantified propositions and is the aggregate target for a
  later proof.

The existence clause uses the published `IsIrreducibleQuotient`, so it requires
an actual surjective intertwiner onto a nonzero irreducible representation.
Neither clause assumes that `π₁` and `π₂` are nonisomorphic or distinct: they
may have the same carrier, instances, and action.

## Why kernels and repeated factors matter

The published `IsIrreducibleHead ρ π` requires an irreducible quotient map
onto `π` and equality of its kernel with the kernel of every irreducible
quotient map of `ρ`. `HasIrreducibleHead ρ` existentially quantifies such
a head in the source carrier universe. This is stronger than merely requiring
that all irreducible quotient targets be isomorphic.

For example, for an irreducible `π`, the product `π.prod π` has two projection
quotients with different kernels. Its identity map is a surjection onto a
product of two irreducibles. It therefore must be excluded by the criterion,
even though every irreducible quotient of this two-copy representation is
isomorphic to `π`. Restricting the test to nonisomorphic factors would lose
this multiplicity-two obstruction.

The existence conjunct is also necessary: absence of a two-factor quotient
alone holds for a representation with no irreducible quotient, including
the zero representation, and does not provide a head.

## Internal derivation rationale and scope

The following is the elementary mathematical rationale for these targets,
not a description of a completed Lean proof.

Given the two irreducible surjections, their kernels `K₁` and `K₂` are proper
maximal stable subspaces of the source. If they differ, neither contains the
other and their sum is the whole source. To lift `(w₁,w₂)`, first choose
`x` with `q₁ x = w₁`. Choose `z` with `q₂ z = w₂ - q₂ x` and write
`z = k₁ + k₂`, with `kᵢ ∈ Kᵢ`. Then `x + k₁` maps to `(w₁,w₂)`.
This gives the first target.

If a strong head exists and there were a surjection onto a product of two
irreducibles, its two projection composites would be irreducible quotient
maps. Their kernels would have to be equal. But a lift of `(w₁,0)` for a
nonzero `w₁` lies in the second kernel and not the first. Irreducibility
includes nonzeroness, so this is a contradiction. Conversely, choose an
irreducible quotient using the existence conjunct. If any other irreducible
quotient map had a different kernel, the first target would supply a
forbidden product quotient. Thus every irreducible quotient map has the same
kernel, exactly the published strong-head relation.

The provenance is this internal maximal-kernel/product-quotient argument
applied to the published
[`ConstituentRelations`](ConstituentRelations.md) and
[`CanonicalConstituents`](CanonicalConstituents.md) definitions. The actual
product representation and product intertwiner are Mathlib's
`Representation.prod` and `Representation.IntertwiningMap.prod`, from
`Mathlib.RepresentationTheory.Basic` and
`Mathlib.RepresentationTheory.Intertwining`. Irreducibility is Mathlib's
`Representation.IsIrreducible`, from
`Mathlib.RepresentationTheory.Irreducible`.

This criterion is not presented as a verbatim assertion from Silberger or
as an analytic or Langlands classification theorem. It uses no such theorem
to establish the prerequisite. No imported Library pair is changed. The
two asserted algebraic implications and their aggregate remain proof
obligations after this statement module is published.

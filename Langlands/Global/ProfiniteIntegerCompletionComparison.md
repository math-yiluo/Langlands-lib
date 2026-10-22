# Normalized comparison of the profinite-integer constructions

`Langlands.Global.ProfiniteIntegerCompletionComparison : Prop` states the
existence of a topological group equivalence from the additive group of the
published residue scalar ring to the published profinite completion of the
integer group. Its complete definition is:

```lean
∃ e : Multiplicative Langlands.Global.ProfiniteIntegerRing ≃*
    Langlands.Weil.ProfiniteIntegers,
  Continuous e ∧ Continuous e.symm ∧
    ∀ z : ℤ,
      e (Multiplicative.ofAdd
        (Langlands.Global.ProfiniteIntegerRing.intCastHom z)) =
        Langlands.Weil.frobenius (Multiplicative.ofAdd z)
```

There are no parameters or hypotheses outside this proposition. The file defines
the statement only; it neither proves it nor chooses an equivalence.

## Objects, topology, and normalization

The source `Langlands.Global.ProfiniteIntegerRing`, imported from
[`ProfiniteIntegerRing.lean`](ProfiniteIntegerRing.lean), is the subring of
families in `∏ n : ℕ+, ZMod (n : ℕ)` satisfying every divisibility reduction
equation. It retains the subspace topology from the product of the finite
discrete residue rings. Its `intCastHom` sends an integer to its family of
residue classes.

`Multiplicative` writes the source's addition as group multiplication: the
product of `ofAdd x` and `ofAdd y` is `ofAdd (x + y)`. Its topology is exactly
the source topology, via Mathlib's standard type-tag instance. The symbol `≃*`
therefore asks for an equivalence respecting addition in the scalar ring, not
its ring multiplication.

The target `Langlands.Weil.ProfiniteIntegers`, imported from
[`Langlands.Weil.Pullback`](../Weil/Pullback.lean), remains
`ProfiniteGrp.ProfiniteCompletion.completion
  (GrpCat.of Langlands.Weil.Degree)`, where `Degree := Multiplicative ℤ`.
Its profinite group topology is unchanged. The map `Langlands.Weil.frobenius`
is the canonical completion map, bundled as a continuous group homomorphism.
The two continuity clauses use precisely these existing topologies and make
the equivalence a homeomorphism as well as a group isomorphism.

For any witness `e`, preservation of the group identity gives
`e (Multiplicative.ofAdd (0 : ProfiniteIntegerRing)) = 1`.
The normalization at `z = 1` instead gives
`e (Multiplicative.ofAdd (1 : ProfiniteIntegerRing)) =
  Langlands.Weil.frobenius (Multiplicative.ofAdd (1 : ℤ))`.
Thus scalar additive zero corresponds to group identity, while scalar ring
one corresponds to the canonical integer-one Frobenius element. The ring unit
is not being identified with the group identity. Quantifying over all integers
also fixes the sign convention, rather than permitting inversion of the
canonical integer map.

## Internal provenance and Library correspondence

This is an internal comparison statement between two explicit Library
constructions of the profinite integers, motivated by finite quotients of
the integer group. It is not a verbatim theorem from Tate-module literature.
The source motivation for the residue scalar ring is documented in
[`ProfiniteIntegerRing.md`](ProfiniteIntegerRing.md); this statement adds the
precise compatibility requirement with the independently constructed group
completion.

The residue-side interfaces used here are `ProfiniteIntegerRing` and
`ProfiniteIntegerRing.intCastHom`. The group-side interfaces are
`Langlands.Weil.ProfiniteIntegers` and `Langlands.Weil.frobenius`.
The pinned Mathlib source
`Mathlib/Topology/Algebra/Category/ProfiniteGrp/Completion.lean`
defines the actual completion using finite-index normal quotients and proves
`ProfiniteGrp.ProfiniteCompletion.denseRange`. The published
[`Langlands.Weil.profiniteIntegerLifting`](../Weil/ProfiniteIntegerLiftingProof.lean)
provides a universe-polymorphic extension property for the same group and
canonical map. These are potential tools for the separate proof task; neither
is used as an assumption that the required comparison already exists.
Mathlib's topology on `Multiplicative` is defined in
`Mathlib/Topology/Constructions.lean`. These Mathlib references refer to the
project's pinned commit `5ed2965256430c3649e86755f9576b54eca72435`.

Only the two definition modules are imported. Neither object is replaced or
modified, and no ring structure on the Weil completion is asserted. There is
no comparison here with a product of p-adic rings, a prime-to-p completion,
or finite adeles. The existential proposition introduces no structure field,
axiom, proof hole, or assumed comparison.

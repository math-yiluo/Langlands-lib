# The central E₆ vertex over totally complex fields from the outer type A middle class

Module: `Langlands.GroupScheme.Rational.NumberFieldTypeE6NodeReduction`.

The module proves that two propositions together give
`NumberFieldTotallyComplexTypeE6DistinguishedVerticesStatement` (module
[`Rational.NumberFieldTypeE6QuadraticLeviReduction`](NumberFieldTypeE6QuadraticLeviReduction.md)):
over a totally complex number field, the vertices `α₂` and `α₄` of every actual Tits index
of a simply connected absolutely almost-simple group of type `E₆` are distinguished. The
two propositions are

- `NumberFieldTotallyComplexTypeE6BranchDistinguishedStatement` (module
  [`Rational.TypeE6BranchCocharacter`](TypeE6BranchCocharacter.md)): the short-arm vertex
  `α₂` is distinguished;
- `NumberFieldTotallyComplexOuterTypeAMiddleObstructionStatement` (module
  [`Rational.NumberFieldTotallyComplexOuterTypeAMiddleObstruction`](NumberFieldTotallyComplexOuterTypeAMiddleObstruction.md)):
  over a totally complex number field, an anisotropic simply connected absolutely
  almost-simple group of outer type `A_{2m+1}` has nonzero Tits obstruction at its middle
  fundamental weight.

This module proves neither proposition.

## Declarations

```lean
def NumberFieldTypeE6DistinguishedVerticesReductionStatement : Prop :=
  NumberFieldTotallyComplexTypeE6BranchDistinguishedStatement.{u} →
    NumberFieldTotallyComplexOuterTypeAMiddleObstructionStatement.{u} →
    NumberFieldTotallyComplexTypeE6DistinguishedVerticesStatement.{u}

theorem numberFieldTypeE6DistinguishedVerticesReduction :
    NumberFieldTypeE6DistinguishedVerticesReductionStatement.{u}
```

The vertices are numbered as in Mathlib's `CartanMatrix.E 6`: vertex `i` is Bourbaki's
`α_{i+1}`, so `α₂` and `α₄` are the vertices `1` and `3`. The private lemmas are:

- `absolutelyAlmostSimple_of_cartanConnected`: a simply connected group with actual Tits
  index data whose Cartan diagram is connected is absolutely almost simple. Over the
  separable closure the group is a product of almost-simple factors, each factor contains a
  simple vertex, and Cartan-connected vertices lie in the same factor
  (`geometricFactorIndex_eq_of_cartanConnected`); so there is one factor, and
  `separablyClosedAlmostSimpleAbsolute` with `IsAbsolutelyAlmostSimple.of_fieldExtension`
  concludes.
- `cartanConnected_of_typeA`: in an index numbered by `CartanMatrix.A (n + 1)`, every vertex
  is Cartan-connected to the vertex numbered `0`, by induction along the chain.
- `typeE6_nodeWeight_mem_rootSpan`: the integral fundamental weight at the central vertex `3`
  of a simply connected E₆ index is the sum of the simple roots with coefficients
  `(2, 3, 4, 6, 4, 2)`. Both sides have the same pairings with all simple coroots, which is a
  finite check against `CartanMatrix.E 6`. So the weight lies in the integral root span.
- `outerKernel_middle`: let the zero vertices of a simply connected E₆ index be the
  vertices `δ 0, …, δ n` of a chain of type `A_{n+1}` through the central vertex
  `δ mid = 3`, and let some Galois element exchange the two long arms. Then the actual
  anisotropic kernel `d.anisotropicKernelIndex.kernel` is absolutely almost simple. Its
  index is numbered by `CartanMatrix.A (n + 1)` through the vertex comparison of the kernel,
  some Galois element moves one of its vertices, and its integral fundamental weight at the
  kernel vertex of `3` has zero Tits obstruction. For the last claim, the ambient weight at `3`
  is fixed by the full star action and lies in the root span, so its obstruction vanishes
  (`titsObstruction_eq_zero_of_mem_rootSpan_unconditional`). The obstruction of the kernel at
  the restricted weight equals the ambient one
  (`TitsIndexData.AnisotropicKernelIndex.titsObstruction_eq`, module
  [`Reductive.SplitLeviTitsComparison`](../Reductive/SplitLeviTitsComparison.md)). The
  restriction of the fundamental weight at a zero vertex is the fundamental weight of the
  kernel at the corresponding vertex (`KernelComparison.weightRestriction_fundamentalWeight_zero`).

## Proof of the reduction

Let `K` be totally complex and let `G`, `d`, `e` be as in the target statement. The first
proposition gives that `α₂` (vertex `1`) is distinguished. Suppose `α₄` (vertex `3`) is not.
By `typeE6NodeMarking` (module
[`Rational.TypeE6NodeMarkingFromRoots`](TypeE6NodeMarkingFromRoots.md)), vertices `2` and `4`
are not distinguished, `0` and `5` are distinguished together, and if they are, some Galois
element exchanges the two long arms. Three cases remain.

1. *Vertices `0, 1, 5` distinguished* (Platonov–Rapinchuk (6.53)(c)). The zero vertices are
   the chain `2, 3, 4` of type `A₃`, and the arm exchange moves vertex `2` of the kernel.
   `outerKernel_middle` with `n = 2` and `mid = 1` makes the kernel an anisotropic, simply
   connected, absolutely almost-simple group of outer type `A₃` whose middle obstruction is
   zero. This contradicts the second proposition with `m = 1`.
2. *Only vertex `1` distinguished, trivial star action.* This is the index excluded over
   every field by `TitsIndexData.not_hasRankOneE6BranchIndex` (module
   [`SimplyConnected.LocalRankOneE6Exclusion`](../SimplyConnected/LocalRankOneE6Exclusion.md)):
   its kernel would be `SL_1` of a central division algebra of degree six, whose tensor cube
   is not split.
3. *Only vertex `1` distinguished, some Galois element moving a vertex* (Platonov–Rapinchuk
   (6.53)(a)). That element acts as the arm exchange. The zero vertices are the chain
   `0, 2, 3, 4, 5` of type `A₅`, and `outerKernel_middle` with `n = 4` and `mid = 2`
   contradicts the second proposition with `m = 2`.

## Source

Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994), registered as
`platonov-rapinchuk-1994-algebraic-groups-number-theory`, §6.8. For the inner forms, printed
pp. 382–383: of the isotropic indices (6.57), the one with circled `α₁, α₆` is excluded, and
(b) and (c) have `α₂` and `α₄` distinguished. For the outer forms, printed p. 385: "α₂ and α₄
must be distinguished vertices". The source proves the outer case with Theorem 6.20 and the
triviality of the cohomology of simply connected groups of type `²E₆` over totally
imaginary fields. The proof here instead uses the Tits obstruction: the central fundamental
weight lies in the root lattice, so its obstruction vanishes on the anisotropic kernel. The
nonvanishing for anisotropic outer type `A` over totally complex fields is the second
proposition. The reduction is a derived argument (provenance: derived).

# Rank and cardinality of actual geometric torsion

`Langlands.AbelianScheme.Tate.geometricTorsionRank` proves exactly the
published proposition `GeometricTorsionRankStatement.{u}`. For every scheme
`S`, actual `A : AbelianScheme S` with `A.HasRelativeDimension g`, positive
integer `n` invertible in `Γ(S, ⊤)`, algebraically closed field `Ω : Type u`,
and point `s : Spec Ω ⟶ S`, it gives

```text
Nonempty ((Fin (2 * g) → ZMod n) ≃ₗ[ZMod n]
  GroupScheme.Tate.Level A.toGrp (Over.mk s) n)
```

and the equality

```text
Nat.card (GroupScheme.Tate.Level A.toGrp (Over.mk s) n) = n ^ (2 * g).
```

The universe `u` is arbitrary. The theorem has no outer hypotheses beyond
those in the unchanged statement, and includes `n = 1` and `g = 0`.

## Implemented proof

The Lean term applies the published
`geometricTorsionRank_of_ample_and_cube` from
[`GeometricTorsionRankAssembly`](GeometricTorsionRankAssembly.md).
Its two premises are discharged by the unconditional published theorems
`Langlands.GroupScheme.algebraicallyClosedFieldAmpleExistence` and
`Langlands.GroupScheme.fieldCubePullback`, imported from their respective
proof modules.

The ample-existence theorem supplies an actual ample line bundle on the
abelian scheme over an algebraically closed field. It obtains that bundle
by pulling the ample degree-one twisting bundle back along an actual
closed immersion into projective space. The cube theorem supplies the
balanced identity for actual line-bundle pullbacks.

The reused assembly first proves the field torsion cardinality statement.
The published
`Langlands.AbelianScheme.finrank_multiplication_eq_of_ne_zero`
symmetrizes the ample bundle, uses the cube theorem to compute its
multiplication pullback, and applies the polarized finite-flat rank
theorem. This computes the native rank of actual multiplication by `n`
as `n ^ (2 * g)`. The published
`natCard_level_eq_multiplicationFinrank_at_unit` identifies the cardinality
of actual torsion with that rank at the unit point. Composing the two
equalities gives the field count.

The assembly then applies
`geometricTorsionRank_of_fieldTorsionCardinality` from
[`GeometricTorsionReduction`](GeometricTorsionReduction.md). That reduction
uses the count for every positive divisor of `n` and finite abelian group
classification to construct field torsion coordinates. It pulls the
actual abelian scheme back along `s`, preserves the specified smooth
relative dimension, and transfers the base unit condition to a nonzero
element of `Ω`. Its additive comparisons of actual torsion preserve the
already installed residue actions by `ZMod.map_smul`, giving the displayed
linear equivalence. Counting its finite source gives the asserted
cardinality.

## Provenance and scope

This module is a derived composition of the named Library theorems. It
introduces no new assertion from external literature. The source
correspondence for the target and the multiplication-degree and
divisor-count arguments is recorded in
[`GeometricTorsionRankStatement`](GeometricTorsionRankStatement.md) and the
companions of the imported results.

The conclusion concerns the existing `GroupScheme.Tate.Level`, the
additive group of actual sections killed by multiplication by `n`, with
its existing integer-induced `ZMod n` action. Both geometric premises of
the conditional assembly are proved here by imported unconditional
theorems. No rank, degree, basis, replacement module or field-fibre
equivalence is supplied as a premise.

The result asserts existence of coordinates and their cardinality; it
chooses no compatible bases across levels or points. Inverse-limit
freeness, adelic comparisons and monodromy-equivariant trivializations
are outside this statement.

Worker 2969 wrote this final composition and explanation. The imported
modules retain the mathematical constructions and their authorship.

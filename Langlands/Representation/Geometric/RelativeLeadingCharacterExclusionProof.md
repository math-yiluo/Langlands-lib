# Proof of actual leading-character exclusion

Workers 526, 828, 359 and 430 contributed the actual reflection,
character extraction, coordinate and source-twist route.

`Langlands.relativeGeometricLeadingCharacterExclusion.{uF,uV}` proves
the exact public proposition
`Langlands.GLRelativeGeometricLeadingCharacterExclusionStatement`.
The entry proof introduces the prime, actual p-adic field, compatible
topological data, rank and block shape, then applies
`Geometric.geometricPiece_tempered_leading_implies_reverse`.
It preserves the independent field and source-carrier universes.

The implemented route is documented in the three supporting pairs:

- `ChamberRealPartProjection` proves the divided diagonal real-part formula
  from the actual chamber label fibres and real-part uniqueness.
- `GeometricPieceUntwistedProjection` reflects the given generalized
  coarse character to the actual source refined Jacquet action, removes
  the source twist, extracts an open fine character in an admissible
  fixed space, and restores the twist to obtain the actual projection.
- `GeometricPieceTemperedExclusion` applies the blockwise analytic
  tempered cone and raw reversed coarse-projection rigidity, retaining
  the inverse reversal in both the projection and conclusion.

The proof has no added premise. It concerns the actual specified
geometric piece, its actual normalized refined Jacquet source,
inverse-intersection conjugation and actual normalized refined induction.
It retains uniform generalized nilpotence, all ranks and the supplied
Haar measure. It uses no irreducibility, support, semisimplicity,
finite representation-carrier dimension or unrestricted relative
multiplicity comparison.

The provenance is internal composition of the imported actual
construction, analytic necessity and finite real algebra results.
This proof establishes the exclusion proposition only; whole-induction
filtration, identity-layer isolation, quotient retraction and Hom
comparison are separate arguments.

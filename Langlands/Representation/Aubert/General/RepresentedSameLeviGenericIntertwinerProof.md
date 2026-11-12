# Generic nonzero morphisms between represented inductions sharing a Levi

`representedSameLeviGenericNonzeroIntertwiner` proves
`RepresentedSameLeviGenericNonzeroIntertwinerStatement.{u, v}`
(module `Aubert.General.RepresentedSameLeviGenericIntertwinerStatement`). Take actual
represented parabolics `P = MN` and `Q = MU` of a connected reductive group `G` over a
nonarchimedean local field, with the same Levi scheme `M`, and an irreducible admissible
smooth complex representation `σ` of `M(F)`. Then there is a nonzero polynomial in the
published unramified coordinates of `M` such that for every unramified character `ψ` in
its principal open, some morphism `i_P^G(σψ) ⟶ i_Q^G(σψ)` is nonzero.

The route is Renard, *Représentations des groupes réductifs p-adiques*, VII.3: generic
`PQ`-regularity followed by the algebraic intertwiner of VII.3.4. No analytic continuation
of intertwining integrals is used.

## Proof

1. `splitComponentStatement` gives a split component `a : A → M` of the connected
   reductive Levi `M`.
2. `exists_generic_isPQRegular` (module `Aubert.General.RepresentedSameLeviGenericRegularity`)
   gives a nonzero polynomial `poly` such that `σψ` is `PQ`-regular for `a` for every
   `ψ` in the principal open of `poly`.
3. Fix such a `ψ`. The twist `σψ` is irreducible by `SmoothRep.isIrreducible_twist_iff`.
   It is therefore nontrivial, because a simple module over `ℂ[M(F)]` is nontrivial
   (`IsSimpleModule.nontrivial`).
4. `exists_ne_zero_of_isPQRegular` (module `Aubert.General.RepresentedSameLeviRegularIntertwiner`)
   turns `PQ`-regularity of the nontrivial `σψ` into a nonzero morphism
   `i_P^G(σψ) ⟶ i_Q^G(σψ)`.

## Dependencies

The proof uses the following helper modules, which are new with this proof:

- `Aubert.General.RepresentedSameLeviGenericRegularity`: generic regularity.
- `Aubert.General.RepresentedSameLeviRegularIntertwiner`: the nonzero intertwiner from
  regularity.
- `Aubert.General.SameLeviPieceDisplacementStatement` and
  `Aubert.General.SameLeviPieceDisplacementProof`: strict displacement on non-identity
  pieces.
- `LanglandsClassification.SimpleCorootFaceExistence`: nonempty open coroot faces.
- `Intertwining.CentralActionQuotientFiniteness` and
  `Intertwining.PieceActionQuotientFiniteness`: finite action quotients.
- `Plancherel.UnramifiedMonomialSeparation`, by Worker 194: polynomial clearing in the
  unramified coordinates.

The published inputs are `representedGeometricLemma`, `pqRegularityPieceFiltration`,
`pqRegularity_of_disjoint_generalizedCharacters`, `pqSupportGraded`,
`pqRegularIntertwiningRestrictionEquiv`,
`normalizedRealPart_piece_eq_sub_nonzeroCone_of_nonidentity`,
`exists_untwisted_sourceJacquetExponent_of_twisted_piece`,
`arbitraryParabolicJacquetAdmissibility`, `leviJacquetFiniteType`,
`admissibleSchur_centralCharacter`, `parabolicRootPresentation` and
`relativeRootReflectionExistence`.

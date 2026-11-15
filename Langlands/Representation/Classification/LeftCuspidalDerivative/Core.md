# The Jacquet module of `𝔄 × E` along `(a, m)`

Lean module: `Langlands.Representation.Classification.LeftCuspidalDerivative.Core`.

An internal module of the proof of
`Langlands.Classification.LeftCuspidalDerivative.LeftCuspidalDerivativeLemma`. Fix a
supercuspidal representation `A` of `GL_d` (`d > 0`), an irreducible `A`-pure
representation `𝔄` of `GL_a` (`a > 0`; `IsPure` from module `PowerSupport`) and an
irreducible left `A`-reduced representation `E` of `GL_m` (`m > 0`). The module analyses the
normalized Jacquet module along `(a, m)` of the normalized parabolic induction of
`𝔄 ⊠ E` from the same block shape `(a, m)`, through the geometric lemma
(`padicGeometricLemma`) filtration. This is the classical computation behind the uniqueness
of the highest `A`-derivative (Bernstein–Zelevinsky 1977, Zelevinsky 1980, Mínguez 2009):
the identity piece is `𝔄 ⊠ E`, and no other piece contains `𝔄` in its first block. Only the
mathematics stated in the Lean declarations below is claimed.

## Declarations

* `isIrreducible_externalSmoothObject`: an external tensor product of finitely many
  irreducible admissible smooth representations is irreducible
  (`FiniteTensor.isIrreducible_external` with Schur's lemma
  `admissibleSchur_scalarEndomorphism`).
* `exists_isSubquotient_piece`: if `F` is glued from functors `pieces i` (`IsGluedFrom`),
  every irreducible subquotient of `F.obj Y` is a subquotient of some `(pieces i).obj Y`
  (`WeylBranchPieces.exists_isSubquotient_graded` on the gluing filtration).
* `multiplicity_eq_one_of_isGluedFrom`: if `F.obj Y` has Jordan–Hölder multiplicity `M`
  with respect to `τ`, the piece `i₀` has multiplicity `1`, and no other piece has `τ` as a
  subquotient, then `M = 1`. Proof: the multiplicities add along the gluing filtration
  (`WeylBranchPieces.grade_multiplicities`); a graded piece with positive multiplicity has
  `τ` as a subquotient (`WeylBranchPieces.isSubquotient_of_positive_multiplicity`);
  multiplicities are unique (`HasJordanHolderMultiplicity.unique`).
* `nonempty_identityPieceEquiv`: for the label `w = 1` (source and target shape equal), the
  geometric piece of a smooth representation `A` of the Levi is equivalent to `A` itself
  (the shared `Langlands.Geometric.wholeConjugatingPieceEquiv` from
  `Langlands.Representation.Geometric.ReversedIdentityPiece`, with `conjugatesLevi_one`
  and `transport_one`). The shared construction identifies a whole-Levi-conjugating
  piece with the transport of its smooth source by composing `fullRefinedJacquetEquiv`,
  `subgroupEqualityEquiv`, `intersectionTransportFullEquiv` and `fullRefinedInductionEquiv`.
* `not_isSubquotient_geometricPiece_of_ne_one`: for a minimal representative `w ≠ 1` of the
  pair of shapes `((a, m), (a, m))` and finite-length left `A`-reduced `E`, `𝔄` is not a
  subquotient of the first-block (`GL_a`) restriction of the geometric piece of label `w`
  of `𝔄 ⊠ E`. Proof: by `binaryGeometricPieceConstituents` (module `Pieces`), either
  `w = 1`, or `𝔄` is a first-block constituent of `E`, or `𝔄` is a subquotient of
  `ρ₁ × ρ₂` with `ρ₂` (of positive rank) a first-block constituent of `E`. In the second case
  `A` is a first-block constituent of `𝔄` (`isFirstBlockConstituent_of_isPure`, module
  `PowerSupport`), hence of `E` (`isFirstBlockConstituent_trans`, module `Transitivity`),
  contradicting left reducedness (`not_leftReduced_of_isFirstBlockConstituent`, module
  `FirstBlock`). In the third case `ρ₂` is `A`-pure
  (`isPure_right_of_isSubquotient_binaryProduct`) and the same argument applies to `ρ₂`.
* `isSubquotient_firstBlock_twoBlock`: `𝔄` is a subquotient of the first-block restriction
  of `𝔄 ⊠ E` when `E` is irreducible (hence nonzero;
  `isSubquotient_external_comp_mulSingle`).
* `isIrreducible_twoBlock`: `𝔄 ⊠ E` is irreducible (irreducible representations of `GL_n`
  are admissible by `glFiniteLengthAdmissibility`).
* `nonempty_equiv_of_isSubquotient_glued` and its wrapper
  `nonempty_equiv_of_isSubquotient_jacquetInduction`: an irreducible subquotient `Z` of the
  Jacquet module of the induction of `𝔄 ⊠ E` whose first-block restriction has `𝔄` as a
  subquotient is equivalent to `𝔄 ⊠ E`. Proof: `Z` is a subquotient of some piece
  (`exists_isSubquotient_piece`); a piece of label `≠ 1` is excluded by
  `not_isSubquotient_geometricPiece_of_ne_one`; the piece of label `1` is `𝔄 ⊠ E`, which is
  irreducible, so `Z ≅ 𝔄 ⊠ E` (`CuspidalInductionJacquetConstituent.nonempty_equiv_of_isSubquotient`).
  The `_glued` version takes the data of the geometric lemma as hypotheses; the wrapper
  obtains them from `padicGeometricLemma`.
* `multiplicity_eq_one_glued` and its wrapper `multiplicity_eq_one_jacquetInduction`: every
  Jordan–Hölder multiplicity `M` of `𝔄 ⊠ E` in that Jacquet module equals `1`. Proof:
  `multiplicity_eq_one_of_isGluedFrom` with the identity piece (`w = 1` is a minimal
  representative since block indices are strictly monotone), whose multiplicity is `1`
  because it is equivalent to the irreducible `𝔄 ⊠ E`
  (`UnlinkedSocleProduct.hasJordanHolderMultiplicity_one`,
  `equivJordanHolderMultiplicityTransport`); all other pieces are excluded as above.

## Lean notes

The block shape `(a, m)` is written out as `BlockShape.ofPair a m ha hm rfl` everywhere
(no `let`), and the outputs of `padicGeometricLemma` are passed as
`(by with_reducible exact _)`: the two elaborations differ only in proof terms, which the
default-transparency unifier handles slowly.

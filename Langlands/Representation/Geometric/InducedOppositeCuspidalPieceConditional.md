# Cuspidal pieces of opposite Jacquet modules from the geometric lemma

Author: Worker 954.

The module `Langlands.Representation.Geometric.InducedOppositeCuspidalPieceConditional`,
namespace `Langlands.InducedOppositeCuspidalPiece`, proves that the
cuspidal-piece statement `Langlands.GLInducedOppositeJacquetCuspidalPieceStatement`
follows from the geometric lemma. It proves an implication and does not
construct the geometric filtration itself. The closed geometric-lemma proof
is `Langlands.Geometric.padicGeometricLemma` in
`Langlands.Representation.Geometric.GeometricLemmaProof`; the final
`InducedCuspidalExponentPersistenceProof` module supplies that proof to the
implications developed here.

The only axioms used are `propext`, `Classical.choice` and `Quot.sound`. There is
no `sorry` and no new axiom.

## Main results

- `cuspidalPiece_of_geometricLemma T B C hn hgeo`. Fix a prime `p`,
  `F : PadicField p`, `T : F.TopologicalData`, `n` with `0 < n`, and block
  shapes `B C : BlockShape n`. It assumes
  `hgeo : GeometricLemmaTheorem.{uF, uW} T B C.reverse`, the geometric lemma
  for the pair `(B, C.reverse)` with inducing carriers in universe `uW`. It
  proves the conclusion of the cuspidal-piece statement for these `B` and `C`
  and for all `π : Rep.{uW}` and `ρ : Rep.{uV}`. The hypotheses on `π` and
  `ρ` are those of the statement: `π` smooth; `ρ` irreducible and
  `IsLeviCuspidal C`; and some subrepresentation of
  `oppositeJacquet T C (induced T B π)` surjects onto `ρ`.
- `glInducedOppositeJacquetCuspidalPiece_of_padicGeometricLemma`, of type
  `PadicGeometricLemmaTheorem.{uF, uW} → GLInducedOppositeJacquetCuspidalPieceStatement.{uF, uV, uW}`.
  It applies the previous theorem with the instance `(B, C.reverse)` of the
  hypothesis.

## Helper lemmas

- `conjugatesLevi_flatten_of_intersections B C S w hS hR`. Assume
  `sourceLevi F B C w = refinedLevi F B S` and `sourceLevi F C B w⁻¹ = ⊤`.
  Then `ConjugatesLevi (B.flatten S) C w`: conjugation by the permutation
  matrix of `w` takes the flattened Levi of `B.flatten S` onto the Levi of `C`.
  One inclusion uses `leviEmbedding_mem_flattenedLevi_iff` and `hS`. For the
  other, every element of the Levi of `C` lies in `sourceLevi F C B w⁻¹` by
  `hR`, so it is a conjugate of an element of the Levi of `B`. That element
  then lies in `sourceLevi F B C w`, which is the refined Levi.
- `leviConjugation_reverse_inv_symm`. For any proof of
  `ConjugatesLevi C C.reverse (C.reversePermutation⁻¹ * 1)`, the inverse of
  the resulting Levi isomorphism is `(leviReverseEquiv C).symm`.
- `exists_transport_subrepresentation`. Let `σ` be a representation of the
  Levi of `B` and `τ` one of the Levi of `C`. If `τ` is an actual subquotient
  (`WeylBranchPieces.IsSubquotient`) of `transport B C w hw σ`, then some
  subrepresentation `U` of `σ` has a surjective intertwining map from
  `transport B C w hw U.toRepresentation` onto `τ`. Transport does not change
  the carrier, so `U` is the same submodule and the map is the same linear map.
- `nontrivial_of_isIrreducible`. An irreducible representation has a
  nontrivial carrier. This is Mathlib's `IsSimpleModule.nontrivial` for the
  associated module.
The proof reuses `Langlands.GeometricExcessBranch.isLeviQuasicuspidal_reverse`
and `Langlands.GeometricExcessBranch.not_isSubquotient_properInduced` from
`Langlands.Representation.Exponents.GeometricExcessBranchFromUpper`.
The first proves quasicuspidality of the inverse block-relabelled representation;
its `reversedLeviRepresentation` is definitionally the pullback used here.
The second excludes irreducible quasicuspidal subquotients of proper normalized
refined induction, allowing the inducing and constituent carriers to have
different universes. Its irreducibility argument is supplied from the local
instance. These published declarations replace the duplicate helper proofs.

## Proof of `cuspidalPiece_of_geometricLemma`

Write `I = induced T B π`, `r = leviReverseEquiv C`, and
`ρr = ρ.ρ.comp r.symm.toMonoidHom`.

1. `ρr` is irreducible (`isIrreducible_comp_of_surjective`) and quasicuspidal
   along `C.reverse` (`GeometricExcessBranch.isLeviQuasicuspidal_reverse`, from the quasicuspidal part
   of `IsLeviCuspidal`).
2. Reversal: the published `oppositeJacquetReverseEquiv T C I` identifies
   `oppositeJacquet T C I` with the upper Jacquet module
   `T.normalizedJacquet C.reverse I.ρ` pulled back along `r`. Restrict the
   hypothesis along `r.symm`, using `IsSubquotient.of_equiv_left` and
   `IsSubquotient.comp`. Then `ρr` is an actual subquotient of the upper
   Jacquet module along `C.reverse`. This module is, definitionally, the value
   of `jacquetInductionFunctor T B C.reverse` at the smooth representation `π'`
   built from `π`.
3. The geometric lemma `hgeo` provides refinements `Sf`, `Rf`, their
   intersection identities `hS`, `hR`, an enumeration `e`, and a gluing
   `IsGluedFrom`. The published `WeylBranchPieces.IsGluedFrom.exists_isSubquotient_piece`
   gives an index `i` such that `ρr` is an actual subquotient of the piece
   `geometricPieceFunctor T B C.reverse (e i) (Sf (e i)) (Rf (e i)) _ _` at `π'`.
4. Proper target refinement. If `refinedParabolic F C.reverse (Rf (e i)) ≠ ⊤`,
   the piece is by definition a normalized refined induction from
   `Rf (e i)`, and `GeometricExcessBranch.not_isSubquotient_properInduced` gives a
   contradiction.
5. Whole target. Otherwise
   `refinedLevi_eq_top_of_refinedParabolic_eq_top` and `hR` give
   `sourceLevi F C.reverse B (e i)⁻¹ = ⊤`. With
   `hS`, `conjugatesLevi_flatten_of_intersections` gives
   `hw : ConjugatesLevi (B.flatten (Sf (e i))) C.reverse (e i)`. Worker 514's
   published `Geometric.wholeLeviGeometricPieceEquiv` identifies the piece with
   `transport (B.flatten (Sf (e i))) C.reverse (e i) hw σ`, where
   `σ = (T.normalizedRefinedJacquet B (Sf (e i)) π.ρ).comp (flattenedLeviEquiv F B (Sf (e i))).toMonoidHom`.
   So `ρr` is an actual subquotient of that transport.
6. Back to `C`. Let
   `hw' = conjugatesLevi_mul hw (conjugatesLevi_reverse C)`, a proof of
   `ConjugatesLevi (B.flatten (Sf (e i))) C (C.reversePermutation * (e i))`.
   Restrict along `r` (`ρr.comp r = ρ.ρ`). The published
   `transportReverseEquiv hw hw' σ` then shows that `ρ.ρ` is an actual
   subquotient of `transport (B.flatten (Sf (e i))) C (C.reversePermutation * (e i)) hw' σ`.
7. `exists_transport_subrepresentation` converts this into the statement's
   form. The witnesses are `S = Sf (e i)`, `w = C.reversePermutation * (e i)`
   and `hw'`, together with the resulting subrepresentation and surjection.

The permutation `w` is block reversal of `C` composed with a minimal
representative for `(B, C.reverse)`. This is why the statement claims no
minimality of `w`.

## Provenance

The route follows I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472 (registered source `bernstein-zelevinsky-1977-induced-i`): section 2.12
(geometric lemma, printed p.448), section 2.4(d) (printed p.447), and section
1.7 (transport, printed p.443). It also uses the GL fact that block reversal
conjugates the opposite parabolic of `C` to the upper parabolic of
`C.reverse`, in the Library as `oppositeJacquetReverseEquiv`. The combination
is derived, not a numbered source result. Every source fact enters only
through the Library declarations named above. Of these, only the geometric
lemma is a hypothesis here; the rest are proved in the Library.

## Scope

The module supplies no exponent, temperedness or numerical information. It
does not exclude the identity piece, does not repair constituents, does not
perform the adjointness step, and does not give an occurrence in a prescribed
quotient. It does not prove `GLInducedOppositeJacquetCuspidalPieceStatement`
outright: the result holds only under the geometric lemma for `(B, C.reverse)`.

# Transport lemmas for embeddings into iterated cuspidal products

Module `Langlands.Representation.Classification.MoeglinWaldspurgerDerivativeToolkit`, namespace
`Langlands.MoeglinWaldspurger.Derivation`. Written by Worker 5735 for Task 5735 (internal
infrastructure, no literature content).

* `isSubrepresentation_trans`, `isSubrepresentation_of_iso_left`, `isSubrepresentation_refl`,
  `isSubrepresentation_of_iso'`: the relation `SmoothRep.IsSubrepresentation` (existence of an
  injective morphism) is transitive, reflexive and invariant under isomorphism (compose the
  injective morphisms with the isomorphisms).
* `isSubrepresentation_castRank`: rank transport preserves subrepresentations (by `subst`).
* `leftReduced_of_iso`: left reducedness (`LeftReduced` of `LeftCuspidalDerivativeStatement`)
  is invariant under isomorphism, since it quantifies over subquotients
  (`SmoothRep.IsSubquotient.of_iso_right`).
* `supercuspidal_hasFiniteLength`, `powerProduct_hasFiniteLength`: a supercuspidal
  representation is irreducible, hence of finite length; `A^K × Y` has finite length when `Y`
  has, by induction on `K` with the published finite-length preservation of the binary product.
* `powerProduct_mono`: `A^K × -` preserves subrepresentations, by induction on `K` with the
  published injectivity of the binary product map (`binaryProductMap_injective`).
* `LDrel_of_embedding` (**comparison wrapper**): assuming `LeftCuspidalDerivativeLemma`, if an
  irreducible `π` embeds into the rank transport of `A^K × Y` with `Y` of finite length, left
  reduced, having an irreducible subrepresentation, and all of whose irreducible
  subrepresentations have class `S`, then `LDrel c [π] K S`. The proof picks an irreducible
  subrepresentation `D` of `Y` (left reduced by the subquotient clause), notes that every
  irreducible subrepresentation of `Y` is isomorphic to `D`, and applies the comparison clause.

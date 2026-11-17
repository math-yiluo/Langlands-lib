# Transporting local Weyl relations to arbitrary affine bases

This internal support module proves that the published local commutator and
negative-simple relation statements supply the relation hypotheses of the
coordinate-cell assembly over every commutative ring. The conclusions remain
conditional on the corresponding local statements. The module does not prove
those local statements or assume an affine Isomorphism Theorem.

## Scope

`AffineSplitWeylRelations.commutatorRelations_of_local` takes
`h2 : LocalSplitWeylCommutatorStatement`, two reductive groups over `Spec R`,
closed fibrewise maximal coordinate tori with the same fibrewise root datum `P`,
a base `b`, descending simple words `W`, Weyl-normalized simple-root and opposite
root parametrizations for both groups, and a positive-root enumeration monotone
in height. It proves `CommutatorRelations b W u u' pos` over the arbitrary ring
`R`.

`AffineSplitWeylRelations.negSimpleRelations_of_local` takes the same group,
torus, root-datum, word, parametrization and positive-order hypotheses, an
arbitrary negative-root enumeration, and
`h3 : LocalSplitWeylNegSimpleStatement`. It proves `NegSimpleRelations` for the
two Weyl-family cell maps over `R`.

Neither theorem assumes that `R` is local, reduced or nontrivial. Their relation
predicates quantify over local test rings whose residue fields are separably
closed, exactly as in the published coordinate-cell assembly predicates.

## Implemented proof

The first group of lemmas, in `LocalSplitRootBaseChange`, proves compatibility
with arbitrary coefficient base change. Constant Weyl points are compared by
their three root factors. Conjugation then commutes with base change by the
group law, and induction on the simple word gives compatibility of `wordConj`
and the whole `weylFamily`. The comparison of root points, positive commutators
and ordered products follows because `GroupScheme.baseChangePointsEquiv` is a
group isomorphism.

`liftCellPoint` carries a point of the original coordinate cell over a test
scheme of the new base to a point of the coordinate cell on that base, preserving
all additive and multiplicative coordinates. The published coordinate formulas
and the canonical split-torus comparison show that its torus coordinate
corresponds to the original one. Thus evaluation of the base-changed cell map
on the lifted point corresponds to evaluation of the original cell map; the
same conclusion holds for the whole Weyl family.

For each relation test `s : Spec A ⟶ Spec R`, the proof equips `A` with the
`R`-algebra structure induced by `Spec.preimage s`. It base changes both groups,
the torus embeddings, root parametrizations and Weyl points to `A`. Published
base-change results preserve reductivity, closedness, fibrewise maximality and
the full coordinate root datum. The local statement is then applied over `A`
and tested at its identity morphism. The point comparison transfers the resulting
relation back to `s`.

For the negative-simple relation, both input cell points are first transported
along the equality between this identity test viewed over `R` and `s`, then
lifted by `liftCellPoint`. After applying the local relation, the point comparison
returns the desired equation, and precomposition with that test isomorphism is
cancelled.

## Provenance

All constructions and proofs are derived from the imported published Library
coordinate-cell, arbitrary-ring root base-change and fibrewise root-datum
base-change APIs. These are internal transport lemmas, with no new
source-level definition or additional geometric assertion.

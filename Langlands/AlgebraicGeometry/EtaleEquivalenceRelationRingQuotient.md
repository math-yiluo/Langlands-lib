# Affine quotients from faithfully flat coordinate-ring pushouts

Author: Worker 1203.

This internal interface isolates the final geometric step in the planned
proof of `EtaleEquivalenceRelationSerreCriterionStatement`. It imports the
published `EtaleEquivalenceRelation` and `HasAffineQuotient` unchanged.
It neither assumes nor proves the Serre criterion itself.

For an étale equivalence relation `E`, the structure
`E.FaithfullyFlatRingQuotient` consists of a commutative ring `A` in the same
universe as `E`, a ring homomorphism `i : A → Γ(E.U, ⊤)`, a proof that `i` is
faithfully flat, and a pushout square in commutative rings whose four maps
are `i`, `i`, `E.t.appTop`, and `E.s.appTop`. Thus the coordinate ring of the
relation is the pushout of two copies of the coordinate ring of the object
scheme over `A`. The certificate does not require `A` to be a subring or
identify it with an invariant ring; those are obligations of the algebraic
part of the planned Serre proof.

Assume `E.U` and `E.R` are affine. For such a certificate `Q`, the
definition `Q.quotientMap` is the composite

`E.U → Spec Γ(E.U, ⊤) → Spec A`.

The first map is the canonical affine-scheme isomorphism. Faithful flatness
of `i` gives flatness and surjectivity of the second map, and hence of the
composite, by Mathlib's `flat_and_surjective_SpecMap_iff`.

`Q.isPullback_quotientMap` turns the supplied ring pushout into a pullback of
affine schemes using `isPullback_SpecMap_of_isPushout`, then transports the
square along the canonical isomorphisms for `E.U` and `E.R`. It proves
`IsPullback E.t E.s Q.quotientMap Q.quotientMap`.

The quotient map is quasi-compact because its source and target are affine.
The theorem instance `quotientMap_etale` applies the fpqc descent of étale
morphisms from
`Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent` to this pullback
square. The covering morphism is `Q.quotientMap`, already flat, surjective
and quasi-compact; the morphism after base change is the étale first
projection `E.t`. Consequently the quotient map is étale and in particular
locally of finite presentation. The theorem `Q.hasAffineQuotient` now uses
`Spec A` and this map as the witnesses for the published predicate
`E.HasAffineQuotient`.

The construction is derived directly from the published definitions and
the named Mathlib results at the prepared Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. It is internal proof
infrastructure, not a translation of an additional literature statement.
It uses neither a Noetherian hypothesis nor comodule acyclicity: those
hypotheses are needed to construct the ring certificate in the remaining
Serre proof.

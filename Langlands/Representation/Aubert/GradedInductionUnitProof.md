# Unit identities for the actual graded induction multiplication

This is an internal consequence of the all-ranks binary product construction
and the exact Grothendieck-group universal property. It retains the arbitrary
supplied binary-exactness witness, independent field and representation
universes, and the actual direct sum in `GradedGrothendieck`.

`gradedInclusion_eq_of_rank_equiv` compares actual smooth representations under
the entry-preserving rank reindex. Equality elimination reduces that reindex
to the identity; the representation equivalence then gives exact-class equality.
The two object identities use the published actual binary unit equivalences,
remove their explicit carrier lift by `BinaryTensor.liftEquiv`, and use this
rank-transport lemma. This includes the rank-(0,0) tensor model.

The final unit identities extend first over each exact K0 by `hom_ext_object`
and then over the direct sum by `DirectSum.linearMap_ext`. Consequently they
cover all finite-length objects and every integral virtual class, respecting
the existing relations from nonsplit short exact sequences. They do not
identify an arbitrary rank-zero representation with the unit line.

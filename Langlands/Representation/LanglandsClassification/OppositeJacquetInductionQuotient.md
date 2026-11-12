# Induction quotients from nonzero opposite Jacquet maps

Worker 148. This internal assembly step converts a supplied nonzero map from
an actual smooth Levi representation into an actual Jacquet module to a
surjection from induction onto an irreducible ambient representation. It uses
a supplied second adjunction for the displayed induction and Jacquet functors.
The intended application takes the Jacquet functor for the opposite parabolic.
The theorem uses the adjunction directly and needs no further geometric
opposition hypotheses.

`exists_surjective_leviInduction_of_nonzero_jacquetMap` takes two represented
rational parabolics with the same Levi scheme, their actual normalized functors,
the second adjunction in carrier universe `max u v`, an inducing representation
in universe `v`, an irreducible ambient representation on its original carrier
in universe `v`, and a nonzero intertwiner into its specified Jacquet module.
It returns an actual surjective intertwiner from induction on the original
inducing carrier to the original ambient target. The induced carrier is in
universe `max u v`. The field universe `u` and carrier universe `v` remain
independent.

The proof lifts both representations to universe `max u v`. Published
cross-universe Jacquet transport and `intertwiningMapCongr` turn the supplied
map into a nonzero map between the lifted objects. The actual induction
functor is additive by its pointwise map formula, so the supplied adjunction's
additive Hom equivalence converts this map to a nonzero induction map.
Published cross-universe induction transport and the ambient lift equivalence
carry that map back to the original inducing object and target. Both transports
send zero to zero, so the resulting map is nonzero. The standard irreducibility
lemma for intertwining maps makes it surjective.

`leviInductionQuotientOfJacquetMap` selects a map from this proved existence
and retains its surjectivity certificate. Classical choice makes no canonical
selection assertion.

The provenance is internal, using the published carrier transport, smooth
functors and categorical adjunction APIs. Second adjointness is an explicit
input. No admissibility, finite length, positivity or temperedness premise is
needed for this assembly step, and no second-adjointness or Langlands
classification theorem is proved here.

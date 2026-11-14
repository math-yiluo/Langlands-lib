# Transport and construction of relative unipotent radicals

This internal construction supports descent of the relative radical in
Conrad's *Reductive group schemes* (2014), Corollary 5.2.5. Its mathematical
inputs are the published relative predicates and the dynamic representability
theorem. The dynamic relative Levi statement remains an explicit hypothesis;
this module does not prove that statement or the global radical theorem.

`IsRelativeUnipotentRadical.precomp_iso` and `.comp_iso` transport relative
radicals through source and ambient group scheme isomorphisms. Closedness,
smoothness and normality transport through the isomorphism. On each chosen
geometric fibre, functoriality of base change reduces the assertion to the
corresponding transport theorem for represented field radicals.

`IsRelativeUnipotentRadical.of_range_eq` transfers the relative radical
predicate to another closed representative of the same subgroup on every
test scheme. Equal all-test images give an actual source isomorphism
compatible with the inclusions, to which source transport applies.
The equality assumption includes tests over nonreduced schemes.

`RelativeLevi.dynamicUnipotentRadical` constructs an actual source group,
inclusion into the supplied represented dynamic parabolic, and proof that
this inclusion is a relative radical. Dynamic representability supplies
representatives of the dynamic unipotent subgroup and centralizer.
Containment of the unipotent subgroup in the dynamic parabolic gives a
factorization through the supplied parabolic representative. The assumed
`DynamicRelativeLeviStatement` then verifies the radical predicate for that
factorization.

All constructions retain an arbitrary base scheme and universe. They are
derived interfaces for transporting representatives and using an explicit
theorem hypothesis, rather than new claims attributed to the literature.

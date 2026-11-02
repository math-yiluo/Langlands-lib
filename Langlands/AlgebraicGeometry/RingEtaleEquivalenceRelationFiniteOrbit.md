# Radical ideals of finite closed orbits of affine étale relations

This internal helper combines the ring-to-scheme adapter with the finite
closed orbit and ideal constructions of Workers 101 and 239. Worker 122
implemented this ring-level assembly. It starts from an explicitly supplied
nonempty closed invariant subset; it does not prove support invariance,
construct a quotient coaction, or prove the nonzero-invariant statement.
All deductions use the imported Library helpers and pinned Mathlib.

For a ring étale equivalence relation with Noetherian object ring `B`,
equality of the source and target preimages of a subset of `Spec B`
means exactly that membership is preserved by the actual relation on
scheme points. The associated scheme relation therefore chooses a minimal
nonempty closed invariant subset inside the supplied closed subset `S`.
The construction `finiteClosedOrbit` is this choice. Its specification
records containment in `S`, nonemptiness, finiteness, discreteness in the
inherited topology, ambient closedness of every point, and equality of
source and target preimages.

`finiteOrbitIdeal` is the actual vanishing ideal of this chosen subset.
Nonemptiness makes the ideal proper, and vanishing ideals are radical.
The zero locus is exactly the chosen closed subset, so it is contained
in `S`. The imported finite closed point ideal calculation proves that
the extensions of the ideal along the two original étale maps agree.

The quotient spectrum is discrete in its actual Zariski topology. The
prime spectrum map of the quotient homomorphism is an embedding, and its
range is the zero locus of the ideal, which is the chosen closed discrete
subset. Pulling back this discrete subset along the continuous injective
map gives the whole quotient spectrum. The generic lemma
`FiniteClosedIdeal.discreteTopology_quotient_vanishingIdeal` records this
step for any closed discrete subset, without a Noetherian hypothesis.

Finally, the quotient by `finiteOrbitIdeal` is nontrivial and reduced
because the ideal is proper and radical. It is Noetherian as a quotient
of `B`; the discrete spectrum result and the imported finite-algebra
helper make it Artinian. All rings in the relation lie in the arbitrary
universe `u`. Neither affine descent nor any invariant zero-detection
conclusion is assumed.

# Hopf-coordinate adapter for the affine homomorphism theorem

This internal support module translates faithful flatness over Hopf subalgebras
into faithful flatness of an injective coordinate homomorphism. Its input is
explicitly conditional: `HopfSubalgebraFaithfullyFlatStatement k` says that every
finite-type commutative Hopf algebra over the field `k` is faithfully flat over
each subalgebra whose comultiplication lies in the span of its pure tensors and
which is stable under the antipode.

The auxiliary algebraic arguments are derived directly from the Mathlib
definitions. Inverse naturality for algebra cogroups proves that a Hopf-algebra
morphism commutes with antipodes. Tensor-product induction shows that its
algebraic range has the stated comultiplication property. Its range is also
stable under the antipode. Applying the explicit input to this range and
composing the range inclusion with the bijective range restriction proves
faithful flatness of an injective morphism.

This module is part of the proof of `AffineHomImageStatement`; it does not claim
to have discharged its explicit Hopf-subalgebra input.

For the geometric step, `pullback` uses full faithfulness of `hopfSpec` to
represent an actual homomorphism by a Hopf-algebra map between the chosen
coordinates. The theorem `spec_map_pullback` identifies its spectrum with the
original map conjugated by the coordinate isomorphisms. Scheme-theoretic
dominance makes the map on global sections injective; naturality of the
`ΓSpecIso` comparison transfers this to the Hopf-algebra map. This step uses no
reducedness assumption.

When the source group scheme is locally of finite type over `Spec k`, its
coordinate algebra is finite type over `k`. The conditional algebra result
therefore makes its injective coordinate pullback faithfully flat. Mathlib's
`flat_and_surjective_SpecMap_iff` gives flatness and scheme-surjectivity of its
spectrum, and the coordinate isomorphisms transport these properties to the
original actual group homomorphism. The theorem `flat_and_surjective` retains
only the explicit Hopf-subalgebra input, affine source and target, a locally
finite type source, and scheme-theoretic dominance.

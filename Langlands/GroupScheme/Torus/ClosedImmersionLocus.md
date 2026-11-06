# Open neighbourhoods of closed split-torus homomorphisms

`exists_open_isClosedImmersion_baseChange` proves the following actual
group-scheme assertion over an arbitrary base scheme `S`. Given a split
torus `H/S`, an affine group scheme `G/S`, a supplied homomorphism `i : H → G`,
and a field-valued point `x : Spec K → S` for which the actual base change
of `i` is a closed immersion, there is an open immersion `q : V → S`
through which `x` factors and over which the actual base change of `i` is
a closed immersion. The factorization is an equality of scheme morphisms.

The implemented proof constructs an affine open chart around the image of
the unique point of `Spec K`. Its universal open-immersion factorization gives
the original field-valued morphism, with an exact equality. Splitness and
affineness survive restriction to this chart. The affine neighbourhood theorem
then supplies a principal open on which the homomorphism is a closed immersion.
Composing the two open immersions gives `V → S`, and composing their point
factorizations gives the asserted equality.

The proof compares one base change along a composite with iterated actual
base change using naturality of the canonical pullback-composition isomorphism.
Closed immersion is preserved and reflected by the two comparison isomorphisms,
so the affine theorem proves the required condition for the original supplied
homomorphism.

The mathematical provenance is internal: this is a direct proof of the
split-source affine-target neighbourhood step, using the diagonal Hopf
coefficient-product argument and elementary affine-chart restriction.
No smoothness, reducedness, noetherian, or finite-presentation hypothesis is
required for this neighbourhood result. It constructs neither a Hom parameter
scheme nor the etale lifting asserted by the separate relative lifting target.

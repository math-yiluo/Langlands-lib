# A nested parabolic as an actual Levi preimage

This is an internal helper for the rational-point form of Renard VI.1.4. It is
derived from the supplied actual Levi multiplication, rational-point density,
and normal unipotent containment. No assertion about arbitrary fields is made.

The first lemma works over any base. An actual subgroup that contains the inner
Levi subgroup and the outer radical, and whose Levi projection lands in the
inner subgroup, is exactly the inverse image of that subgroup. The proof uses
the two coordinates of the inverse multiplication on every test scheme.

The construction `leviPreimageIsoOfRange` turns this all-test range equality
into an isomorphism from the original subgroup scheme to the actual pullback
of the inner subgroup along the outer Levi retraction. It requires the original
inclusion to be a monomorphism and the inner subgroup to be closed. The two
schemes represent the same subgroup functor, so the published uniqueness
construction for representing group schemes gives the isomorphism. Its
homomorphism followed by the pullback inclusion is the original inclusion.
This construction and its compatibility proof work over any base.

The second lemma works over a nonarchimedean local field with smooth connected
affine source groups. Rational-point containment supplies the actual map from
P to Q, by density and closedness. The outer radical lies in P by the preceding
nested-parabolic containment lemma. For a rational point of P, its outer Levi
coordinate remains in P because its radical coordinate lies there. The supplied
rational-point intersection then puts its Levi coordinate in the original inner
subgroup. Density extends this projection containment to every test scheme.
The supplied inner subgroup also lies in P by density. The first lemma now
identifies the all-test range with the inverse image under the outer retraction.

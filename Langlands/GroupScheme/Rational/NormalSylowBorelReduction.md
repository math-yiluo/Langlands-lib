# Normal maximal p-subgroups contained in Borel subgroups

This is an internal reduction for the corrected maximal open pro-p proposition.
It uses the existing algebraic-group interfaces and the finite Ga-series point
count. It does not prove the finite-field Sylow/Borel classification.

Over a finite field, an affine split-unipotent group with only the identity
rational point has trivial range on every scheme test. Indeed, a Ga-series of
length `n` gives exactly `q ^ n` rational points. Since `q` is at least two,
`q ^ n = 1` forces `n = 0`, and the length-zero series is precisely all-test
triviality.

Let `G` be connected reductive over a finite field of characteristic `p`.
Suppose `H` is a normal maximal p-subgroup of `G(k)` and is contained in the
rational-point image of a field-defined geometric Borel `i : B → G`.
The theorem `range_borel_eq_top_of_normal_maximalPSubgroup` shows that the range
of `i` is the top subgroup functor. Present `B` as the dynamic parabolic of a
cocharacter. The opposite contracting subgroup has a smooth affine
split-unipotent representative, whose rational-point image is a p-group.
Normality of `H` makes its join with this image a p-group, so maximality absorbs
the image into `H`, and hence into `B(k)`. The opposite dynamic intersection
theorem makes all these points the identity. The point-count argument above
then makes the contracting subgroup trivial on every test. Signed parabolic
comparison makes the original parabolic the whole group.

`normalMaximalPSubgroupBorelIso` constructs the resulting actual isomorphism
`B ≅ G`, with homomorphism equal to `i`. Solvability transfers along this
isomorphism, and the existing solvable reductive torus theorem proves
`isTorus_of_normal_maximalPSubgroup_le_borel`.

Finally, `finiteFieldNormalSylowTorus_of_sylowBorel` has type
`FiniteFieldSylowBorelStatement.{u} → FiniteFieldNormalSylowTorusStatement.{u}`.
The classification supplies a Borel and its radical whose rational-point image
is `H`; that image is contained in the Borel image, so the preceding result
applies. Both statements retain their published arbitrary-universe scope.
The argument uses finite point counts only for split-unipotent groups and does
not assume Zariski density of rational points over a finite field.

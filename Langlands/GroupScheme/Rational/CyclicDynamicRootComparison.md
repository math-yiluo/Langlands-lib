# Dynamic root groups with cyclic actual root support

Internal supporting construction for the residue root comparison in the
unramified facet problem. The original character is not assumed to be an actual
root. Instead every actual relative root is assumed to be an integral multiple
of it, and its pairing with the chosen cocharacter is strictly positive.

The field and every group and torus live in arbitrary universe `u`. The dynamic
comparison assumes a smooth affine group, a monic split-torus map, and
`HasRelativeRootSystem` for that map. Connected reductive groups with maximal
split torus provide the last hypothesis through the existing root-system proof.
The cyclic support and positive pairing hypotheses remain explicit.

The proof uses the published positive dynamic semigroup comparison, cyclic root
functor comparison, and disjointness of positive rays of indivisible roots.
Positive characters in the cyclic lattice are positive natural multiples.
Consequently two indivisible positive roots have intersecting positive rays,
so they coincide. Descent along positive integral root multiples then puts every
positive actual root in this one ray. The semigroup congruence theorem identifies
the actual dynamic subgroup with the intrinsic root subgroup on every test.
The zero character is excluded explicitly from both semigroups.

A nontrivial dynamic positive subgroup supplies an actual positive root: if
there were no positive ambient tangent weights, semigroup triviality would make
the dynamic subgroup trivial. This argument uses no rational point existence
assumption and no algebraic closedness of the field.

`cyclicDynamicRoot` chooses this actual indivisible positive root, independently
of a later point, from nontriviality of the dynamic subgroup. Its subtype
retains both equalities
`U(ν) = U_b` and `U(-ν) = U_(-b)` on every test scheme. Negation preserves
indivisibility because actual roots are closed under negation.

`characterAut_eq_neg_of_pos_multiple` proves that any torus automorphism
negating the selected root also negates the original character. It writes the
root as a positive natural multiple, rationalizes the character equation,
cancels that nonzero scalar, and uses injectivity of rationalization for a split
torus. The original character need not survive as an actual root.

These are internal consequences of the named Library comparisons and ray
theorems, with no additional external source assertion. This unit does not
derive cyclic support from a descended action, construct an integral
normalizer, or establish the final facet derivative root datum.

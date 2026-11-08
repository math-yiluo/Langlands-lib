# From a supplied Bruhat cover to opposite-cell unit points

This internal geometric argument works over a field `k : Type u`. For the
rational and global constructions, the ambient group `G` and subgroup `H`
have affine structure morphisms over `Spec k`. It retains a supplied Bruhat
cover for the actual subgroup and commutative group scheme `T`, a supplied
normalizing conjugator, dynamic representatives, and a criterion that
unit-valued normalizing points centralize this same `T`. It asserts no
existence of these data and imposes no additional torus hypothesis on `T`.

The mixed-cover lemma applies the ordinary cover to `g n₀`. Multiplication
on the right by `n₀⁻¹` leaves a normalizing middle point and changes the
right subgroup to its conjugate by `n₀`.

The separate coordinate lemma assumes affine structure morphisms for
`G`, `H` and its second group `Q`. It uses left covariance and right inverse
covariance to express the value on a three-factor product as the product of the two
subgroup coordinate values and the middle coordinate value. A unit product
in the commutative ring of global sections has unit factors. Thus the
middle point has a unit value. This calculation works on all relative
test schemes.

For the rational factorization lemma, the supplied centralizer criterion
places that middle point in the centralizer of `j : T.toGrp ⟶ G` and hence
the dynamic centralizer of the chosen cocharacter through `T`. The dynamic limit splits
the left factor into a unipotent point and a centralizer point. These
centralizer points belong to the opposite dynamic parabolic. Combining
them with the right factor and using the supplied representatives gives
actual rational points of the unipotent and opposite parabolic.

For the global construction, retain the affine structure morphisms of
`G` and `H`, and assume additionally that `k` is algebraically closed and
`G` is smooth and locally of finite type over `k`.
The published opposite-cell theorem makes
the supplied multiplication an open immersion. The published rational-open
criterion promotes rational unit-locus factorization to a global lift for
every unit-valued point on an arbitrary relative test scheme.
`bruhatUnitCellLift` constructs this lift, and `bruhatUnitCellLift_comp`
proves its multiplication identity. Projecting the lift and using the
unipotent inclusion into the first parabolic gives
`exists_opposite_parabolic_factors_of_bruhat_unit`, with the right factor
written as an inverse as in the Steinberg big-cell statement. Tests need
neither be affine nor reduced.

The provenance is this implemented composition of the published coordinate
covariance, normalizer group law, dynamic limit, subgroup representation,
opposite-centralizer, opposite-cell and rational-open results. No Bruhat theorem or representation
irreducibility is proved by this conditional construction.

Integration gives the local instances used here module-specific names to permit
joint imports. Their types, values, and local scopes are unchanged.

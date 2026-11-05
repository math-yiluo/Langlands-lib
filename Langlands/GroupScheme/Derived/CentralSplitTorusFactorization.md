# Factorization through the supplied derived maximal split torus

Author: Worker 1562.

This internal construction is derived from the published split-image and
represented-subgroup interfaces. It supplies auxiliary factorizations for the
derived and central split-product proof. It does not assert that the product
map is surjective or is an isogeny.

`IsMaximalSplitTorus.exists_factor_of_commute` works over any field. In an affine
group scheme `M`, every homomorphism from a split torus whose values commute on
all test schemes with those of a supplied maximal split torus factors through
that maximal split torus. The proof forms their product homomorphism and uses
`IsSplitTorus.exists_factor_isSplitSubtorus'` to construct its closed split image.
Maximality makes the second factor's map to that image an isomorphism. Composing
the first factor with its inverse gives the required factorization. No
reductivity or smoothness premise is used.

`IsDerivedSubgroup.exists_factor_splitTorusEnd` assumes that `G` has affine structure morphism, an actual derived
inclusion `d : D → G`, an ambient split-subtorus inclusion `i : S → G`, a maximal
split torus `j : S_D → D`, and a morphism `e : S_D → S` with
`j ≫ d = groupHom e ≫ i`. For an endomorphism `q` of `S` whose ambient values
belong to `derivedSubgroup G` on every test scheme, it constructs `f : S → S_D`
with `f ≫ e = q`. The actual derived predicate supplies representability and a
closed inclusion; no reduced-test or rational-point restriction is imposed.

The proof lifts `q ≫ i` through `d` using
`SubgroupFunctor.IsRepresentedBy.factorHom`. Closedness of `d` implies its
monicity and makes `d` an affine morphism. Composing it with the assumed affine
structure morphism of `G` gives the affine structure morphism of `D`. Monicity reflects commutation of this lifted
map with `j`, since both maps take values in the commutative torus `S` after
composition with `d`. The preceding maximality helper supplies the factor.
Finally monicity of `i` gives the asserted equality in the commutative-group
scheme category.

`IsDerivedSubgroup.splitTorusEndFactor` is a classical choice of this factor;
`IsDerivedSubgroup.splitTorusEndFactor_comp` proves its defining equation. This
chosen morphism and the two auxiliary theorems are internal derived content,
with the proof route given above. The affine ambient hypothesis also applies to this chosen morphism and its
defining equation. All universes and fields remain unrestricted.

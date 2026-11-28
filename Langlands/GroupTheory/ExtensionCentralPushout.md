# Pushout along a map into the center

Gan and Gao push out the central extension by `Z(G∨)` along its inclusion
into the dual group `G∨` in the local and global covering L-group constructions.
The source is Gan–Gao, *The Langlands–Weissman program for Brylinski–Deligne
extensions*, Astérisque 398 (2018), §5.2, printed pp. 213–215 (PDF pp. 231–233),
and §13.2, printed pp. 244–245 (PDF pp. 262–263). The registered source
`gan-gao-2018-langlands-weissman-program` has SHA-256
`fabbe056bdec2a5d57a22a0d3ad275640d0343c3f71092a7df427f7ebaebe892`.

The construction in `Langlands.GroupTheory` takes a Mathlib `GroupExtension`
with central kernel map `i : A →* E` and a homomorphism `j : A →* Z(D)`.
`centralPushoutRelation` is the image of `a ↦ (j(a)⁻¹, i(a))`. Inversion in
`Z(D)` is multiplicative, so this image is a subgroup of `D × E` contained
in the center. The ambient group `D` can be noncommutative. `CentralPushout`
is the quotient by that subgroup. The classes of `(d, 1)` and `(1, e)` give
`centralPushoutInl` and `centralPushoutFromOld`. Their images commute because
the factors commute in the product, and their maps on `A` agree by the defining
quotient relation. The projection sends `[(d, e)]` to `p(e)`, so it is trivial
on `D` and equals the old projection on `E`.

`centralPushoutExtension` packages exactness in Mathlib's `GroupExtension`.
If the class of `(d, 1)` is trivial, the relation's second coordinate has
`i(a) = 1`. Injectivity of `i` gives `a = 1` and then `d = 1`.
If a class `[(d, e)]` projects to `1`, exactness of the old extension writes
`e = i(a)`, so the class equals `[(d * j(a), 1)]`. Surjectivity comes from
the old projection through the map from `E`.

`centralPushoutLift` descends the product homomorphism
`(d, e) ↦ u(d) * v(e)` for `u : D →* H` and `v : E →* H` with commuting images
and equal restrictions to `A`. Agreement sends each relation to the identity.
The lift restricts to `u` and `v`, and `centralPushout_hom_ext` proves uniqueness
by writing the class of `(d, e)` as the product of the two factor classes.

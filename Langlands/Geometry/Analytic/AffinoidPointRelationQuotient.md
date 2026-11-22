# Kernel pairs and quotients of affinoid points

Work over a complete, ultrametric, nontrivially normed field `K`. Let
`f : A → B` be a bounded map of presented affinoid `K`-algebras and
let `x` be a `B`-valued point of a separated algebraic space locally
of finite type over `K`. Let `p_x : M(B) → Y` be the point map into its
supplied analytification. Given a localized morphism `F : Y → Z` and
a localized monomorphism `b : M(A) → Z`, suppose
`p_x ≫ F = M(f) ≫ b`, where `M(f) : M(B) → M(A)` is induced by `f`.
A supplied `AffinoidPointRelation` for `f` and `x` then gives the
kernel pair of `p_x` in the localized category.

On a small affinoid test spectrum, the two lifts correspond to actual
bounded algebra maps. Equality of their images in the analytification
implies equality of ring-valued points by injectivity of the comparison.
Postcomposition with `F` and cancellation of `b` imply that the two
bounded maps agree on `A`.
The affinoid relation's factorization criterion supplies the algebra map
out of the relation. Finiteness of the first relation map ensures
boundedness of the lift. Generation by the two maps ensures uniqueness.
For arbitrary localized tests, use these lifts on every small chart
spectrum. Chart separation gives joint monicity and the chart gluing
theorem gives the global lift.

For the quotient construction, assume that `A → B` is algebraically
finite étale and that the two localized spectrum maps of the relation
are analytically étale. Reflection for finite Banach maps makes the
two relation maps algebraically finite étale. The finite affinoid
quotient theorem then constructs a presented affinoid algebra `Q`
with algebraically finite étale maps `A → Q` and `Q → B` that factor
the original map. The relation algebra is the ordinary ring pushout
of `Q → B` along itself. On spectra of rings this gives the self-pullback
of the quotient cover. The comparison of faithful flatness with flat
and surjective spectrum maps makes the finite étale cover an fppf
cover. Equality of the two restrictions of the original point then
descends it to `Q`.

The proof is internal. It combines the affinoid point comparison,
localized chart gluing, automatic boundedness in a finite triangle,
and the affinoid realization of a finite étale relation quotient.

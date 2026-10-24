# Affine test comparisons and unit points

This internal construction compares affine test objects in the category of schemes over a fixed base. It derives from the existing `Gm.affinePointsEquiv`, its naturality theorem, and the pullback construction of the multiplicative group scheme in `Langlands.GroupScheme.Multiplicative`. No external existence theorem is asserted.

For a scheme `S`, a commutative ring object `B`, and equal structure maps `f, g : Spec B → S`, `Gm.affineTestIso f g h` is an isomorphism `Over.mk f ≅ Over.mk g`. Both underlying scheme maps are the identity. The equality `h : f = g` supplies the two triangle conditions, and the inverse laws follow from the identity composition laws. `affineTestIso_hom_left` records the underlying forward map.

`affinePointsEquiv_iso` proves that, for every unit `v` of `B`, the point corresponding to `v` on the first test is the composite of this isomorphism with the point corresponding to `v` on the second test. The implemented proof uses injectivity of the affine point equivalence, its global-unit naturality, and the identity action on global sections.

`specIdentityTestIso B` specializes this construction to the structure maps `Spec.map (𝟙 B)` and `𝟙 (Spec B)`, using the functorial identity law for `Spec`.

`affinePointsEquiv_symm_left` expands the underlying scheme map of an affine unit point. It is the pullback lift of the Laurent-coordinate map corresponding to the global unit obtained from `v` through `(Scheme.ΓSpecIso B).inv`, together with the structure map `f`. The triangle holds because the integral affine scheme is terminal. This is a definitional formula for the existing point equivalence, without a new choice of unit normalization.

Finally, `specIdentityTestIso_unit_left` proves that the two identity-test unit points have equal underlying scheme morphisms. Its proof rewrites both by the pullback-lift formula and uses `Spec.map_id`. The comparison is valid in every universe and for every commutative ring, without field or reducedness hypotheses.

This is a general prerequisite for comparing relative affine cocharacter evaluation with evaluation on the identity test. It does not itself compare Harris rational or embedding-labelled coordinates, prove reflex conjugacy, or construct Shimura levels.

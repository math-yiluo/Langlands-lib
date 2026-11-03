# Closed factorization loci for actual affine schemes

This internal derived construction transports the projective tensor coefficient
locus to arbitrary affine schemes over `Spec R` and arbitrary closed subschemes
of their product. The rings and schemes lie in an arbitrary common universe.

`coordinateIso` is the canonical isomorphism from an affine object `X` of the
over category to the spectrum of exactly `((algΓ R).obj X).unop`. It uses the
unit of the algebraic global-sections/spectrum adjunction and the affine
essential-image theorem. This retains the coordinate algebra and its
`R`-algebra structure used by the generic closed-factorization statement.

The main result `affine_closed_locus` takes affine `X` and `Y`, projectivity of
that exact coordinate module of `X` over `R`, and an actual closed immersion
`d : D ⟶ X ⊗ Y`. It produces an object `Z` and an actual closed immersion
`i : Z ⟶ Y`. For every affine test object `T` and every morphism `t : T ⟶ Y`,
factorization of `t` through `i` is equivalent to factorization of the entire
product morphism `X ◁ t : X ⊗ T ⟶ X ⊗ Y` through `d`. The test object is not
required to be flat. The coordinate module need not be finitely generated;
no field, smoothness, reducedness or finite-type hypothesis is imposed.

The implemented argument proceeds as follows. `spec_closed_locus` presents
any closed subscheme of an affine product as an ideal quotient by Mathlib's
closed-immersion presentation theorem. It applies the projective tensor
coefficient locus and transports its criterion through the presentation
isomorphism. `over_factorization_iff` identifies underlying scheme
factorizations with factorizations over the base, using the structural
commutative triangles. `spec_over_closed_locus` uses fullness of `algSpec`
to recover the algebra map of every spectrum test and identifies its product
map by the two pullback projections. `affine_test_spec_closed_locus` uses
`coordinateIso` for the test scheme to cover every affine test. The two
categorical factorization lemmas transport the target or domain along an
isomorphism. `affine_closed_locus_right` uses those lemmas and the coordinate
isomorphisms of `X` and `Y` to give the actual-affine criterion in the
coefficient-first product order. Finally, braiding naturality gives
`affine_closed_locus` in the `X ◁ t` convention. Composition with these
isomorphisms preserves closed immersions.

The source is Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition
(2015), Proposition A.8.10(1), printed pp. 547–549 / PDF pp. 573–575, especially
the coefficient ideal and affine-test factorization argument on printed
p. 549. The preceding tensor construction puts the coefficient algebra first;
the final braiding comparison explicitly reconciles that order with the
projective factor first. The coordinate and categorical comparisons are
internal derived adapters implementing this affine part of the source.

The conclusion here quantifies over affine tests only. Extension to arbitrary
test schemes, gluing for nonaffine `Y`, faithfully flat descent from projective
coordinates after base extension, and the final fixed-subgroup and centralizer
representability targets remain separate obligations.

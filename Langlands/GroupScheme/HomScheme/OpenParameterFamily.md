# Restriction of an actual subgroup family to an open parameter scheme

This internal construction works over an arbitrary scheme in universe `u`. It
restricts an actual subgroup-family homomorphism to an open parameter subscheme;
it does not assume that the source is a torus, that the homomorphism is closed,
or that the ambient group is reductive.

`openParameter U` is the open subscheme defined by `U`, with structural morphism
`U.ι ≫ M.hom`. Its morphism `openParameterMap U` to the original parameter scheme
is a monomorphism. `openParameterLift` factors a parameter morphism through this
open subscheme when its topological image is contained in `U`;
`openParameterLift_fac` proves the factorization over the original base.

The restricted actual family is `familyHom j (openParameterMap U)`.
`evaluate_openParameter` is the composition identity from the published
`SubgroupFamilyEvaluation` module. Thus the comparison is an equality of actual
subgroup functors on every test scheme.

`smooth_openParameter` uses composition of smooth morphisms with an open
immersion. `isProper_openParameter` assumes that `U` is also closed and uses the
closed-immersion criterion for a preimmersion with closed image, then composition
of proper morphisms.

`existsUnique_evaluate_openParameter` assumes that a supplied subgroup functor
has a unique classifying morphism for the original family, and that every such
classifying morphism has image in `U`. The open immersion lifts that morphism;
composition of evaluation proves that the lift classifies the subgroup.
Uniqueness follows by composing any other classifying morphism with the
monomorphism `openParameterMap U` and using the original uniqueness.

These are derived scheme-theoretic helpers for the construction in Conrad,
*Reductive group schemes* (2014), proof of Theorem 5.2.11(3), p.158: restriction
of the universal parabolic family to its open and closed Borel locus. This
module supplies the restriction construction and its formal properties only;
it does not assert existence of either that locus or a universal family.

# Ordinary roots detected after a group morphism and integral reduction

This internal supporting unit works at arbitrary universe over a local domain
with a specified fraction field. It uses apartment data for a torus map
`i : S → G`, a homomorphism `f : G → H`, a relative-component model of `H`,
a compatible split integral torus for `i ≫ f`, and actual special-fibre
quotient data. The original torus map is a monomorphism and `G` is affine,
as required by the apartment data. No injectivity or isomorphism assumption
is made on `f`.

Let the affine functional `ψ` have relative-root derivative `a`. Assume that
the image under `f` of the whole depth group `U_ψ` consists of integral
points of the model of `H`, and that every integral section whose generic
point lies in the image of `U_(ψ+)` has trivial actual quotient reduction.
If an integral section has generic point in the image of `U_ψ` and its
quotient image lies outside the root functor for twice the specialized
character `a`, then the original `ψ` is an ordinary affine root of the
original apartment. `mem_affineRoots_of_mapped_quotient_exclusion` proves
this assertion, and `ordinaryRootOfMappedQuotientExclusion` packages the
same functional as an ordinary affine root. The coercion lemma retains
exactly `ψ`.

The proof extracts an original depth point mapping to the supplied integral
section. A forbidden containment in the definition of ordinary affine roots
factors that point as `v * w`, with `v` at strict depth and `w` in the
doubled generic root group. Whole-depth integrality supplies an integral
lift `y` of `f(v)`. Dividing the supplied section by `y` gives an integral
section with generic point `f(w)`. Functoriality puts `f(w)` in the
corresponding target root functor, and `IntegralRootReduction` puts the
quotient reduction of this section in the doubled specialized root functor.
Strict-depth vanishing kills the reduction of `y`, contradicting the given
exclusion. If the doubled character is not a generic root, the factor `w`
is trivial and the supplied section itself has strict-depth image.

This is the morphism version of the earlier `OrdinaryRootQuotientCertificate`
argument; its provenance is the actual subgroup-map, ordinary-root, and
integral-root reduction interfaces. It applies in particular to the inner
automorphism used for translated apartments without changing the original
apartment data. Whole-depth integrality and strict-depth vanishing remain
explicit hypotheses. The result assumes no reductivity of the quotient,
Henselian property, perfection, or algebraic closure, and makes no final
facet root-comparison or root-datum assertion.

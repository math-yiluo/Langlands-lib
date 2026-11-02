# Exact integral equations for actual rational dual pullbacks

This is an internal comparison using the existing actual dual maps,
their conditional additive rational extensions, actual rational dual pullback,
and integral representatives of rational isomorphisms. It makes no new
geometric existence claim. All displayed tensor, Picard, dual geometry,
evaluation and ordered-pair additivity prerequisites are inputs, as in the
imported constructions.

For an actual integral homomorphism `f : A ⟶ B` and an integral dual-valued
homomorphism `lamB`, `integralDualPullbackHom` is the actual composite
`f ≫ lamB ≫ dualAB f`. The target is the constructed dual abelian scheme
of `A`, with exactly the supplied dual witnesses and evaluations.
`rationalDualPullbackHom0_homToHom0` proves agreement with the existing
rational dual pullback after including all integral maps into rational Hom.
The proof uses the rational dual map's integral agreement and the inclusion's
compatibility with composition.

`rationalDualPullbackHom0_smul_hom` proves quadratic dependence on the rational
homomorphism: replacing `f` by `r • f` multiplies the pullback by `r * r`.
This follows from linearity of rational dualization and bilinearity of
rational composition.

Fix a supplied rational isomorphism `e`, a supplied
`RationalIsoIntegralData e`, and integral dual-valued maps `lamA` and `lamB`.
Write `n` for the supplied forward denominator. Its defining equation is
`homToHom0 d.hom = n • e.hom`, with `n` nonzero.
`integralDualPullbackHom_rationalization` therefore identifies the
rationalization of the integral pullback along `d.hom` with `n * n` times
the rational pullback along the original `e.hom`.

`rationalDualPullbackMultiple_iff_integralMultipleData` proves that the
existing geometric equation with prescribed multiplier `q` holds exactly
when there are integers `a` and `b` with `a` nonzero, rational scalar identity
`b = a * (n * n * q)`, and the actual integral equation
`a • (d.hom ≫ lamB ≫ dualAB d.hom) = b • lamA`.
The implemented proof uses the generic exact cross-multiple criterion in
`Langlands.CategoryTheory.RationalizationMultiples` and cancels the nonzero
rational scalar `n * n`. It never cancels an integer on an integral Hom group.
`rationalDualIntegralMultipleData` chooses this exact integral data from the
supplied rational equation.

The criterion applies to the same actual representatives and the original
rational isomorphism and multiplier; it does not replace either by a newly
chosen rational isomorphism or multiplier. It imposes no positivity or
polarization property on the two integral dual-valued maps. Such properties,
when required by a consumer, remain the existing geometric conditions.
No geometric isogeny, integral model existence, level-orbit comparison or
moduli representability theorem is asserted here.

# Composition and transport for canonical differential square maps

This internal helper module treats the actual canonical relative differential
square maps in arbitrary universe `u`. It is independent of the affine
base-change theorem and of the unconditional arbitrary-scheme theorem.
It imports the canonical maps, the open-immersion proposition, the
published module-sheaf stalk comparison, and `Modules.PullbackUnitProofs`
for its general adjunction helper. The open-immersion proposition remains
an explicit assumption only in the final transport lemma.

`relativeDifferentialsSquarePushforwardMap_app_D` computes the square map's
adjoint on universal differentials. Applying the universal property of
relative differentials on local sections then proves composition of these
pushforward maps. The published
`Langlands.Scheme.Modules.homEquiv_conjugate` and a private composite-adjunction
calculation transfer this identity to `relativeDifferentialsSquareMap_comp`,
including the actual `pullbackComp` comparison. The composite calculation
follows the published `RelativeDifferentialsMapsCoherence` implementation
with general squares in place of fixed-base maps.

`relativeDifferentialsSquareMap_congr` identifies square maps when the two
horizontal arrows are equal, using `pullbackCongr`; the proof substitutes
the equalities and simplifies. `relativeDifferentials_isIso_of_openCover_pullback`
detects invertibility after pullback along every map of any scheme open
cover. Its proof uses the published stalk criterion, the natural isomorphism
between restriction and pullback along an open immersion, and invariance of
stalk maps under restriction.

`relativeDifferentialsBaseChangeMap_isIso_of_square` transports invertibility
from a square on an isomorphic model of the categorical fiber product. It
assumes the open-immersion comparison proposition, an isomorphism to the
fiber product with the two specified projection identities, and invertibility
of the square map on the model. Composition and congruence identify the
pulled-back canonical map. The open-immersion proposition makes the side
comparison invertible; cancellation and the singleton isomorphism cover
then give invertibility of the original canonical base-change map.

This helper contains no proof or assumption of the arbitrary-scheme
base-change theorem and no assumption of affine base change. Its provenance
is an internal derivation from the published concrete canonical maps and
Mathlib's adjunction and cover APIs. It supports the affine-local route of
Stacks Project Lemma 29.33.10 (01V0), with the map of Lemma 29.33.8 (01UV),
in registered source `stacks-relative-differentials-internal-hom-2026-10-21`,
retained file `01UM.html`, lines 321–371. The implemented route is described
above. Worker 208 authored these calculations; Worker 538 reused the module
with the affine proof. The separate parent proof imports this helper and the
affine theorem rather than redeclaring their results.

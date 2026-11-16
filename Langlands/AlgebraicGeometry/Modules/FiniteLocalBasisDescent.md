# Descent of finite local bases

This internal supporting construction proves that finite local bases descend
along an fppf covering morphism of schemes, in an arbitrary universe `u`.
For `p : X ⟶ Y` flat, locally of finite presentation and surjective, and an
actual module sheaf `M` on `Y`, finite local bases of the ordinary pullback
`p* M` imply finite local bases of `M`. The predicate is the existing
`Langlands.Scheme.Modules.HasFiniteLocalBasis`: one local generator datum
whose generator maps are isomorphisms and whose generator index types are finite.
It is also the predicate used by `RelativeUnipotent.IsFiniteLocallyFree`.
There is no affine, noetherian, connected, nonempty-base or constant-rank
hypothesis.

`finiteLocalBasisOfPullbackFppf` selects such actual local generator data,
together with proofs of both properties. It applies classical choice to the
proved reflection theorem; it does not prescribe a particular open cover or
preserve the supplied cover.

`finiteFreeStalkIso` identifies the actual stalk of a finite free sheaf with
the corresponding finite power of the actual local ring. The stalk functor
preserves coproducts by its published adjunction. A finite index type is first
enumerated by `Fin` so the coproduct-to-product comparison respects the
arbitrary universe, and the published linear unit-stalk comparison acts on each
coordinate.

`isFinitePresentation_of_hasFiniteLocalBasis` uses the local bases as generators
and the empty relation families. `flat_stalk_of_hasFiniteLocalBasis` chooses a
basis chart containing the point, restricts the generators to its actual open
subscheme, and applies the finite free stalk comparison. Flatness passes from
that local ring to the original local ring along the open immersion's flat
stalk map, and the linear restriction-stalk comparison identifies the result
with the original stalk.

`restrictStalkFiniteFreeEquiv` transports a finite power chart on a stalk to
an open restriction. It combines the actual additive stalk comparison with
the actual local-ring isomorphism on every coordinate; its scalar-compatibility
proof uses the linear restriction-stalk comparison and multiplicativity of that
ring isomorphism.

`exists_freeNeighborhood_of_spec_stalk_basis` spreads a finite basis of an
actual affine stalk when the affine section module is finitely presented. The
quasi-coherent comparison with the sheaf associated to its actual affine section
module transfers the basis to a localization. Mathlib's finite-presentation
basis-spreading theorem supplies a principal neighborhood and a localized
basis. `DerivedSections.freeChartOfLocalizedBasis` realizes this as an actual
free sheaf chart. `exists_freeNeighborhood_of_stalk_basis` first chooses a
spectrum chart for a locally finitely presented module, applies the preceding
result, and transfers the resulting chart to the open image of the composite
open immersion using its canonical isomorphism with that image.

`hasFiniteLocalBasis_of_finitePresentation_flatStalks` uses finite presentation
of each actual stalk and freeness of finite flat modules over local rings.
It chooses a finite basis at each point, spreads it by the preceding theorem,
and assembles the varying finite index types with
`freeNeighborhoodGenerators`. Each chart may have its own rank, including zero.
This construction also applies on an empty scheme, with no chosen point needed.

Finally, `hasFiniteLocalBasis_of_pullback_fppf` descends finite presentation
using the published `isFinitePresentation_of_pullback_fppf`. For each point of
`Y`, surjectivity chooses a point above it. The actual pullback stalk is the
tensor product of the original stalk with the new local ring. The new stalk
is flat by its finite local bases; scalar restriction through the flat stalk
map makes that tensor product flat over the original local ring. Faithful
flatness of the local ring map reflects flatness to the original stalk via
`RelativeFlatnessDescent.flat_of_faithfullyFlat_tensor`. The preceding
finite-presentation and flat-stalk criterion then gives finite local bases.

The provenance is entirely internal and derived: the ingredients are the
Library's actual stalk and restriction comparisons, finite-presentation descent,
faithful stalk flatness and free-chart constructions, together with Mathlib's
finite flat local freeness and finite-presentation localization theorems.
This unit supplies a module-sheaf reflection step for the relative radical
filtration task. Construction of a descent datum, its effective module sheaf,
and descent of natural group-point/section equivalences remain separate
obligations; the full radical-filtration statement is not asserted here.

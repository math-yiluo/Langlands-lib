# Comparing the relative Picard automorphism presheaf

This internal construction compares the full automorphism presheaf formed
directly from the actual relative Picard pseudofunctor with the ordinary
pullback construction in `Picard.SmoothAutomorphisms`. Its provenance is the
published actual line-bundle pseudofunctor and a generic coherence comparison;
it invokes no external representability theorem.

For `f : X → S`, a test `T : Over S`, and an actual line bundle `L` on
`(relativeSpace f).obj T`, `relativeSliceAutomorphismPresheaf f T L` is
`(relative f).presheafHom (Core.mk L) (Core.mk L)`, precomposed with the
opposite of `T.iteratedSliceBackward` and postcomposed with `uliftFunctor`.
Thus its domain is every scheme over `T.left`. Its values consist of actual
bundle automorphisms, with the composition comparisons prescribed by the
relative pseudofunctor. The universe lift changes no morphism data.

`sliceRelativeAutomorphismPresheafIso` naturally identifies the ordinary
slice construction with this direct relative construction. The implemented
comparison specializes
`Langlands.CategoryTheory.presheafHomPrecompositionIso` to `relativeSpace f`
and the ordinary Picard pseudofunctor, takes its inverse, and whisks it by
the iterated-slice functor and the value lift. The definition of `relative f`
is precisely the pseudofunctor precomposition appearing there. In particular,
the comparison includes every restriction map and both pullback composition
comparisons; it does not compare just the values on individual schemes.

`relativeSliceUnitsAutomorphismPresheafIso` composes that comparison with
`sliceUnitsAutomorphismPresheafIso`. Its source is the restriction of the
actual `RelativeGlobalUnits.presheaf f` along `Over.map T.hom`. It therefore
identifies units of global functions on each actual relative test with the
automorphisms computed by the actual relative pseudofunctor, naturally over
the full slice.

`HasSmoothRelativeAutomorphismSchemes f` requires, for every such `T` and `L`,
an actual `G : Over T.left`, a natural isomorphism from its lifted scheme
Yoneda presheaf to `relativeSliceAutomorphismPresheaf f T L`, and ordinary
scheme smoothness of `G.hom`.

`HasSmoothUnitSchemes.hasSmoothRelativeAutomorphismSchemes` transports any
smooth scheme representative for relative units along the natural scalar
comparison, retaining the same `G` and smoothness proof. The converse in
`hasSmoothRelativeAutomorphismSchemes_iff_hasSmoothUnitSchemes` specializes
the relative condition to the actual trivial line bundle and composes with
the inverse scalar comparison. The trivial bundle exists on every relative
scheme, including an empty one.

No hypotheses on `f`, on the base, or on test schemes are imposed. In
particular this comparison retains nonreduced and non-quasi-compact tests.
The module proves an equivalence of representation conditions; it supplies
no existence proof for either condition, no stack quotient, and no Picard
class-sheaf representability theorem.

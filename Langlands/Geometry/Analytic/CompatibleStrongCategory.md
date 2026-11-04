# Category of original compatible strong atlas maps

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
printed p. 18 (zero-based PDF index 14), Definition 1.2.7 and the
composition construction following Proposition 1.2.8, introduces strong
morphisms and their category. The registered original is
`berkovich-1993-etale-cohomology`, PDF SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The present category uses the explicit local compatibility convention of
`CompatibleStrongMaps`, whose equivalence with coefficient coherence and
agreement on arbitrary actual source overlaps are already proved.
The source does not separately spell out that compatibility law; this
module states internal categorical consequences of the implemented law.

The morphisms retain the supplied continuous map and every admissible
original bounded algebra pullback, its chart equation and its restriction
equations. Their additional law is the full bounded equation on each
constructed inverse-image affinoid domain of a common target subchart.
The objects retain actual topological spaces and atlases of spectra of
finite positive-polyradius Tate quotient algebras, with the existing full
affinoid-domain representations. No analytic output is assumed.

`CompatibleStrongHom.ext_of_pullback` determines an entire compatible map
from its continuous map and one complete admissible bounded pullback per
original source chart. Its proof applies `StrongHom.ext_of_coherent` to
the two original coherence laws, so it preserves algebra-map information
that is not detected by spectrum points alone.

The identity uses the original atlas restrictions. Composition uses the
actual bounded gluing construction in `CoherentStrongComposition`.
`id_comp` and `comp_id` compute one admissible chain using the same source
or target index twice, and then apply the bounded identity laws.
`comp_assoc` chooses one admissible three-map chain for each source,
recovers its complete bounded pullbacks in both parenthesizations and
applies associativity of bounded algebra maps. Full coherent
extensionality then proves equality of every original pullback, including
targets unrelated to the chain used to compute the composite.

`CompatibleAtlasPresentation` wraps exactly the existing
`AffinoidAtlasPresentation` data to carry this category. The original type
already has the category of maps with monotone chosen target charts from
`ChosenAtlasMorphisms`; the wrapper keeps the two morphism types distinct
and adds no geometric assumptions or replacement space data.
`spaceFunctor` retains the literal ambient topological spaces and
continuous maps.

`SaturatedAtlasPresentation.compatibleFunctor` includes the existing
saturated strong-map category in this category. Every supplied saturated
strong map acquires the compatibility proof from its saturated source;
the entire bounded-map family is unchanged. The identity and composition
equations use equality of complete records, with proof irrelevance for
the two derivations of the restriction laws. The functor is full and
faithful: the inverse on each Hom takes `toStrongHom`, and the proof field
does not change equality. Its composite with the new `spaceFunctor` is
literally the existing saturated `spaceFunctor`.

All presentations share the existing universe parameters `u`, `v`, `w`
over a complete ultrametric normed field; nontrivial valuation is not
required. Neither saturation, a directed chart family nor a greatest
chart is required for the original compatible category. This focused
unit constructs the category and its actual saturated inclusion.
The saturation functor, analytic localization comparisons, etale sites
and equivariant constructions remain subsequent work.

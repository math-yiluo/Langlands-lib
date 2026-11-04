# Model Hom comparison along filtered algebra diagrams

This derived target specializes Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), printed pp. 5–6,
Theorem 3.4(1), to the explicit actual objects and comparison of
`SchemeLimitModelSpectrum`. The source asserts the natural Hom-colimit
bijection for two finitely presented models over an initial stage of a
directed ring system. The present target permits a small filtered
category of algebras over the fixed model ring and retains the weaker
separate equality and factorization hypotheses of
`ModelHomColimitComparison`.

All types share an arbitrary universe `u`. Fix a commutative ring `R`, a
small filtered category `J`, a functor `F : J ⥤ CommAlgCat R`, and an
actual algebra cocone `c` with `IsColimit c`. Let `X` and `Y` be arbitrary
schemes over `Spec R`. They are not required to be affine or separated.
The assertion `SpectrumModelHomColimitComparison` has three clauses.

1. If the structural morphism of `X` is quasi-compact and that of `Y`
   is locally of finite type, the actual map
   `spectrumHomColimitMap R F c X Y` is injective.
2. If the structural morphism of `X` is quasi-compact and
   quasi-separated and that of `Y` is locally of finite presentation,
   that same map is surjective.
3. Under the hypotheses of clause 2, the map is bijective and the
   actual cocone `spectrumHomCocone R F c X Y` has an `IsColimit`
   witness, expressed as `Nonempty` so that the target is a proposition.

The domain is the concrete quotient of the disjoint union of the
relative Hom sets between the pullbacks of `X` and `Y` to
`Spec (F.obj j)`, indexed by the original category `J`. The target is
the relative Hom set between their pullbacks to `Spec c.pt`.
The map is actual base change on every stage representative.
No scheme-limit witness, comparison bijection or categorical universal
property is supplied as data. The scheme-limit witness needed for a
proof is constructed from `IsColimit c` by `spectrumConeIsLimit`.

The provenance is derived. Applying the generic scheme-diagram target
to the actual opposite-spectrum diagram gives the same map after the
proved quotient equivalence `spectrumHomColimitEquiv`. That equivalence
preserves each stage representative, and `spectrumHomColimitMap_eq`
proves the comparison square. Filteredness makes the opposite index
cofiltered and supplies the connectedness needed for the scheme-limit
adapter. The actual type-cocone universal-property criterion gives the
last conclusion. These are the proposed proof dependencies, not assumed
fields of the target.

For Conrad's finitely presented models, finite presentation means local
finite presentation together with quasi-compactness and
quasi-separatedness. Those source hypotheses imply the hypotheses of
clause 3. Passing to the tail after the initial ring stage gives the
fixed `R`-algebra system used here; this target does not construct that
tail or its colimit identification. It also does not assert initial
model existence, prescribed-isomorphism or property descent,
arithmetic realizations, or any topology. This file defines the
proposition; a separate proof unit must establish it.

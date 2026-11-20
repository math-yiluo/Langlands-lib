# Detection of analytic morphisms along étale covers

`EtaleCoverHomExtStatement` says that a jointly surjective family of
localized étale maps detects equality of complete localized analytic
morphisms. It applies to any target in the localized category, with
independent field, space and cover-index universes. The theorem
`etaleCoverHomExt` proves it for complete ultrametric normed fields.

For strong morphisms between constructed saturations, joint surjectivity
gives equality of the two base maps.

For an admissible source and target chart, choose the finite étale
refinements of the source chart. The spectrum-surjective flat map on each
refined chart is faithfully flat, so its coefficient map is injective.
The full-recognition composition
formula identifies the two composites with the pullbacks of the given
equal strong maps. Injectivity cancels the finite étale map. The canonical
contained-chart comparisons turn the resulting coefficient equalities into
equality over a finite domain cover of the source chart. Finite-cover
separation gives equality of the chart pullbacks and hence of the full
strong maps.

For localized morphisms, choose a common strong source refinement for the
two arrows and transport the cover along the source isomorphism. Each
cover arrow has a strong étale representative with the resulting fixed
target, obtained by taking its fraction numerator and replacing the source
by its constructed saturation. The cover remains jointly surjective under
the source homeomorphisms. Localization is faithful on strong maps, so the
localized equalities give equalities of the actual strong composites.
The strong detection theorem and the comparison isomorphisms then give
the localized equality.

This is an internal consequence of finite chart refinements, faithful
flatness detected by the bounded-spectrum ideal criterion, the existing
recognized-pair composition and the finite-domain separation theorem.

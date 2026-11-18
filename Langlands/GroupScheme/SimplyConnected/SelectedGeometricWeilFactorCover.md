# Actual Weil covers for a selected geometric factor

This derived internal specialization fixes a geometric almost-simple factor
and retains its actual stabilizer-field descent model throughout the Weil
presentation and covering product.

For an almost-simple ground-field group `A`, a simply connected almost-simple
product presentation `D` of `A_L` over a separably closed Galois extension, and
a chosen factor index `j`, `stabilizerEmbeddingProductIso` is the published
embedding-product comparison for `E = D.factorStabilizerField j` and
`H = (D.factorStabilizerDescent j).1`. The descent lemma retains its compatibility
with every ground-field Galois automorphism and the original embedding-coordinate
transport. Composing it with the original conjugate-factor product and applying
the published compatible descent construction gives `stabilizerWeilIso :
A ≅ Res(H)`. The base-change formula identifies its inverse exactly with those
two original geometric comparison maps.

For a prescribed almost-simple ground-field factor `Dk.factor i` of a simply
connected `C`, `weilFactorAtGeometricIndex` uses precisely this Weil presentation
in the actual covering product. Its extension and group are definitionally
`Dgeo.factorStabilizerField j` and `(Dgeo.factorStabilizerDescent j).1`; the
projection lemmas are reflexive equalities. The construction retains the original
insertion, actual simply connected complement, actual central cover and anisotropy
comparison from `PrescribedWeilFactorCover`.

No Cartan-component selection or root/star identification is asserted by this
unit. Those geometric comparisons can now use a fixed factor and its field
without substituting an arbitrary existential Weil witness.

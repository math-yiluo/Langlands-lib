# Transport of actual Picard atlases from etale to fppf classes

Author: Worker 509.

This is internal derived support for the actual Picard-sheaf
representability argument. It uses the published canonical comparison in
`Picard.EtaleFppfSheafComparison` and the accompanying generic atlas
transport lemmas. The base scheme `S : Scheme.{u}`, source scheme `X`,
and morphism `f : X → S` are arbitrary.

`etaleFppfClassPresheafIso f hF` forgets the sheaf structure on the
published `etaleFppfClassSheafIso`. Its hypothesis `hF` explicitly says
that the ordinary etale class sheaf presheaf is a sheaf for the entire
fppf topology over `S`. Its source and target are exactly
`RelativePicard.etaleClassSheafPresheaf f` and
`RelativePicard.classSheafPresheaf f`, with values in `Type (u+1)`.

`etaleFppfClassPresheafIso_hom` identifies its forward map with the
published canonical `etaleToFppfClassSheaf f`, on underlying
presheaves. `toEtaleClassSheaf_etaleFppfClassPresheafIso_hom` proves that
the composite with the ordinary-class-to-etale-sheaf unit is the
ordinary-class-to-fppf-sheaf unit. Thus the transport retains the
specified canonical comparison and the classes of actual bundles.

`classSheaf_algebraicSpace_of_etale_atlas` takes the explicit hypothesis
`hF`, scheme representability of the etale class sheaf's diagonal, and
an actual etale-surjective scheme atlas locally of finite type over `S`.
It concludes that the actual fppf Picard class sheaf is an algebraic
space and supplies an actual etale-surjective scheme atlas locally of
finite type over `S`. The proof transports the diagonal through the
full natural isomorphism, retains the input atlas scheme, and composes
its atlas transformation with the canonical comparison.

The proof tests geometry on complete presheaf pullbacks, as required by
the original geometric predicates. It retains every scheme in `Over S`
and every sheaf section, including sections with no global bundle
representative, with no reduction to affine or field-valued tests.
There are no properness, field, reducedness, compactness, or section
hypotheses in this conditional result.

This module does not prove fppf descent of etale classes, existence of
the input atlas, or closedness of the diagonal. Those remain separate
inputs to the final proper-field theorem. It does not prove the exact
`FieldPicardSheafAlgebraicSpaceStatement`.

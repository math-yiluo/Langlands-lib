# Relative centralizers of fibrewise regular coordinate cocharacters

This internal result combines the full fibrewise coordinate root datum,
the existing regular-cocharacter field comparison and the residue-fibre
reconstruction of dynamic centralizers. It is a derived construction with
no separate external-source translation.

Let `G` be reductive over `Spec R`, with `R` any commutative ring. Supply
a map `i` from the coordinate split torus indexed by a finite type `I`,
maximal on every residue fibre, a full common fibrewise root datum `P`,
and an exponent vector `n` whose integer pairing with every root of `P`
is nonzero. The cocharacter is exactly `AffineRegularBorel.cocharacter i n`.
The field and residue comparisons do not assume `i` monic over the base;
the global comparison and isomorphism construction do.

`centralizer_eq_range_field` identifies the whole dynamic centralizer
of the actual pulled-back cocharacter with the range of the actual
pullback of `i`, on every test scheme over any supplied field algebra.
`isRegular_field` gives regularity from the full datum. Fibrewise torus
maximality gives maximality over that field. The existing theorem
`centralizer_comp_eq_range_of_isRegular` identifies the centralizer
with the range of the coordinate torus map there. Its canonical source
isomorphism does not change the range, yielding the actual pullback map.

`centralizer_eq_range_residue` uses the ring homomorphism corresponding
to each residue-field point to specialize this comparison. Then
`centralizer_eq_range_of_mono` applies
`Dynamic.centralizer_eq_range_of_residueFibres`: both the coordinate
torus and the ambient group are smooth, the ambient group is affine,
and the supplied monicity makes the torus a representative of its range.
The conclusion is an equality of subgroup functors on every test scheme
over the original base.

Finally, `torusToCentralizerIso` gives the canonical isomorphism from the
coordinate torus to any supplied representative `j` of this centralizer.
It uses uniqueness of monic representatives of the same subgroup functor.
`torusToCentralizerIso_hom_comp` states that this isomorphism followed by `j`
is the original map `i`.

The results hold in every universe and impose no noetherian hypothesis.
The common full root datum and the regular exponent vector remain
explicit inputs. The existing `CoordinateRootDatum.regularExponent`
and its specification supply such a vector for each finite root datum.
These results supply centralizer comparisons; they do not assert
closedness of an ambient group homomorphism.

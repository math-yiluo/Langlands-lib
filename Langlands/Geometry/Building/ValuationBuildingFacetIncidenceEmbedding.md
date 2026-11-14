# Facet incidence along a compatible building map

This internal construction extends `ValuationBuildingFacetEmbedding`. It uses
the same source local-field valuation building `B`, integer-valued target
building `C` over an arbitrary field, rational-point homomorphism `φ`, point map
`e`, and real affine apartment map `a`. All fields and group schemes are at the
same arbitrary universe `u`.

The hypotheses are exactly:

- `e (g • x) = φ g • e x`;
- `e (B.apartmentMap x) = C.apartmentMap (a x)`;
- `a ⁻¹' facet C.affineRoots (a x) = facet B.affineRoots x` for every `x`;
- the source apartment axioms `hD`;
- common source apartments `hcommon`.

No injectivity or surjectivity of `e`, `a`, or `φ` is assumed. The apartment
injections used in the proof follow from the connected reductivity and maximal
split torus included in the building data.

For a source facet `Fc`, let `facetLift Fc` denote the full target facet
constructed in `ValuationBuildingFacetEmbedding`. This module proves:

- the preimage of the combinatorial closure of `facetLift Fc` is the
  combinatorial closure of `Fc`;
- the image of the latter closure is the intersection of the former closure
  with `range e`;
- `C.FacetPrecedes (facetLift Fc) (facetLift Fd)` holds exactly when
  `FacetPrecedes B Fc Fd` holds.

`facetRangeOrderIso` equips the previously constructed `facetRangeEquiv` with
this exact incidence comparison. Its source order is the published explicit
`buildingFacetPartialOrder` on source facets, using the supplied apartment
axioms and the proved apartment injection. Its target order is the restriction
of `C.buildingFacetPartialOrder` to the full facets meeting `range e`.
No global order instance is installed. The forward map remains `facetLift`,
as recorded by `facetRangeOrderIso_val`.

The proof first applies
`AffineRootSystem.preimage_facetClosure_of_preimage_facet` from
`FacetClosurePullback`. Thus the supplied open-facet pullback also holds for
closed facets. Equivariance and apartment compatibility put image points in a
common target chart, where the published exact closed-facet chart formula and
target apartment injection identify their coordinates. Common source apartments
and the corresponding source formula then globalize the comparison. The
image-intersection equality follows from the preimage equality. Finally,
membership in a closed facet is equivalent to incidence of the unique
containing facet, giving preservation and reflection of incidence.

This is derived from the published facet partitions, closure formulas, and
incidence orders, together with the supplied comparison hypotheses. In the
unramified application those hypotheses are supplied by the existing target
statement, and its building axiom supplies common apartments. Identifying
`range e` with a fixed locus yields the corresponding geometric fixed-facet
interpretation. The special-fibre parabolic correspondence is a further
obligation and is not asserted here.

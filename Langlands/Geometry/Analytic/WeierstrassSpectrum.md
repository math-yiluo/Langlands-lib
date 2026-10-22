# Proof of spectrum identification for a Weierstrass presentation

Author: Worker 36.

`WeierstrassPresentation.spectrumIdentification` proves the separate
`SpectrumIdentificationStatement`. Its three conclusions are dense range
of the constructed base map, equality of its spectrum image with the
unit-radius norm locus, and a closed embedding of spectra.

For a base point x in the locus, evaluate the base algebra in its actual
completed residue field from `Spectrum.ResidueField`. The evaluation norm
equals x. Multiplicativity of the field norm makes the powers of every
selected image bounded by one. `residuePowerBound` supplies these bounds
to the constructed bounded extension `liftFromBase`. Pulling back the
field norm along that extension defines `pointLift`. Its base restriction
equals x by the extension formula and exact residue-field norm evaluation.
Together with forward inclusion, this proves `range_comap_baseMap`.

The base algebra has dense image in the Weierstrass quotient. The
base-map formula places each old coordinate in its image, and the
imposed equations do the same for each new coordinate. Every scalar
monomial therefore belongs to the image subalgebra. Convergent Tate
monomial expansions, mapped through the continuous quotient projection,
place every quotient element in its closure. Surjectivity of that
projection completes the proof of `denseRange_baseMap`.

Every spectrum seminorm is continuous on the quotient algebra: it is
the norm of the constructed bounded evaluation in its completed residue
field. Two spectrum points with equal base restrictions agree on a dense
set, hence everywhere. This proves injectivity of the spectrum map.
Its continuity, together with compactness of the source spectrum and
Hausdorffness of the target spectrum, gives `comap_baseMap_closedEmbedding`.
The closing theorem assembles these three results.

The Statement Markdown records the source conventions and derived scope.
The completed-residue-field step uses the construction following
Exercise 1.2.4, p.4, of Berkovich's Trieste 2009 notes. The proof constructs
the relevant fields and maps; it assumes no realizing field or inverse
spectrum map. It does not derive power bounds for arbitrary affinoid
targets from spectrum-image containment, and therefore does not establish
the full analytic-domain universal property, a structure sheaf, or a site.

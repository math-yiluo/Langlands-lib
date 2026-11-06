# Good neighbourhoods from a relative torus maximal at a field point

This internal module constructs an actual good original-base open from a
supplied closed relative standard torus whose actual fibre is maximal at a
field-valued point. The base is any scheme in universe `u`; the field need not
be algebraically closed. The ambient group is smooth and affine. The image
of the field point belongs to the unchanged reductive geometric
identity-component locus. The universal algebraically closed maximal-torus
centralizer, forward reflection, root reducedness and root-line statements
remain explicit inputs. No torus-lifting or full openness theorem is asserted.

`isMaximalTorus_of_baseChange_comp` proves the reverse of the published
composite-fibre maximality transport. It uses the actual naturality equation
for pullback composition and source and ambient isomorphism invariance.
`splitTorus.isMaximalTorus_baseChangedHom_comp` includes the canonical
standard-torus coordinates in this transport.
`splitTorus.isMaximalTorus_fieldPoint_extension` uses the published universal
maximal-torus field-extension proof and the same actual comparisons to show
that a maximal standard torus at a field-valued point remains maximal after
composing that point with any field extension. The original smooth affine
ambient group ensures that its actual field pullback has these properties.

`splitTorus.identityComponentReductiveNeighbourhood_of_maximal_fieldPoint_extension`
handles an affine base. It passes to the algebraic closure of the supplied
field and preserves the supplied torus's maximality. The spectra of both
fields have a single point, so the composite point has the same original-base
image. The published zero-weight comparison and field-input constructor
then give an actual open containing that image and contained in the original
locus. No comparison of independently chosen algebraic closures is required.

`splitTorus.identityComponentReductiveNeighbourhood_of_maximal_fieldPoint_overScheme`
handles any base scheme. It chooses the standard affine-cover chart
containing the field point's image. The entire range of the field point lies
in that chart, so the open-immersion lift gives an actual factorization
through it. The relative torus inclusion is pulled back with its canonical
standard-torus source coordinates; it stays closed and its field-point fibre
stays maximal by the composite comparison. The affine constructor gives a
good open in the chart. Its actual image under the open immersion is the
required original-base open, by the unchanged locus's base-change identity.

The provenance is internal composition of actual pullback naturality,
maximality transport under isomorphisms, the published maximal-torus
field-extension theorem, standard affine-open covers and open-immersion
factorization, and the existing good-open construction and open-map descent.
Every universal field-structure premise and the supplied relative torus
remain explicit. All constructions are uniform in arbitrary universe `u`,
with no characteristic, Noetherian or connected-ambient-fibre restriction.

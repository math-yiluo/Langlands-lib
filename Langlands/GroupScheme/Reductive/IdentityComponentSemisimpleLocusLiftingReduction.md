# Semisimple-locus openness from affine torus neighbourhoods

This internal derived reduction uses the published relative split-torus
lifting statement and an explicit affine local-neighbourhood premise. It proves
`IdentityComponentSemisimpleLocusOpenStatement` in every universe under
these two premises; the affine premise is not assumed to hold without proof here.

The affine premise asks for an open neighbourhood of a semisimple geometric
identity-component fibre at which a supplied actual closed standard torus is
self-centralizing. For an algebraically closed field-valued point with maximal
torus fibre, the published maximal-torus centralizer theorem supplies this
self-centralizing condition. For an arbitrary field-valued point, extend to its
algebraic closure; maximality persists and the image point is unchanged. For a
general base, lift that field point through an affine open chart, transport its
standard torus and maximality using the actual base-change isomorphisms, and
descend the resulting open by its open image.

A split presentation of any split torus reduces to standard coordinates. The
relative split-torus lifting statement lifts a specified maximal split torus in
the residue fibre to an etale neighbourhood, retaining its recovery isomorphism.
The published lifting-recovery maximality lemma supplies the needed maximal
field fibre. The semisimple locus commutes with arbitrary base change, so the
good open descends by the etale projection.

Finally choose a split maximal torus after a finite Galois residue extension,
realize that extension by the published etale residue neighbourhood, apply the
preceding construction, and descend once more. Every semisimple point therefore
has an open neighbourhood in the same locus. The topological neighbourhood
criterion gives the exact arbitrary-base openness conclusion. This follows the
existing proved reductive-locus lifting assembly with the semisimple locus and
its actual transport comparisons; it adds no field or base hypothesis.

# The connected-fibre locus and structural limit descent

This internally derived supporting unit proves descent of geometrically
connected nonempty structural fibres along arbitrary cofiltered limits of
affine schemes. The space at the specified stage is quasi-separated and has
a quasi-compact locally finitely presented etale surjective atlas.

`connectedFibreLocus X` is the set of ordinary base points where the canonical
geometric fibre component count is one. The final limit argument uses this
named locus.

The first criterion extends the existing spectrum-base criterion to the
published `schemeGeometricFibreComponentCount` over an arbitrary scheme S.
One component means nonempty connectedness. The forward direction tests the
canonical algebraic closure of each residue field; the converse compares
every algebraically closed field test with that canonical fibre, using the
atlas and the existing geometric component equivalence. The actual
structural fibre comparison then gives the stated morphism predicate.

The arbitrary-base-change criterion uses the existing component-count
base-change theorem and preservation of the finite-presentation atlas.
Thus good fibres after a scheme base change are exactly the ordinary points
mapping into the original count-one locus.

Constructibility over affine S follows from the already derived arbitrary-ring
constructibility reduction, quasi-separated model-existence reduction and
proved etale-equivalence-relation model existence. These existing results
provide the ring-base theorem without an extra premise. The proof applies it
after base change along the inverse of S's canonical spectrum isomorphism.
The count-base-change identity identifies the required locus as the inverse
image along that isomorphism. Quasi-separatedness and the atlas have exactly
their published relative meanings.

Finally the count-one locus is constructible, so the existing
`ConstructibleAffineLimit` theorem detects whether its inverse image is the
whole limit at a finite incoming stage. The base-change criterion converts
this equivalence into the stated structural connected-fibre theorem.
All diagram, cone and limit data are actual data, with arbitrary cofiltered
index categories in the declared universe.

The provenance is composition of the cited Library constructions and proofs;
no additional literature assertion or general morphism limit-descent premise
is used. The conclusion concerns structural morphisms of base-changed spaces.
The full eight-property statement and descent for an arbitrary morphism remain
obligations of the host task.

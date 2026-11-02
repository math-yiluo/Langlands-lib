# Ring covering data from a finite affine scheme cover

`finiteEffectiveCover` constructs ring covering data from an actual finite
surjective cartesian morphism of étale equivalence relations whose covering
relation has an affine quotient. The base object and relation schemes are
affine. All objects have the arbitrary universe `u`.

The source scheme of the cover is affine because its morphism to the affine
base is finite. Its relation scheme is affine by the pullback presentation
of its affine quotient. The source-cartesian scheme square supplies the
actual tensor coordinates and their target compatibility. The affine
quotient supplies faithful flatness over the actual invariant ring and
its effective tensor-square presentation. The finite morphism gives the
finite module of global sections. Surjectivity of the map on prime spectra
follows by transporting scheme surjectivity along the canonical affine
spectrum isomorphisms.

Provenance is internal affine duality, using the existing affine-coordinate
and affine-quotient-presentation results and Mathlib's finite-morphism and
surjectivity APIs. The cover structure is Worker 239's interface. This
constructor neither assumes nor establishes the final acyclicity theorem.

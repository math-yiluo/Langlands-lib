# Actual root supports of field fibres over a local ring

Let `R` be an arbitrary commutative local ring, `G` an actual smooth affine
 group scheme over `Spec R`, and `i` an actual homomorphism from the coordinate
 split torus with finite index `I` to `G`. No reductivity, injectivity or
 maximality hypothesis is imposed on `i`. The fields and ring range over the
 arbitrary common universe `u`.

The complete relative adjoint weight-rank profile is constant on `Spec R`.
 The implementation uses the published local constancy of that profile.
 Every prime specializes to the closed point, so the open fibre of the
 profile through the closed point contains every prime. In particular,
 the existing integral-coordinate root support of the actual geometric
 identity components is the same at any two primes.

For any two supplied fields `k,l` with their supplied `R`-algebra structures,
 the actual weight spaces for each fixed integral exponent have equal
 dimensions on the two actual pullback groups. The torus maps here are the
 canonical coordinate maps `baseChangeHom`, using the inverse of the
 split-torus base-change isomorphism followed by base change of `i`.
 The proof identifies each weight dimension with the rank of its actual
 relative weight summand at the image of the field-valued point and applies
 constancy. This applies to all field-valued points, with no requirement
 that the coefficient maps be local.

`fieldCharacterEquiv` compares the entire actual character lattices of
 the two coordinate tori through their integral-coordinate equivalences.
 `fieldRootsEquiv` restricts this map to the actual roots of the two torus
 maps. Root membership is equivalent to a nonzero exponent with nonzero
 weight dimension; the proved dimension equality therefore gives the
 restriction. The formula theorems state both the underlying actual
 character and the equality of its integral coordinates.

The provenance is internal: the proof combines the published actual
 relative-weight finite projectivity, locally constant ranks and arbitrary
 scalar-extension comparison with Mathlib's specialization property of
 the spectrum of a local ring. This is a root-support comparison only.
 It constructs no coroot comparison, full root-datum equivalence or
 integral group isomorphism. Those remain separate obligations for the
 strict-Henselian generic-isomorphism theorem, including the central
 lattice directions.

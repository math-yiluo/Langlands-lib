# Affine-valued maps from a proper connected reduced scheme

This internal module extends the published algebraically closed field argument
in `GlobalFunctionsFieldProof` from smooth geometrically connected schemes to
proper connected reduced schemes. It proves that the actual structure
morphism's map on global sections is an isomorphism. Properness makes the
section algebra integral over the base field. Reducedness and connectedness,
via the dense canonical map to the spectrum of global sections, let the
published elementary scalar-surjectivity lemma show that every global function
is a base-field constant. Field injectivity supplies the other direction.

For an affine target, equality of maps is detected by global sections. If the
source's structure map induces an isomorphism on global sections and has a
specified section, composing with that section shows that every map is its
constant value there. The specialized theorem applies this to proper connected
reduced schemes over an algebraically closed field.

`properConnectedAffineHomEquiv` packages the resulting actual bijection of
morphisms over the base field with rational points of any affine target.
Evaluation at the specified source point is inverse to the constant-map
construction. The specified point is explicit; no section is assumed to exist
without being supplied.

The provenance is the published `GlobalFunctionsFieldProof` and Mathlib's
integrality and affine-target extensionality theorems. No additional geometric
result is assumed. An intended application is a homogeneous quotient's
affine-valued orbit map in the Borel normalizer proof. This module itself neither
constructs that quotient nor proves its properness or any normalizer theorem.

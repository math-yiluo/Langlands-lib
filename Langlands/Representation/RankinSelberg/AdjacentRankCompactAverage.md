# Finite vector integration for adjacent-rank compact-orbit sections

This internal construction implements the inner vector integral of JPSS
Section 6.1, formula (10), printed page 430 of the registered original
`jpss-1983-rankin-selberg`. It is not yet a section of the normalized induction.

Here `K` is a Hausdorff topological field with continuous field operations,
`n` is any natural number, and `GL_n(K)` carries a measurable space in which
open sets are measurable. The chosen measure `μ` is finite on compact sets.
These are the measure assumptions throughout the integral, its functional
comparison and its linearity laws; Haar invariance and global sigma-finiteness
are not required.

The tests form the submodule of rectangular Schwartz functions whose entire
topological support has full row rank. For such a test and a smooth representation
on an arbitrary algebraic complex module, the function

`h ↦ Φ([h,0]g) ξ(h) ρ(h⁻¹)v`

is locally constant and compactly supported. The scalar weight `ξ` is an actual
group character with explicitly supplied local constancy. Compactness follows
from `AdjacentRankCompactOrbit`; smoothness of the representation gives local
constancy of its orbit map. Since `μ` is finite on compact sets, compact
topological support bounds the measure of the nonzero support and gives
finite-measure support. The published algebraic integration API therefore
defines this vector integral against `μ` by a finite fiber sum, without placing
a norm or topology on the module.

Every algebraic functional takes this vector integral to the corresponding
complex Bochner integral. The construction is additive and homogeneous in the
representation vector. These are finite-sum identities; continuity of the
functional is not required. Finite-measure support supplies the hypotheses of
the imported `integral_linearMap` and `integral_eq_bochner` comparison laws and
the `integral_add` and `integral_smul` vector laws.

Lower covariance, smoothness in the ambient group variable, tensor linearity,
spanning and the Jacquet identity remain to be proved.

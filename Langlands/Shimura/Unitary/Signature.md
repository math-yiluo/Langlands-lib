# Hermitian adjoints and archimedean signatures

`AlgebraInvolution.adjoint` constructs the involution
`a ↦ h⁻¹ σ(a) h` from an actual invertible self-adjoint algebra element.
Linearity, reversal of multiplication, preservation of one and involutivity are
proved in the implementation. No adjoint identity is postulated.

`signatureMatrix n r` is the actual complex diagonal matrix with entry `1`
when the coordinate index is below `r`, and `-1` otherwise. Its self-adjointness
and square-one identity are proved. `signatureUnit` packages its inverse;
`signatureAdjoint` combines it with Mathlib's conjugate-transpose star on
complex matrices, as a real-linear involution. `signatureUnitary` is the
corresponding genuine subgroup of invertible matrices. The signature predicates
require `r ≤ n`.

`HasSignature` uses a specific real embedding of the totally real field `E`.
It installs that embedding's algebra structure on `ℝ`, takes the actual tensor
product `ℝ ⊗[E] A`, and requires an actual real-algebra isomorphism to complex
matrices intertwining the two involutions. Thus a signature label cannot be
chosen independently of the underlying algebra and involution.
`HasHarrisSignature` expresses `n > 1`, one distinguished embedding of signature
`(n-1,1)`, and positive-definite signatures at every other real embedding.
`HasDefiniteSignature` gives positive-definite signatures everywhere.

These are the algebraic realization of the hypotheses in Harris 1999,
Section 1, equation (1.1), printed page 301 (PDF page 3), and the standard
diagonal-Hermitian description recalled in Harris 1997, printed page 89.
The latter paper's Shimura homomorphism must be conjugated as corrected in
Harris 1998, Erratum, pages 180-182; this file defines no homomorphism, and
the accompanying `Domain` module constructs the corrected one.
This file does not assert the global existence of algebras with prescribed
signatures and finite invariants, nor a Shimura canonical model.

Remark, not formalized here: a Hermitian matrix `h` and its negative `-h`
define the same adjoint involution, and reversing the coordinates carries
`-signatureMatrix n r` to `signatureMatrix n (n-r)`. Hence the predicates for
`(r,n-r)` and `(n-r,r)` agree, as in the usual identification of `U(n-1,1)`
with `U(1,n-1)`. No declaration here depends on this remark.

This module depends on the accompanying `CMData` and the published
`Langlands.Shimura.Unitary.Involution` and `Similitude` modules. It retains independent field/algebra
universes and fixes the archimedean target as the actual real and complex
numbers. All code and intrinsic certificates are by Worker 57.

## Exact source and environment record

The retained originals are:

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39-2 (1999), pp.299-318;
  source `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
  SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
- Harris, *Supercuspidal representations in the cohomology of Drinfeld upper
  half spaces; elaboration of Carayol's program*, Invent. Math. 129 (1997),
  pp.75-119; source `harris-1997-drinfeld-cohomology`,
  SHA-256 `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`.
- Harris, *The local Langlands conjecture for GL(n) over a p-adic field, n < p*,
  Invent. Math. 134 (1998), pp.177-210; source `harris-1998-local-langlands`,
  SHA-256 `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
- Kottwitz, *On the lambda-adic representations associated to some simple
  Shimura varieties*, Invent. Math. 108 (1992), pp.653-665;
  source `kottwitz-1992-lambda-adic-simple-shimura`,
  SHA-256 `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.

The exact relevant passages and declaration correspondence are stated above.
The formal environment is Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

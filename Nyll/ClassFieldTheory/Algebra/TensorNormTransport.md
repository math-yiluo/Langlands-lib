# Transport of the norm of a base-changed algebra

Module `Nyll.ClassFieldTheory.Algebra.TensorNormTransport`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let K, L, A and K', L', A' be commutative rings with L and A algebras over K (and likewise with primes), and let eK, eA, eL be ring isomorphisms compatible with the algebra maps (`hA`, `hL`). This file transports the tensor product A ⊗_K L and the determinant norm `Algebra.norm A` on it, the norm of A ⊗_K L as an A-algebra.

- `tensorMapOfCompatibleEquiv`, `tensorCongrOfCompatibleEquiv`: the ring homomorphism, then ring isomorphism, A ⊗_K L ≃ A' ⊗_K' L' sending a ⊗ l to eA(a) ⊗ eL(l) (`…_tmul`).
- `tensorCongrOfCompatibleEquiv_norm`: eA(N(z)) = N'(E z) for z ∈ A ⊗_K L, where E is this isomorphism; it rests on Mathlib's `Algebra.norm_eq_of_equiv_equiv`.
- `tensorNorm_exists_iff_of_compatibleEquiv`: for x ∈ K, some unit of A ⊗_K L has norm the image of x in A if and only if some unit of A' ⊗_K' L' has norm the image of eK(x) in A'.
- `tensorNorm_mem_range_iff_of_compatibleEquiv`: a unit a of A is a norm of a unit of A ⊗_K L if and only if eA(a) is a norm of a unit of A' ⊗_K' L'.

No finiteness or freeness of L over K is assumed, so `Algebra.norm` is Mathlib's, which is 1 when the algebra has no finite basis; the statements hold in that case too.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Algebra/TensorNormTransport.lean`: the Lean file is the source byte for byte (SHA-256 `083a70a48abcb395dd6cf7af47af080b01cde3a1475a8ae28211696f4f385fed`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

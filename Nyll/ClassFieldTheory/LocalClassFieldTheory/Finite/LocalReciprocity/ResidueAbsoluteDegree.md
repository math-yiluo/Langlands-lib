# The absolute Galois group of a finite field is the group of profinite integers

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAbsoluteDegree`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite field `k`, the Frobenius map `ZHat → Gal(k̄/k)`, `z ↦ Frob^z`, assembled from compatible finite Frobenius coordinates, is shown to be an isomorphism of topological groups. Its inverse is the continuous degree map used in the finite local reciprocity construction.

## Main definitions and results

- `finiteResidueGaloisIntermediateField k n`: for `n > 0`, a finite Galois intermediate field of `AlgebraicClosure k` of degree `n` (`finrank_finiteResidueGaloisIntermediateField`), the image of a chosen embedding of the degree-`n` extension.
- `residueAbsoluteFrobenius_algebraicClosure_injective`: the Frobenius map is injective, since these fields detect every finite coordinate of `ZHat`.
- `mem_range_algebraMap_iff_frobenius_fixed`: the elements of `k̄` fixed by Frobenius are those of `k`.
- `residueAbsoluteFrobeniusRange_eq_top` and `residueAbsoluteFrobenius_algebraicClosure_surjective`: the image is closed (being compact) with fixed field `k`, hence by infinite Galois theory it is the whole group.
- `residueAbsoluteFrobeniusEquiv : ZHatMul ≃ₜ* Field.absoluteGaloisGroup k`: the isomorphism of topological groups; the inverse is continuous because `ZHat` is compact and the Galois group Hausdorff (`absoluteGaloisGroupT2`).
- `residueAbsoluteDegree`: the inverse, `Gal(k̄/k) → ZHatMul`, with `residueAbsoluteDegree_frobenius` sending arithmetic Frobenius to `Multiplicative.ofAdd (1 : ZHat)`, the element `1` of `ZHat`.
- `finiteResidueFrobeniusIntermediate_residueAbsoluteDegree`, `finiteResidueFrobeniusExponentHom_degree_coordinate`, `finiteResidueFrobeniusExponentEquiv_symm_restrict`: on a finite Galois subextension `E`, the restriction of `σ` is Frobenius raised to the degree of `σ` reduced modulo `[E : k]`.

## Points to watch

`ZHatMul` is `ZHat` written multiplicatively. The finite field is given with a `Fintype` instance; the algebraic closure is Mathlib's `AlgebraicClosure k`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAbsoluteDegree.lean`: the Lean file is the source byte for byte (SHA-256 `cf4f775341721eb324a2a81258f8201bbc1f0aaebccf8c99518b66ecd1facb8e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

# Global norms of ideles supported at one place

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.OnePlaceNormKernel`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L / K` be a finite extension of number fields, Galois where needed. An idele of `K` supported at one place `v` is a global norm of a relative idele exactly when its component is a norm from the local tensor algebra `K_v ⊗_K L`; at a finite place this norm group is, for `L / K` Galois, the norm group of the chosen completion of `L` above `v`. This is the identity `N(I_L) ∩ K_vˣ = N((K_v ⊗_K L)ˣ)`, before passing to idèle classes.

## Main definitions and results

- `ideleNormSubgroup`: the range of the norm `RelativeIdeleGroup.norm K L` on relative ideles; `IdeleNormQuotient` is `I_K` modulo it, and `ideleNormClass` the projection.
- `norm_relativeInfinitePlaceIdele` and `norm_relativeFinitePlaceIdele`: the norm of a relative idele supported at `v` is the one-place idele of its local determinant norm (`infiniteTensorDetNorm`, `localTensorNorm`).
- `infinitePlaceIdele_mem_ideleNormSubgroup_iff` and `finitePlaceIdele_mem_ideleNormSubgroup_iff`: the one-place idele of `x ∈ K_vˣ` is in `ideleNormSubgroup` if and only if `x` is a norm from `(K_v ⊗_K L)ˣ`. `ideleNormClass_comp_infinitePlaceIdele_ker` says the same, at an infinite place, about the kernel of `ideleNormClass` composed with the one-place embedding.
- `finitePlaceIdele_mem_ideleNormSubgroup_iff_chosenLocalNorm` and `ideleNormClass_comp_finitePlaceIdele_ker` (`L / K` Galois): the same with `chosenFinitePlaceLocalNormSubgroup`, the norm group of the chosen completion, by `finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup`.
- `finitePlaceIdeleClass_mem_ideleClassNorm_range_of_mem_chosenLocalNorm`: if `x` is in the chosen local norm group, the idèle class of its one-place idele lies in the range of the idèle-class norm `ideleClassNorm K L`.

The norm identities are checked component by component. For the forward direction of the equivalences, the `v`-component of a relative idele with the given norm is a local preimage.

## Remarks

- `ideleNormSubgroup` is the norm image of relative ideles (built from `K_v ⊗_K L`), not literally of `I_L`; the class-level statement transports the witness to `I_L` with `relativeIdeleBaseChangeMulEquiv`.
- The equivalences hold in `I_K`, before quotienting by principal ideles. For idèle classes only one direction is proved: a local norm gives a global norm class.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/OnePlaceNormKernel.lean`: the Lean file is the source byte for byte (SHA-256 `295d900374d4532223b09f16ed85d43944eaf55fec316eefb3f6a1ff0ab19ec4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

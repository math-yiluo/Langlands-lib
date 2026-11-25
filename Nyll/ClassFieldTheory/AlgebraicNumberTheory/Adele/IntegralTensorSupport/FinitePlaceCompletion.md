# Two models of a finite completion, and integrality of traces

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.FinitePlaceCompletion`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let K be a number field and w a finite place of K, given as a height-one prime of 𝓞 K. Two models of K_w occur in the library. One is the completion of K at the w-adic absolute value `adicAbv K w`. The other is Mathlib's `w.adicCompletion K`. This file builds a K-algebra isomorphism between them and its base change to K_w ⊗_K L. It also proves the trace and discriminant facts used to show that basis coordinates are integral.

## Comparison of completions

- `relativeFinitePlaceCompletionBaseMap w`: the map from K, with the w-adic absolute value, to `w.adicCompletion K`. It preserves norms and is an isometry.
- `relativeFinitePlaceCompletionRingHom w`: its extension to the completion. It is an isometry (`..._isometry`) and surjective (`..._surjective`).
- `relativeFinitePlaceCompletionRingEquiv` and `relativeFinitePlaceCompletionAlgEquiv`: the resulting isomorphism of rings, and of K-algebras. `relativeFinitePlaceCompletionAlgEquiv_symm_norm` says its inverse also preserves norms.
- `relativeFinitePlaceLocalTensorAlgEquiv w`: the base change to K_w ⊗_K L.
- `norm_le_one_of_mem_adicCompletionIntegers` and `mem_adicCompletionIntegers_of_norm_le_one`: the valuation ring of `w.adicCompletion K` is the set of elements of norm at most 1.

## Traces and coordinates

- `basis_coord_isIntegral_of_integral_traces`: a form of Cramer's rule. Let b be a basis of B over a field A, and R a ring with an algebra map to A. Suppose that the traces of b_j b_k and of x b_j are integral over R, that the discriminant of b is nonzero, and that its inverse is integral over R. Then every coordinate of x in b is integral over R.
- `trace_tensorProduct_basis_mul` and `discr_tensorProduct_basis`: for a K-basis b of L and a field A over K, the trace matrix and the discriminant of the basis of A ⊗_K L induced by b are the images of those of b.
- `isIntegral_trace_tensor_of_components`: let L/K be separable and vK a nonarchimedean, nontrivial absolute value on K. Suppose every component of x ∈ K_v ⊗_K L in the local tensor decomposition lies in the valuation ring of its completion. Then the trace of x over K_v is integral over the valuation ring of K_v.

## Proofs

Surjectivity holds because the range is closed, the map being an isometry, and contains the dense image of K. The trace on the product of completions is the sum of the traces of the components, and each component is integral over the base valuation ring by `isIntegral_over_baseCompletionIntegers_of_mem`.

## Points to watch

- `basis_coord_isIntegral_of_integral_traces` is described as Cramer's rule over an integrally closed base, but its statement assumes nothing about R beyond the listed integrality hypotheses.
- The last theorem holds for any field extension that is finite and separable. It does not need number fields.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Adele/IntegralTensorSupport/FinitePlaceCompletion.lean`: the Lean file is the source byte for byte (SHA-256 `ca849cba47671dd1ff33f587853c1eb1984c090bbe6160239542b51e4f45047f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

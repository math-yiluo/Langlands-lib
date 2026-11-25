# Local degrees, norms and traces in a finite separable extension

Module `Nyll.ValuedFieldTheory.Valuation.Completion.DegreeNormTrace`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite separable field extension, `v` a nontrivial real absolute value on `K`, and `L_w` the completions of `L` at the absolute values `w` extending `v`. From the decomposition `K_v ⊗_K L ≅ ∏_w L_w`, proved in another file of the library, the file derives the fundamental identities relating global and local degrees, norms and traces.

## Main results

- `completionModuleFinite`: each `L_w` is finite-dimensional over `K_v`.
- `completionDegreeNormTrace_degree`: `[L : K] = ∑_w [L_w : K_v]`.
- `completionDegreeNormTrace_norm`: for `x ∈ L`, the image in `K_v` of the norm of `x` over `K` is the product over `w` of the norms over `K_v` of the images of `x` in `L_w`.
- `completionDegreeNormTrace_trace`: the image in `K_v` of the trace of `x` over `K` is the sum over `w` of the traces over `K_v` of the images of `x` in `L_w`.
- `completionDegreeNormTrace`: the three formulas together.

## Proof

Each statement transports the decomposition `completionTensorDecomposition_left` through generic lemmas on base change to a finite product of algebras (dimension is additive, norm is multiplicative, trace is additive over the factors), together with the compatibility of norm and trace with scalar extension.

## Points to watch

- Separability of `L/K` and nontriviality of `v` are assumed because the decomposition theorem used is stated under them.
- The finite index set is the type `AbsoluteValueExtension v L` of absolute values on `L` restricting exactly to `v`; its `Fintype` structure comes from the decomposition (`completionTensorDecomposition_extensionFintype`).
- The norm and trace identities are stated after mapping the global norm and trace from `K` into `K_v`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Completion/DegreeNormTrace.lean`: the Lean file is the source byte for byte (SHA-256 `1632add0b26908569df7573d2cf8b59880727186348f02bde914fd567af01532`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

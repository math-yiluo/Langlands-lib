# Common Galois overfields of number-field towers

This internal construction takes number-field towers `F → E → L₁` and
`F → E → L₂`, with both upper fields Galois over `F`. It constructs a number
field `M` in the same universe, Galois over `F`, and embeddings of `L₁` and `L₂`
into `M` which agree on `E`. The `CommonGaloisOverfield` structure records the
field, its algebra structures, and all five scalar-tower compatibilities.

The definition `commonGaloisOverfield` embeds each upper field over `E` into
`AlgebraicClosure E`. It takes the supremum of the two image intermediate fields
over `F`. Each image is isomorphic over `F` to its original number field. Mathlib's
finite-dimensional and normal compositum results therefore make the supremum a
finite normal extension of `F`. It is a number field and is separable in
characteristic zero, hence Galois. Restricting the two embeddings to the
compositum yields the two upper algebra structures. The algebra structure from
`E` is obtained through the first embedding; equality of the embeddings on `E`
proves the remaining tower compatibility.

This is derived field-theoretic infrastructure for comparing idele-class
representatives in different auxiliary extensions. Its provenance is the
Mathlib embedding, intermediate-field compositum, and normality APIs imported
by the Lean file. It makes no cohomological assertion and does not prove the
global invariant statement. No Galois assumption on `E/F` is needed.

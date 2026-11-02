# Sections of a common represented kernel pair

This internal derived lemma applies to actual presheaves on the full scheme
slice over an arbitrary scheme `S`. Given two maps from the same represented
presheaf to presheaves `F` and `G`, it assumes that the same scheme `R` and
the same two projections `t s : R ⟶ U` form a kernel-pair pullback square
for each map.

`same_kernel_of_common_represented_kernelPair` proves that two morphisms
`x y : T ⟶ U` have equal images in `F` if and only if they have equal
images in `G`, for every scheme `T` over `S`.

The implemented proof evaluates the first pullback square at `T`.
Mathlib's `Types.exists_of_isPullback` lifts a pair of sections with equal
images to a section of the represented relation. Commutativity of the
second square, evaluated at this lifted section, gives equality of its
images in `G`. Interchanging the squares proves the reverse implication.

The result uses no sheaf or geometric assumptions and imposes no conditions
on the test schemes. It constructs no quotient. Its provenance is the
published actual lifted scheme Yoneda interface and Mathlib's pointwise
pullback and type-valued pullback universal properties.

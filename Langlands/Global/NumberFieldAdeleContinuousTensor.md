# Continuous functions and full adelic scalar extension

For number fields `K` and `L` in an arbitrary common universe, an algebra
`K → L`, and any topological space `X` in any universe,
`Langlands.Global.adeleContinuousMapTensorAlgEquiv` constructs

`L ⊗[K] C(X, Adeles K) ≃ₐ[L] C(X, Adeles L)`.

The rings of continuous functions use the original full adele topologies.
All infinite places and all finite places are retained. The comparison
sends `a ⊗ f` at `x` to the principal adele of `a` multiplied by the
original full adelic inclusion of `f x`.

This is internal derived infrastructure for continuity of the canonical
adelic Weil-restriction map. It uses the canonical full adelic tensor
algebra equivalence, the original continuous full adelic inclusion, and
`adeleBasisHomeomorph` with its trace-dual coordinates. It does not assume
compactness or the norm-one comparison.

The implementation first constructs `adeleInclusionAlgHom`. Its base-field
algebra structure on `Adeles L` is the composite of the given field
inclusion and the principal map for `L`. The proof scopes that structure
locally, retaining the existing `L`-algebra structure. Composition with the
continuous inclusion gives an algebra map on continuous functions, and
the tensor universal property constructs `adeleContinuousMapTensorAlgHom`.

The evaluation identity `eval_comp_adeleContinuousMapTensorAlgHom` says
exactly that evaluating this map equals tensor extension of evaluation
followed by `numberFieldAdeleTensorEquiv`. It follows by tensor induction.

To prove bijectivity, choose a finite field basis. Tensor coordinates of a
continuous-function tensor evaluate to the full adelic coordinates of its
image. This is proved on pure tensors and sums. Those coordinates prove
injectivity. Conversely, the coordinates of any continuous upper-adele
function are continuous by the trace-dual basis homeomorphism. The finite
sum of the basis elements tensored with these coordinate functions maps
back to that function, by the inverse-coordinate formula. This proves
surjectivity and yields the stated algebra equivalence.

The result establishes a comparison of continuous function rings on any
space. It makes no assertion about rational-character kernels or rational
quotient compactness.

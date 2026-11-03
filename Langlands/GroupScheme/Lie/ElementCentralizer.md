# The actual adjoint stabilizer of a Lie element

`Lie.elementCentralizer G X` is a subgroup functor of the actual group scheme
`G` over a ring `R`, for `X` in the actual dual-number identity kernel over `R`.
A point on a test scheme `U` belongs when, after every affine refinement
`Spec A → U`, its constant dual-number lift commutes with the scalar extension
of `X`. Multiplication, inverse and arbitrary restriction preserve this condition.
The definition requires neither affineness nor a Lie bracket.

`mem_elementCentralizer_affine_iff` proves that on `Spec A` membership is
equivalent to constant-point conjugation fixing the actual extended kernel
point. The converse uses full faithfulness of affine spectra and naturality
of kernel conjugation, so the quantification over refinements is retained.
For affine `G`, `mem_elementCentralizer_adjoint_iff` identifies this equation
with the existing linear adjoint action. `elementCentralizerLie` is the
submodule obtained by evaluating this subgroup functor on the dual-number test.
The file also proves identity and composition laws for kernel coefficient maps.

This is a derived all-test construction of the stabilizer `C_G(X)` introduced
before Milne, *Algebraic Groups* (2017), Proposition 17.76, printed p.377 / PDF
p.393. The construction and the affine adjoint comparison are elementary
consequences of the published actual-kernel APIs. No representability,
smoothness, connectedness, or Lie-bracket comparison is claimed here, and no
semisimplicity hypothesis is used.

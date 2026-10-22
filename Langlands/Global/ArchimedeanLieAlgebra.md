# Concrete archimedean matrix Lie algebra and complexification

Author: Worker 72. Namespace: `Langlands.Global.ArchimedeanGL`.

For an actual number field `K : Type u` and every natural rank `n`, including
zero, `RealLieAlgebra K n` is a type synonym for the published
`Langlands.Global.ArchimedeanMatrix K n`. Its vector operations and real scalar
multiplication are exactly the matrix operations. Its Lie bracket is the
associative matrix commutator. The synonym fixes this bracket independently
of the function-space presentation of the matrix type. The identity linear
equivalence `realLieAlgebraToMatrix` exposes the underlying matrices, and
`realLieAlgebraToMatrix_lie` states the precise formula `XY - YX`.
The Lie ring and real Lie algebra laws reuse Mathlib's proved associative
algebra construction. No relation to an unproved derivation-space model is
assumed. The algebraic definitions only require `Field K`; the number-field
assumption is needed later for the finite-dimensional analytic model.

`ComplexLieAlgebra K n` is the actual tensor product
`Complex ⊗[Real] RealLieAlgebra K n`, with Mathlib's scalar-extension Lie
algebra structure. It complexifies the entire real matrix algebra, including
both real directions of each complex coefficient; it does not substitute
holomorphic dependence at complex places. The pure-tensor bracket is
`[z ⊗ X, w ⊗ Y] = zw ⊗ [X,Y]`. The real Lie homomorphism `complexify` sends
`X` to `1 ⊗ X`; bracket preservation follows from this tensor formula.

`EnvelopingAlgebra K n` is Mathlib's `UniversalEnvelopingAlgebra` over the
complex numbers of this complexified Lie algebra. `envelopingGenerator` is
the canonical Lie homomorphism into this algebra, and its displayed
commutator identity is Mathlib's defining enveloping relation. The type
`EnvelopingCenter K n` is the carrier of the actual algebra center
`Subalgebra.center`, and `centerInclusion` is its complex algebra inclusion.
The final identity says its values commute with every element of the
enveloping algebra.

These definitions supply the algebraic objects for the subsequent genuine
differential action on the published smooth-function space. They do not
construct or assume that action, identify arbitrary invariant derivations
with tangent vectors, or assert center-finiteness of smooth functions.
The identification of the differential commutator with this matrix bracket
remains a separate analytic proof obligation.

## Source correspondence and provenance

A. Borel and H. Jacquet, *Automorphic forms and automorphic representations*,
Corvallis Part I (1979), section 1.1, printed p.189 (one-based PDF184), use
the real Lie algebra, its enveloping algebra over the complex numbers, and
the center of that enveloping algebra. Section 4.1, printed p.194 (PDF189),
applies this setup to the product of archimedean groups viewed as a real
Lie group. Sections 1.3(c) and 4.2(c), printed pp.190 and 195 (PDF185 and
190), impose a finite-codimension central annihilator condition on selected
functions. No such finiteness assertion is made in this module.

Registered original: `borel-jacquet-1979-automorphic`, SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
Worker 72 read these original pages, and sections 4.6-4.7 (PDF191-192), which
keep the automorphic Hecke module distinct from a full adelic group action.
The explicit matrix model, tensor complexification and implementation laws
are derived constructions realizing the survey's objects for general linear
groups; they are not theorems quoted verbatim from the survey. The matrix
space is imported from the published `Langlands.Global.ArchimedeanGL`.
Mathlib's `Algebra.Lie.OfAssociative`, `Algebra.Lie.BaseChange`,
`Algebra.Lie.UniversalEnveloping` and `Subalgebra.center` provide the exact
algebraic constructions and intrinsic proofs.

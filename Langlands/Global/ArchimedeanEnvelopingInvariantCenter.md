# Full-group invariant enveloping elements are central

Author: Worker 94. Namespace: `Langlands.Global.ArchimedeanGL`.

For every `K : Type u` with `Field K` and `NumberField K`, and every natural
rank `n`, this module constructs the complex algebra inclusion
`envelopingGroupInvariantToCenter` from the actual full-group fixed subalgebra
`envelopingGroupInvariants K n` into the genuine center `EnvelopingCenter K n`.
Its underlying map is the identity on enveloping elements. The theorem
`envelopingGroupInvariants_le_center` supplies the inclusion.
The full archimedean group is `InfiniteAdelicGL K n`; it is not restricted to
the standard compact subgroup or its identity component.

The composite `lieSymmetricGroupInvariantCentralSymmetrize` sends full-group
invariant elements of the actual Lie symmetric algebra into this center.
It is complex linear. Its coercion formula identifies its value with the
published whole symmetrization `lieSymmetricAlgebraSymmetrize`.
No multiplicativity of symmetrization is asserted.

The analytic input is provided by two public derivative theorems.
`realLieExponentialCurve K n Y t` transports the matrix exponential
`exp (t • realLieAlgebraToMatrix K n Y)` through the actual archimedean group
coordinates. Its matrix inverse is the exponential with negative argument;
the two exponential addition identities prove that it is an actual unit.
At `t = 0` the group element is the identity.
`exponentialCurve_adjoint_deriv` proves that matrix conjugation of a real
Lie vector `X` along this curve has derivative `[Y, X]` at zero.
This follows by differentiating `exp(tY) X exp(-tY)` and using the actual
matrix commutator formula.

For any enveloping element `a` and any algebraic complex linear functional
`ℓ : EnvelopingAlgebra K n →ₗ[ℂ] ℂ`,
`exponentialCurve_enveloping_deriv` proves

\[
 \left.\frac{d}{dt}\right|_{t=0}
   \ell\bigl(\operatorname{Ad}(\exp(tY))a\bigr)
 =\ell\bigl(\iota(1\otimes Y)a-a\iota(1\otimes Y)\bigr).
\]

Here `ι` is the genuine enveloping generator and `1 ⊗ Y` is `complexify K n Y`.
The derivative is over the real variable `t`. The theorem imposes no topology
or continuity assumption on the enveloping algebra or on `ℓ`.

The proof forms a private complex submodule of elements satisfying this
scalar derivative identity for every `ℓ`. It contains one and is closed under
addition and complex scalar multiplication. To prove closure under right
multiplication by a real Lie generator, the conjugated generator is expanded
in a finite real basis of the actual archimedean matrix space. The basis
coordinates are continuous linear maps because that matrix space is finite
dimensional over the reals. The matrix derivative theorem differentiates
each coordinate, and the scalar product rule differentiates its product with
the scalar evaluation of the remaining enveloping factor. Summing the
finitely many terms and using the enveloping bracket relation gives the
commutator formula. Tensor-product induction extends closure to every
complexified Lie generator. Induction through the exhaustive genuine
enveloping degree filtration then proves the formula for every `a`.

If `a` is fixed by the full group, each of these scalar orbit functions is
constant. Uniqueness of derivatives forces every functional to vanish on
each real-generator commutator. Algebraic dual separation makes those
commutators zero. Tensor-product induction shows that all complexified
generators centralize `a`. The published generic theorem
`Langlands.Algebra.LieCasimir.enveloping_adjoin_range` says that those
generators generate the whole enveloping algebra as a complex algebra.
The centralizer subalgebra therefore equals the whole algebra, proving that
`a` belongs to its center.

This is an internal construction derived from the published actual
archimedean matrix, Lie, conjugation, symmetric and enveloping objects,
the genuine exhaustive filtration, and Mathlib's matrix exponential,
calculus and algebraic dual separation results. It is not a separate
literature theorem or a replacement of those objects. The number-field
hypothesis provides the finite-dimensional matrix setting used by the
calculus proof; the universe of `K` and every rank, including zero, are
retained. No reverse center-to-group-invariants inclusion, invariant
preimage for the full group, central generation, admissibility or
automorphic differential growth theorem is proved here.

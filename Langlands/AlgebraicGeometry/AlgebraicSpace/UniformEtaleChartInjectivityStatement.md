# Uniform injectivity of affine étale charts over normed extensions

Author: Worker 114.

`UniformEtaleChartInjectivityStatement` is a derived prerequisite, proposed for
an elementary approach to ground-field extension in the rational-point topology
of algebraic spaces. It is not attributed to a numbered theorem of Conrad and
does not assert the existence of an analytification.

Let `K` be any nontrivially normed field, `X` a separated algebraic space over
`Spec K`, and `a : U → X` an étale map from an affine scheme locally of finite
type over `K`. The statement asks for finitely many regular functions `f_i` on
`U`, chosen before any extension field or bound. For each positive real `R`
there is a positive `δ` such that the following holds over every normed
extension `L/K`: if `p,q ∈ U(L)` have all `f_i` values of norm at most `R`, if
the corresponding values differ in norm by less than `δ`, and if `p,q` have
the same image in `X(L)`, then `p=q`. The extension may have infinite degree.
No completeness or henselian hypothesis is imposed.

The coordinate ring is the existing `AffineCoordinateRing K U`, the actual
ring of global sections of `U`; evaluations use the published equivalence
`affineSchemePointEquiv K U L`. The same-image condition is evaluation of
the actual presheaf map `a` at `Spec L`.

The proposed argument explains the scope of this internal target. Separatedness
of `X` makes `R_U = U ×_X U` a closed subscheme of the affine scheme
`U ×_K U`. Because `a` is étale, its diagonal is open; because `U` is
separated over `K`, its diagonal in `R_U` is also closed. The resulting
idempotent regular function of `R_U`, equal to one on the diagonal and zero
on its complement, can be lifted to a regular function on `U ×_K U`.
Finite type expresses that lift as a polynomial in a finite family of
regular functions on the two factors. A polynomial norm estimate on bounded
coordinates, valid uniformly over norm-preserving field extensions, forces
the lifted function to remain nonzero near the diagonal. A pair in the same
fibre must therefore lie on the diagonal.

This route is a mathematical motivation, not a Lean proof. The module contains
only the Prop-valued statement. Uniform injectivity is a substantial missing
prerequisite; it alone does not prove the embedding or closed-image conclusion
of `HenselianExtensionPointEmbeddingStatement`.

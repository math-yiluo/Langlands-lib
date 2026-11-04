# Exact kernels for smooth affine algebraic groups

`Langlands.GroupScheme.AffineQuotient.smoothNormalKernel.{u}` proves
`SmoothNormalKernelInput.{u}`. Let `k : Type u` be algebraically closed,
`G` a smooth affine group scheme locally of finite type over `k`, and
`i : H ⟶ G` a closed subgroup with normal range on every relative scheme
test. The conclusion supplies a natural number `n` and an actual group
scheme homomorphism `G ⟶ GL (Fin n)` whose kernel inclusion has exactly the
same range functor as `i`. No smoothness or reducedness of `H` is assumed.

The proof starts with the actual Chevalley line-stabilizer theorem. It
provides a representation `ρ` and a standard vector `e_j` whose unit-scalar
line stabilizer is exactly `H`, on all scheme tests. Smoothness over the
field makes `G` reduced. The orbit-coordinate construction then chooses a
basis from the rational orbit of `e_j`, retaining `e_j` itself, and supplies
split coordinates invariant under `G` on every test. Rational-point
detection here uses algebraic closedness, reducedness and local finite type
of `G`; it imposes no reducedness condition on the test scheme.

Let `σ` be the representation in those orbit coordinates. Normality
implies that each selected orbit vector is an `H`-eigenvector with a unit
eigenvalue on every test: apply the original line criterion to the
conjugate of an `H`-point by the rational orbit point. Thus `σ` is diagonal
on `H`. Let `s₀` index the retained vector `e_j`. The dual representation
`σ.dual` scales `e_s₀` by the inverse of the unit scaling `e_j` under `ρ`.
Consequently `e_(j,s₀)` is fixed by `H` in `ρ.tensor σ.dual`.

Every point fixing that tensor preserves the original line of `e_j`, and
therefore belongs to `H`. This assertion holds over arbitrary commutative
test rings: the tensor coordinate at `(j,s₀)` makes the first scalar a
unit, and the remaining coordinates recover its scalar action.
The representation on the entire `H`-fixed subspace of the tensor
representation is defined because `H` is normal and affine. Here `H` is
affine because it is closed in the affine group `G`. It kills `H`, and any
point in its kernel fixes `e_(j,s₀)`, so its scheme-theoretic kernel is
exactly `H`. The existing fixed-subrepresentation construction already
indexes its coordinates by `Fin n`.

This is the smooth-source case of Milne, *Algebraic Groups* (2017),
Lemma 5.17, printed page 103 (PDF page 119). Its implementation follows the
rational-orbit, inverse-character and fixed-space construction of
Lemma 5.16, printed page 102 (PDF page 118), with the hypotheses needed for
rational-point detection made explicit. All kernel and stabilizer
comparisons retain arbitrary scheme tests, including nonreduced ones.
The general arbitrary-field quotient theorem follows separately by the
reduction in `AffineQuotientReduction`.

Worker 706 assembled the proof from the orbit and eigenline helpers.
Worker 239 supplied the tensor and dual cancellation helpers and the
reduction interface.

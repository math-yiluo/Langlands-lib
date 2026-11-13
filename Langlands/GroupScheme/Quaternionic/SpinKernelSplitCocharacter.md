# A split cocharacter in the original quaternionic spin cover

This internal supporting construction works with a finite-dimensional central division algebra \(D/K\), an extension field \(L/K\), and a specified splitting chart
\[
e:L\otimes_K D \simeq_L M_2(L).
\]
It supplies a cocharacter of the base change of the original spin cover, its comparison with the original binary diagonal on square roots of one, and its ambient hyperbolic Levi action. It does not construct full orthogonal coordinates or prove the final kernel-generator statement.

For a commutative \(L\)-algebra \(R\), with its compatible \(K\)-algebra structure, `splitDiagonalUnits` sends a unit \(t\) to the inverse chart of \(\operatorname{diag}(t,t^{-1})\). The chart here is `Quaternionic.chartR e R`. The canonical reduced-norm/determinant identity `reducedNorm_eq_det_fintype` proves that these units have reduced norm one; `splitNormOneDiagonal` is the resulting group homomorphism into `reducedNormOne K D R`.

The coefficient lemmas prove the following identities and compatibility:

- The chart of `splitNormOneDiagonal e R t` is \(\operatorname{diag}(t,t^{-1})\).
- If \(t t=1\), its underlying unit equals the original scalar unit `normCoverScalarUnits K D R t`.
- It respects arbitrary \(L\)-algebra maps, using tensor-product base change on the underlying units.
- Multiplication by the scalar unit gives chart matrix \(\operatorname{diag}(t^2,1)\).

The proofs apply the injectivity of the chart and compute the four matrix entries. Naturality uses `chartR_naturality`. No proof divides by two; the coefficient identities apply also to nonreduced commutative algebras.

For every scheme \(U\) over \(\operatorname{Spec}L\), `splitBinaryPoints` uses its ring of global sections, presented as `restrictedSections K L U`, and the published point equivalences to give points of the original binary product over \(K\). Its coordinates are
\[
\bigl(\operatorname{diag}(t,t^{-1}),\ \texttt{splitNormOneDiagonal}\ e\ R\ t\bigr).
\]
`splitBinaryPoints_naturality` checks all restrictions of test schemes, using the special-linear and norm-one point equivalences and the coefficient naturality just proved. The base-change point equivalence gives `splitBinaryBaseChangePoints`; `homOfPoints` then constructs the group-scheme morphism `splitBinaryCocharacter` into the base-changed original binary product. Its point formula is `splitBinaryCocharacter_points`. When \(\dim_K D=4\), `splitBinaryPoints_root` identifies every square-root-of-one point with the published `BinaryKernel.diagonal`, using its coordinate formula and the scalar comparison.

For the spin construction the hypotheses are those of the original binary lift: \(K\) is infinite, \(\sigma\) is a first-kind involution with \(\dim_K D=4\) and symmetric-subspace dimension \(3\), \(h\) is a hyperbolic pair for a quaternionic quadratic form \(q\), and \(\pi:S\to\operatorname{Isom}(q)\) is a spin cover. The proposition `DegreeTwoNormOneSimplyConnectedStatement` remains an explicit argument, as required by `BinarySpinLift.productHom`.

`splitSpinCocharacter` composes the binary cocharacter with the base change of that product lift. `splitSpinCocharacter_points` describes it on every relative test scheme. `splitSpinCocharacter_root` identifies its restriction to square roots of one with the original `BinarySpinLift.diagonalSpin` after transport by the base-change point equivalence.

Finally, `splitSpinCocharacter_ambient_points` projects through \(\pi\) and the original ambient isometry inclusion. The resulting matrix unit is
\[
\operatorname{extendUnits}_h\left(
  \operatorname{hyperbolicLevi}_{\sigma_R}
    \bigl(\operatorname{scalar}(t)\,\texttt{splitNormOneDiagonal}(t)\bigr)
\right).
\]
The proof uses `BinarySpinLift.productHom_ambient_points`, the binary coordinate formula, and `BinarySpinLift.diagonal_normOne_action`. Together with the coefficient calculation, this describes the Levi argument by the split matrix \(\operatorname{diag}(t^2,1)\). These are all-test identities, with no restriction to field-valued points.

The provenance is internal: the module assembles the published splitting-chart, canonical reduced-norm, binary-action, point-equivalence, and binary-spin-lift APIs into the cocharacter needed by the quaternionic spin-kernel reduction. It introduces no new literature claim or characteristic assumption.

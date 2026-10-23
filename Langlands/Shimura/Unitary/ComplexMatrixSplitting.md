# Complex matrix splitting of the Harris algebra

This module constructs algebra equivalences for the actual scalar extensions of
the algebra carrying the Harris involution. It is an internal algebraic
prerequisite derived from the published real-place charts and the ordered complex
splitting of the Deligne quadratic algebra. It does not assume a separate complex
matrix decomposition as input.

## Inputs and conventions

The generic construction `ComplexMatrix.tensorAlgEquiv` requires commutative
rings `R` and `S`, an `R`-algebra structure on `S`, and a possibly noncommutative
ring `A` with an `R`-algebra structure. For every natural number `n`, it identifies
`S ⊗[R] Matrix (Fin n) (Fin n) A` with matrices over `S ⊗[R] A`, as `S`-algebras.
No positivity or nonzero-rank assumption is needed for this generic comparison.

The Harris specialization retains the hypotheses of `HarrisSignatureCharts`:
totally real and totally complex number fields `E` and `K`, a quadratic extension
`K/E`, the indicated `E`, `K`, and rational algebra structures on `A`, the tower
`ℚ → E → A`, a second-kind involution `σ`, and actual charts `C` of rank `n`
indexed by real embeddings of `E`. The chart data also records the chosen complex
embeddings `Φ` and the distinguished real place. A finite basis `b` of `A` over
`E` is explicit input, just as in `RealSplitting`. In the central simple case the
published `CentralSimpleUnitaryData.totallyRealBasis` provides this basis.

The two complex factors are ordered by evaluation at `+i` and `-i` in the
published `DeligneTorus.tensorSplitEquiv`. The conjugation in the second factor
is entrywise conjugation of the original matrix. It fixes the newly extended
complex scalar; it is not conjugate transpose.

## Constructions and formulas

`tensorLinearEquiv` distributes tensor product over the two finite entry indices.
`tensorAlgEquiv` upgrades it to an algebra equivalence. Its formula is

\[
 s\otimes M\longmapsto (s\otimes M_{ij})_{ij}.
\]

The multiplication proof expands both sides as the same finite sum over the
intermediate matrix index and uses multiplication of pure tensors. The identity
proof treats the diagonal and off-diagonal entries separately. This verifies
matrix multiplication, rather than using pointwise multiplication on arrays.

`prodAlgEquiv` identifies matrices over a product ring with the product of the
two matrix algebras. Its inverse pairs the entries. Combining this with
`tensorAlgEquiv` and `DeligneTorus.tensorSplitEquiv` gives `complexEquiv`:

\[
 \mathbf C\otimes_{\mathbf R}M_n(\mathbf C)
 \simeq_{\mathbf C}M_n(\mathbf C)\times M_n(\mathbf C).
\]

`tensorSplitEquiv_tmul` and `complexEquiv_tmul` prove the ordered formulas

\[
 z\otimes w\longmapsto(zw,z\overline w),\qquad
 z\otimes M\longmapsto(zM,z\overline M).
\]

The scalar formula follows by expanding the real and imaginary coordinates of
the quadratic algebra; the matrix formula applies it entry by entry.

`HarrisSignatureCharts.iteratedComplexMatrixEquiv` first extends
`C.realMatrixEquiv b` to complex scalars, distributes tensor product over the
finite set of real places, then applies `complexEquiv` at each place. It gives

\[
 \mathbf C\otimes_{\mathbf R}(\mathbf R\otimes_{\mathbf Q}A)
 \simeq_{\mathbf C}
 \prod_{\tau:E\hookrightarrow\mathbf R}
 (M_n(\mathbf C)\times M_n(\mathbf C)).
\]

For `x : ℝ ⊗[ℚ] A`, its pure-tensor formula at `τ` is
`(z • C.realMatrixEquiv b x τ, z • (C.realMatrixEquiv b x τ).map star)`.

`complexMatrixEquiv` precomposes this map with the published
`AlgebraInvolution.baseChangeTowerEquiv ℚ ℝ ℂ A`, giving the corresponding
isomorphism directly from `ℂ ⊗[ℚ] A`. Its pure-tensor formula is

\[
 (z\otimes a)_\tau\longmapsto
 (z\,C.\mathrm{evaluation}(a)_\tau,
  z\,\overline{C.\mathrm{evaluation}(a)_\tau}).
\]

## Provenance and scope

These are internal constructions from `DeligneSplitting`, `RealSplitting`, and
`InvolutionBaseChangeTower`, using Mathlib's finite-product tensor equivalences
and its algebra-equivalence constructors. All displayed formulas are implemented
and proved in this module. No additional external existence theorem is used.

The equivalences depend on the supplied charts and basis. This module does not
prove their independence, the complex coordinate formula for the involution,
the matrix weights of the complex cocharacters, conjugacy or reflex-field
comparison, or smoothness and reductivity. The PEL geometry, representability,
level schemes and coefficient descent remain further obligations of the host
task. In particular, this algebra equivalence alone is not a construction of a
Shimura variety.

# Harris matrix splitting over complex coefficient algebras

This module extends the published complex matrix decomposition to every
commutative complex algebra. It constructs actual algebra equivalences, proves
their pure-tensor formulas, and proves compatibility of the generic matrix
splitting with complex-algebra homomorphisms. It is an internal consequence of
`ComplexMatrixSplitting`, `DeligneSplitting`, and `RealSplitting`.

## Scalars and ordered factors

Let `S` be a commutative ring with complex and real algebra structures satisfying
`IsScalarTower ℝ ℂ S`. Write `j : ℂ → S` for its complex algebra map. No field,
reducedness, finite dimension, or nontriviality hypothesis on `S` is imposed.
The real structure is retained explicitly so the construction can be used with
global sections equipped with a specified structure map.

`ComplexMatrix.scalarEquiv S n` is an `S`-algebra equivalence

\[
 S\otimes_{\mathbf R}M_n(\mathbf C)
 \simeq_S M_n(S)\times M_n(S).
\]

It composes `tensorAlgEquiv` with the entrywise map induced by
`DeligneTorus.tensorSplitEquiv S`, then with `prodAlgEquiv`. Thus the
multiplication is ordinary matrix multiplication. The tensor and matrix
comparisons already have their multiplication and inverse laws proved in the
imported modules. The factor order is evaluation at `+i`, then at `-i`.

The private scalar calculation applies `j` to the real/imaginary decomposition
of a complex number and to that of its conjugate. The scalar tower identifies
the real coefficients. It yields the public formulas
`tensorSplitEquiv_scalar_tmul` and `scalarEquiv_tmul`:

\[
 s\otimes w\longmapsto(sj(w),sj(\overline w)),\qquad
 s\otimes M\longmapsto(s\,j(M),s\,j(\overline M)).
\]

Here both `j` and conjugation act entrywise on matrices. Conjugation affects
only the original complex entries; no conjugation on `S` is required.

For any commutative complex algebra `T` with the same compatible real-scalar
structure, and any complex-algebra homomorphism `f : S →ₐ[ℂ] T`,
`scalarEquiv_natural` proves

\[
 e_T((f\otimes 1)x)
   = (f((e_Sx)_1),f((e_Sx)_2)).
\]

The left side uses `AlgebraInvolution.changeCoefficients` for the real-algebra
restriction of `f`; the right side maps entries. The proof is tensor induction:
the pure-tensor case uses the displayed formula and `f`'s compatibility with
complex scalars, and the additive case uses entrywise additivity.

## The actual Harris algebra

The specialization retains the inputs of `HarrisSignatureCharts`: totally real
and totally complex number fields `E` and `K`, a quadratic extension `K/E`, a
ring `A` with the indicated `E`, `K`, and rational algebra structures and tower
`ℚ → E → A`, a second-kind involution, and actual Harris signature charts `C`
with their distinguished place and chosen complex embeddings. A finite
`E`-basis `b` of `A` is explicit. In the central simple setting it is supplied by
`CentralSimpleUnitaryData.totallyRealBasis`.

`C.iteratedScalarMatrixEquiv b S` gives

\[
 S\otimes_{\mathbf R}(\mathbf R\otimes_{\mathbf Q}A)
 \simeq_S
 \prod_{\tau:E\hookrightarrow\mathbf R}(M_n(S)\times M_n(S)).
\]

It extends the constructed `C.realMatrixEquiv b`, distributes tensor product
over the finite set of real embeddings, and uses `scalarEquiv` in each factor.
For `x : ℝ ⊗[ℚ] A`, `iteratedScalarMatrixEquiv_tmul` gives at `τ`

\[
 s\otimes x\longmapsto
 (s\,j(C.\mathrm{realMatrixEquiv}(b)(x)_\tau),
  s\,j(\overline{C.\mathrm{realMatrixEquiv}(b)(x)_\tau})).
\]

With a rational algebra structure on `S` and the compatible tower
`ℚ → ℝ → S`, `C.scalarMatrixEquiv b S` precomposes this equivalence with
`baseChangeTowerEquiv ℚ ℝ S A`. Its source is therefore the actual
`S ⊗[ℚ] A`. The theorem `scalarMatrixEquiv_tmul` identifies its value at
`s ⊗ a` and `τ` as

\[
 (s\,j(C.\mathrm{evaluation}(a)_\tau),
  s\,j(\overline{C.\mathrm{evaluation}(a)_\tau})).
\]

## Provenance and remaining scope

Every equivalence is constructed by composition of the published tensor,
product, ordered scalar-splitting, and real-chart equivalences. The formulas
are proved by complex-coordinate calculations, tensor induction, and the
published formulas for those maps. These internal algebraic deductions do not
invoke a further existence theorem or assume a desired decomposition.

The construction permits coefficient rings obtained from arbitrary complex
test schemes, but this module does not yet identify cocharacter matrices on
those schemes. Involution formulas over general `S`, general-linear
group-scheme comparisons, weights, conjugacy, reflex-field comparison,
smoothness, reductivity, PEL geometry, level schemes, and coefficient descent
remain subsequent obligations. No independence from the chosen charts or
basis is asserted.

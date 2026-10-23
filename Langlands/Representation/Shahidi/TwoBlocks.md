# Ordered two-block shapes for Shahidi induction

This construction specializes the published `GeneralLinear.BlockShape` to
positive ordered ranks `(m,n)`. It supplies the concrete block shape for the
induced representations in Shahidi, *Fourier transforms of intertwining
operators and Plancherel measures for GL(n)* (1984), printed pages 67 and
70–72. The registered source is `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
The explicit equivalences and matrix identities are internal constructions
from the published Library block API, rather than separately asserted
results from the paper.

All declarations below, except the final modulus formula, lie in
`Langlands.Shahidi`.

- `twoBlocks m n hm hn` has two blocks with sizes `m` and `n`, total `m+n`,
  and explicit positivity proofs `hm` and `hn`. It is reducible, so its block
  index is literally `Fin 2` and its sizes are the vector `![m,n]`.
- `twoBlocks_index_first` and `twoBlocks_index_second` prove that the
  Library's consecutive numbering is exactly `Fin.castAdd n` on the first
  block and `Fin.natAdd m` on the second. The proofs use the finite prefix-sum
  formula for `finSigmaFinEquiv`.
- `twoBlockLeviEquiv` is the actual group equivalence from the dependent
  Levi product to `GL_m(R) × GL_n(R)`. Its inverse assembles the two matrices
  by finite dependent function construction. Three evaluation lemmas expose
  the forward map and both components of its inverse.
- `twoBlocks_mem_parabolic_iff` identifies membership in the actual Library
  parabolic with vanishing of the lower-left rectangular block. The proof
  specializes the Library's entrywise criterion to the two possible indices.
- `twoBlocks_leviEmbedding` identifies the Library Levi embedding with
  `GeneralLinear.blockSum (g 0, g 1)`. It proves equality of matrix units by
  splitting their row and column indices into the two consecutive blocks.
- `twoBlocks_leviProjection_first` and `twoBlocks_leviProjection_second`
  extract the two actual diagonal submatrices, in those same coordinates.
- `twoBlockLeviContinuousEquiv` equips the same Levi equivalence with the
  existing product topologies. Continuity follows from coordinate evaluation
  in one direction and the two continuous product projections in the other.

The group constructions hold over an arbitrary commutative ring `R : Type u`.
Only the continuous equivalence asks for a topology on `R`; it does not
assume a topological-ring structure. No representation carrier or normed
space occurs in this helper, so it imposes no field/carrier universe relation.

The final theorem is
`Langlands.PadicField.TopologicalData.leviModulus_twoBlocks`. For every
`PadicField p`, supplied `TopologicalData T`, and actual two-block Levi
matrix `g`, it proves the exact equality of positive-unit characters

`T.leviModulus (twoBlocks m n hm hn) g =
T.determinantNorm m (g 0)^n / T.determinantNorm n (g 1)^m`.

This follows by expanding the Library's product over ordered pairs of blocks:
only `(0,1)` contributes. It uses the existing normalized determinant absolute
value, without any supplied normalization compatibility assumption. The theorem
is a formula for that published algebraic modulus character; it does not itself
assert its interpretation as a Haar-measure scaling factor.

For the surrounding induction task, Shahidi's displays on pages 67 and 72
literally use exponents `1/2(s+n/2)` and `-1/2(s+m/2)`. The standard positive
half of the modulus computed here, combined with twists `s/2` and `-s/2`,
instead gives `(s+n)/2` and `-(s+m)/2`. Lemma 2.2 on page 84 supports the
latter interpretation: in equal ranks, the diagonal pair `(-a,a⁻¹)` contributes
`|det a|^(s+n)`, and additive-matrix inversion contributes
`|det a|^(-2n)`, giving the lemma's `|det a|^(s-n)`. The literal twice-halved
display would give `s-3n/2`. This is an interpretation inferred from the source's
computations, not a known published erratum. Worker 162 personally read the
required pages 67,70–73,84–87.

This helper defines neither induced representations nor analytic integrals.
The general local-field determinant-power layer, the p-adic induction
specialization, function carriers, swapped target, and covariance exponents
remain the enclosing task's construction obligations. No convergence,
meromorphic continuation, tensor-functional, or local-coefficient assertion is
made here.

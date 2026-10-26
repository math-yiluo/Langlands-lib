# The JPSS upper-column conjugation

This module proves the matrix and coefficient identities used by
`UnequalRankFourierSmearingProof`. Worker 582 implemented these derived
identities for the actual published matrices in `QuotientIntegrals` and
`UnequalRankSmearingUnipotent`. They are proved here, without a conjugation
or character identity as an additional hypothesis.

For a field `F`, put
`N = n + ((j+1) + k + 1) + 1`, `c = n+j+2`,
`B = unequalRankMatrix (j+1) k g X`, and
`E = unequalRankSmearingEntries n j k z`.
Indices are zero based. The block sizes of `B` are `n+1`, `j+1`, `k+1`;
`E` is supported in column `c`, with entry `z i` in each leading row
`i < n+1`. Thus the actual smearing unipotent has value `I+E`.
All parameters `n,j,k` may be zero.

`unequalRankMatrix_trailing_row` proves that the rows of `B` at or after
`c` are identity rows. Since `E` uses only row `c` when multiplying on the
right, `unequalRankSmearingEntries_mul_block` gives `E B = E`.
Multiplication by the inverse gives `E B⁻¹ = E`, and hence
`unequalRankSmearingConjugate_val` proves

`B (I+E) B⁻¹ = I+B E`.

The group element on the left is defined as `unequalRankSmearingConjugate`.
No formula for the entries of `B⁻¹` is needed.

`mul_unequalRankSmearingEntries_apply` expresses the only possibly nonzero
column of `A E` as
`(A E)[a,c] = ∑ i : Fin (n+1), A[a,i] * z i`.
The private `sum_initial` lemma restricts this finite sum to its leading
coordinates. For `A = B`, rows at or after `c` vanish in this product
(`block_mul_unequalRankSmearingEntries_trailing`). It follows that `B E`
is strictly upper triangular, so
`unequalRankSmearingConjugate_mem_upperUnipotent` proves membership in the
actual `upperUnipotent N F`. The definition `unequalRankSmearingUpper`
packages this element with its membership proof.

Only the adjacent entry in row `c-1 = n+j+1` can contribute to the
standard character. The middle-leading block entries of `B` are precisely
`X`, as proved by `unequalRankMatrix_middle_leading_entry`. Therefore
`unequalRankSmearingUpper_superdiagonalSum` gives the adjacent-entry sum
`∑ i, X (Fin.last j) i * z i`.
For a unitary additive character `ψ`, field commutativity converts this
to the actual `rowPairing z (X (Fin.last j))`. The theorem
`unequalRankSmearingUpper_character` identifies the actual
`standardCharacter` with
`ψ.complex (rowPairing z (X (Fin.last j)))`, with the plus sign.

Finally, `unequalRankMatrix_smearing_coefficient` uses
`B U(z) = (B U(z) B⁻¹) B` and the covariance property of a coefficient
in `coefficientModel π ℓ` to prove

`f(B U(z)) = ψ.complex (rowPairing z (X (Fin.last j))) * f(B)`.

This identity needs no smoothness or topology on the representation carrier;
the field and representation universes are independent. A topology on the
field is used only to supply the published unitary-character type. Averaging,
integrability, and the Fourier cutoff are proved in the companion modules.

The source calculation is Jacquet, Piatetski-Shapiro and Shalika,
*Automorphic Forms on GL(3) I* (1979), Lemma 4.1.5, printed p.189:
the displayed matrices are conjugated and the resulting character is `ψ(zx)`.
The higher-rank version is the lemma inside the proof of Theorem 2.7 in
their *Rankin-Selberg Convolutions* (1983), printed pp.394–395, whose
proof refers to the 1979 argument. Both displays were inspected visually.
The retained source identifiers, hashes and complete locators are recorded
in [the proof documentation](UnequalRankFourierSmearingProof.md).
The entrywise finite-sum proof and its named intermediate identities are
internal derivations; neither paper states these Lean interfaces verbatim.

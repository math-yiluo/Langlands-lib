# The upper-column unipotent for unequal-rank JPSS smearing

This derived definition/API unit constructs actual invertible matrices over an
arbitrary field `F`. All declarations are in `Langlands.RankinSelberg`.

For natural numbers `n`, `j`, `k`, put `N = n + ((j+1) + k + 1) + 1`.
The leading block has `n+1` coordinates, the rectangular block has `j+1` rows
at zero-based indices `n+1` through `n+j+1`, and the immediately following
coordinate is `c = n+j+2`. In particular `c < N` even when `k = 0`.
The indices agree with `unequalRankMatrix (j+1) k g X` in
`Langlands.Representation.RankinSelberg.QuotientIntegrals`.

For `z : Fin (n+1) → F`, `unequalRankSmearingEntries n j k z` is the matrix
`E(z)` whose `(a,b)` entry is `z[a]` if `a < n+1` and `b = c`, and is zero
otherwise. `unequalRankSmearingUnipotent n j k z` is the element of
`GeneralLinear N F` with value `I + E(z)` and inverse `I - E(z)`.
`unequalRankSmearingUnipotent_apply` gives its full entry formula;
`unequalRankSmearingUnipotent_val` and
`unequalRankSmearingUnipotent_inv_val` expose the value and inverse matrices.

The cross-product identity `unequalRankSmearingEntries_mul` proves
`E(z) E(z') = 0` by evaluating the matrix product: a nonzero entry in the
first factor would require the intermediate index to be `c`, whereas the
second factor requires that index to be less than `n+1`.
`unequalRankSmearingEntries_sq` specializes this to square-zero, verifying both
inverse equations. Additivity of `E` and vanishing of the cross product give
`unequalRankSmearingUnipotent_add`, namely `U(z+z') = U(z) U(z')`.
`unequalRankSmearingUnipotent_zero` identifies `U(0)` with the identity.
Since every supported entry is strictly above the diagonal,
`unequalRankSmearingUnipotent_mem_upperUnipotent` proves membership in the
Library's actual upper-unipotent subgroup, with all diagonal entries one.
No positivity hypotheses on `n`, `j`, or `k` are imposed; each can be zero.

Given `[TopologicalSpace F] [IsTopologicalRing F]`,
`continuous_unequalRankSmearingEntries` is proved by continuous coordinate
projections and constant zero entries. Then
`continuous_unequalRankSmearingUnipotent` uses continuity of both `I+E(z)` and
`I-E(z)` in the topology of matrix units. These hypotheses include any supplied
topological field structure; no topology or measure is chosen.

The provenance is the displayed upper-column matrix in the Fourier-smearing
lemma within the proof of Theorem 2.7 of Jacquet, Piatetski-Shapiro and Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
printed pp.394–395, registered source `jpss-1983-rankin-selberg`. With their
leading rank `t = n+1` and middle block size `j_source = j+1`, that display is
exactly `I + E(z)` in these zero-based Library coordinates. Their final trailing
block has size `k` and may be empty. The related rank-one construction is the
matrix `u` in Lemma 4.1.5 on printed p.189, used in Proposition 4.1.4 on
pp.188–190 of the same authors' *Automorphic Forms on GL(3) I*, Annals of
Mathematics 109 (1979), registered source `jps-1979-gl3-i`.

The all-rank entry formula, explicit inverse, and algebraic and continuity
lemmas here are derived from the displayed source construction; neither paper
names this all-rank Lean API. This module establishes no Fourier closure,
Fourier inversion, coefficient cutoff, conjugation-character formula, or
adjacent-span equality. Those arguments require further hypotheses and proofs.

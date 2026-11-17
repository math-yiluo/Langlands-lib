# Normalized simple-root directions for Whittaker derivatives

This internal helper derives elementary diagonal identities from the published
column-matrix and Whittaker character-derivative constructions. It makes no
claim to construct an adelic gauge or prove Mellin convergence.

`diagonal_conj_simpleRootColumn` computes the conjugate of a column direction
supported at the simple root `(i,i+1)`. Multiplying that direction by the
adjacent diagonal ratio cancels the two diagonal factors in conjugation. The
proof checks matrix entries using the diagonal multiplication formulas and the
inverse identities for units.

`colConj_diagonal_mul_simpleRoot` applies this matrix identity to the
archimedean coordinates of an adelic product `a k`, when `a` is diagonal at
infinity. The normalized conjugated direction depends only on `k`.

`colFrequency_padRow_one_single` computes the character frequency for the
identity rational block and a direction in row `i`. The padded identity row
selects this entry, so the frequency is the mixed trace of the character
parameter times that entry. The proof reduces the sum to its one nonzero
summand.

`exists_simpleRoot_frequency_moment_bound` assumes a common determinant
exponent for all vectors of the decay class. For a fixed derivative order,
vector, compact set of right factors, and norm bound on the direction, it
bounds every normalized simple-root character-frequency moment times the
Whittaker norm by that same determinant power. The constant is independent
of the diagonal point, the simple-root index, the direction within its norm
bound, and the standard additive character (with its rational parameter).

The proof bounds entries of the right factor and its inverse on the compact
set, then bounds the conjugated unscaled column matrix. The diagonal identity
identifies this matrix with the conjugated normalized column at the original
point. The iterated character-derivative identity equates its Whittaker
function with `(2π i L)^N W`. Apply the determinant-power derivative-word
estimate and use `2π ≥ 1` to remove the harmless Fourier constant. These
frequency moments are preparatory estimates; constructing a Schwartz–Bruhat
majorant and proving quotient integrability remain separate obligations.

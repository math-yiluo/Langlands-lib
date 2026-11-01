# Cancellation of the final-column Fourier transforms

Worker 1198. Internal derived adapter for JPSS Section 6.2 Lemma (2).
`rectangularFixedLastColumn` restricts a rectangular Schwartz-Bruhat function to a fixed last column; the first-column projection is a continuous left inverse, so this restriction is Schwartz-Bruhat. The map is complex-linear.

`rectangularFourierEquiv_partial_fixedLastColumn` proves that full plus Fourier after inverse-character final-column Fourier, evaluated at `[A,b]`, equals square plus Fourier of the original fixed-column slice at `b`, evaluated at `A`. The proof uses the published finite scalar entry-tensor decomposition. The two transforms on each last-column factor cancel by scalar self-duality and Haar negation invariance. The first-column factors undergo only their scalar plus Fourier transforms. Linearity extends this computation to every rectangular Schwartz-Bruhat function, including dimension zero. All additive measures are the products of the supplied scalar Haar. No unipotent Haar comparison is used in this adapter.

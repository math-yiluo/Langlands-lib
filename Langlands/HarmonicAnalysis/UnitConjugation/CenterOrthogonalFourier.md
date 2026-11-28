# The Fourier transform on the orthogonal of the center

The module `Langlands.HarmonicAnalysis.UnitConjugation.CenterOrthogonalFourier` sets up Fourier
analysis on `V = z^⊥`, the trace-form orthogonal of the center `z` of a finite-dimensional
semisimple algebra `A` over a nonarchimedean local field `F` of characteristic zero. All
declarations are in the namespace `Langlands.HarmonicAnalysis.UnitConjugation`.

## Results

- `centerOrthogonalPairing`: the restriction of the trace form `B₀` to `V`; it is symmetric
  (`centerOrthogonalPairing_isSymm`), nondegenerate (`centerOrthogonalPairing_nondegenerate`,
  since the orthogonal of `V` is `z` by `orthogonal_centerOrthogonal` and `V ∩ z = 0`) and
  invariant under conjugation (`centerOrthogonalPairing_conj`).
- Instances `isFiniteDimensionalOverLocalField_centerOrthogonal` and
  `isFiniteDimensionalOverLocalField_centerSubmodule` (the Library's
  `IsFiniteDimensionalOverLocalField`, giving compact open exhaustions, Hausdorffness, local
  compactness and second countability).
- `det_mul_self_of_preserves`: a linear automorphism preserving a nondegenerate bilinear form
  has determinant `±1` (comparing the form with its pullback through the dual map);
  `measurePreserving_centerOrthogonalConj`: hence conjugation preserves every Haar measure on
  `V`, by the Library's `map_linearEquiv_addHaar`.
- `centerOrthogonalFourier ψ μ`: the Library's Fourier transform `pairingFourierSB` on `V`,
  `β̂(Y) = ∫_V ψ(B₀(Y, X)) β(X) dμ(X)`.
- `fourier_pullback_centerOrthogonalConj`: the Fourier transform commutes with conjugation (a
  change of variables with the invariance of `B₀` and of `μ`).
- `fourier_scalarDilation`: `(β_s)^ = |s|^{dim V} (β̂)_{s⁻¹}` with `|s| = distribHaarChar F s`;
  the change of variables `X = s X'` multiplies Haar measure by
  `distribHaarChar F (det(s · id)) = |s|^{dim V}`.
- `productHaar μz μV`: the Haar measure on `A` transported from `μz × μV` along
  `centerDecomposition`; `restrict_fourier_extendTest`: for this measure and the trace form,
  the restriction to `V` of the Fourier transform of `extendTest α β` is `(∫_z α) β̂`, because
  `B₀(Y, Z + X) = B₀(Y, X)` for `Y, X ∈ V` and central `Z`, and the integral over `z × V`
  of a product is the product of the integrals (Mathlib's `integral_prod_mul`).

## Source

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, with notes by
S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions`: Introduction, printed p. 2 (the
Fourier transform for a symmetric nondegenerate invariant form `B` and a character `χ` of the
additive group), and §3.5, printed p. 29 (PDF p. 44): `(f_t)^ = |t|^n (f̂)_{t⁻¹}`.

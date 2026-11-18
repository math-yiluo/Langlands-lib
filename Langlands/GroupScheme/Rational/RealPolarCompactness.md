# Compactness of real points from bounded torus factors

This helper module proves that the real points of a connected reductive group over `ℝ` are
compact when all its closed tori have bounded matrices.

## Declarations

- `RealPolar.posDef_eq_one`: let `P : GL n ℝ` be positive definite. If every nonnegative
  eigenvalue of `P` and of `P⁻¹` (with a nonzero eigenvector) is at most `1`, then `P = 1`.
  Proof: each eigenvalue `λ > 0` of `P` satisfies `λ ≤ 1`, and `λ⁻¹` is an eigenvalue of
  `P⁻¹`, so `λ⁻¹ ≤ 1`. Hence all eigenvalues are `1`, and the spectral theorem
  (`Matrix.IsHermitian.spectral_theorem`) gives `P = 1`.
- `RealPolar.compactSpace_of_torusBound G hG hbound` (main result): let
  `G : GroupScheme (Spec (CommRingCat.of ℝ))` with `[IsAffine G.X.left]` and
  `IsConnectedReductive G`. Assume `hbound`: for every `d`, every
  `ρ : MatrixRepresentation G (Fin d)` and every closed torus `i : T ⟶ G`, the entries of
  `ρ(i(s))` are bounded uniformly in the real points `s` of `T`. Then
  `G.affinePoints (CommAlgCat.of ℝ ℝ)`, with the evaluation topology
  `G.affinePointsTopologicalSpace`, is a compact space.

## Proof of the main result

`connectedReductiveSelfAdjointRealizationStatement` gives a closed representation `ρ` whose
real image is stable under transpose. For a real point `g`,
`exists_affineUnitary_right_quotient_posDef` gives `a` in the unitary part
`K = ρ.affineUnitarySubgroup` with `P = ρ(g a⁻¹)` positive definite. By
`RealPolar.eigenvalue_le_one` (applied to `g a⁻¹` and to its inverse, after converting points
with `GaloisPointComparison.rationalCoeffEquiv` and
`Langlands.Plancherel.rationalMatrix_eq_affineMatrix`), every nonnegative eigenvalue of `P`
and of `P⁻¹` is at most `1`. So `P = 1` by `posDef_eq_one`, and `g = a ∈ K` because
`ρ` is injective on real points (`isClosedEmbedding_affineMatrix`). Thus `G(ℝ) = K`, which is
compact (`isCompact_affineUnitarySubgroup`).

## Provenance (internal)

An internal step of the compactness half of `RealAnisotropicCompactConnectedStatement`
(Borel–Tits, *Groupes réductifs* (1965), Corollary 9.4, printed p.127, for `k = ℝ`). The
route (polar decomposition and growth of powers) was written for this development and is
not the argument of Borel–Tits.

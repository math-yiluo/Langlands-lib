# The symplectic space of the unitary dual pair

**GKT §10.5** (Theorem 10.28, p. 288: the symplectic space `𝕎 = W ⊗ V` of a Type I pair, Case `3`)
and **§12.4.1** (the polarization `𝕎 = 𝕏^* ⊕ 𝕏` of `W ⊗ V` for split `W`, p. 369), in matrix form
for Case `3₊`, with the form `½ tr_{E/F}` of the book's `tr_{E/F}`.

The module `Langlands.Theta.DualPair.Unitary.Form` defines the symplectic space of the dual pair
`(U(Q), U(ν, ν))` over a quadratic extension of local fields, its polarization by a Hermitian
pairing, and the action of `U(ν, ν)` on its Heisenberg group (GKT (2.1), p. 47). The Schrödinger
representation is in `Langlands.Theta.DualPair.Unitary.Schrodinger`.

## Content

Let `E / F` be fields with an `F`-algebra map `c : E → E` (the conjugation of a quadratic
extension), `Q` an `α × α` matrix over `E` (Hermitian: `Matrix.IsHermitianFor c Q`), and
`J = UnitaryGroup.hyperbolicForm ν E` the hyperbolic skew-Hermitian form.

- `hermitianTensor c JA JB x y = ∑ x_{ij} JA_{ik} JB_{jl} c(y_{kl})`: the sesquilinear form on
  `M_{α×β}(E) = E^α ⊗ E^β` which is the tensor product of the forms with Gram matrices `JA`, `JB`.
- `hermitianSymplecticForm c Q w w' = ½ tr_{E/F} hermitianTensor c Q J w w'` on `W = M_{α×2ν}(E)`;
  for Hermitian `Q` and involutive `c` it is alternating, and `U(ν, ν)` preserves it by right
  multiplication (`hermitianSymplecticForm_mul`). This is the symplectic space `E^α ⊗_E E^{2ν}`
  restricted to `F` of the dual pair; it is one half of the book's form
  `⟪w ⊗ v, w' ⊗ v'⟫ = tr_{E/F}(⟨w, w'⟩ \overline{(v, v')})` of GKT Theorem 10.28.
- `hermitianPairing c Q : M_{α×ν}(E) →ₗ[F] M_{α×ν}(E) →ₗ[F] F`,
  `(x, y) ↦ ½ tr_{E/F} tr(Qᵀ x c(y)ᵀ)` (`hermitianPairing_apply`); it is
  `hermitianSymplecticForm c Q (x, 0) (0, y)` (`hermitianPairing_eq_hermitianSymplecticForm`), and
  splitting `W` into its first and last `ν` columns identifies the symplectic form with the
  polarized form of the pairing: `hermitianSymplecticForm c Q (x, y) (x', y') = β x y' - β x' y`
  (`hermitianSymplecticForm_fromCols`). So `M_{α×ν}(E) × 0` and `0 × M_{α×ν}(E)` are complementary
  Lagrangians, and the Heisenberg group of `W` is `HeisenbergGroup (polarizedForm (hermitianPairing c Q))`
  (`Langlands/Theta/Heisenberg/Schrodinger.lean`).
- `UnitaryGroup.rightMulInvEquiv c g`: `(x, y) ↦ (x, y) g⁻¹`, an `F`-linear automorphism of
  `M_{α×ν}(E)²` (`rightMulInvEquiv_apply`), preserving `polarizedForm (hermitianPairing c Q)`
  (`polarizedForm_rightMulInvEquiv`); `UnitaryGroup.heisenbergAction c hc hQ` is the resulting
  homomorphism `U(ν, ν) →* MulAut (HeisenbergGroup _)`, `g · (w, t) = (w g⁻¹, t)`
  (`heisenbergAction_apply`), built from `HeisenbergGroup.mapEquiv`. The inverse makes the right
  multiplication a left action. `UnitaryGroup.val_inv_mul_val`, `val_mul_val_inv`: the matrices of
  `g⁻¹` and `g` are inverse.

The internal part (namespace `Langlands.Theta.Unitary.Internal`) carries the computations with the
form (`form_mul`, `form_add_left`, `form_swap`, …, `continuous_form_left`), the matrix of an element
of `U(ν, ν)` (`mat`, `mem_sieg`), and the pairing `pr` with its properties (`pr_alg`: bilinear,
symmetric, non-degenerate for invertible Hermitian `Q`, and `β(x a, y) = β(x, y c(a)ᵀ)`). The
topology of `E` comes from `Langlands.HarmonicAnalysis.QuadraticExtensionTopology`.

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`, under
`src/Development/AbelianVarietyTheory/`: `PublishedTheorems/TwistedTraceFormula/KudlaSplittingSplitUnitary.lean`,
lines 76–212 (`form`, the lemmas on `form`, `continuous_form_left`; the operators `heisFun` of the
same lines are in `Langlands.Theta.DualPair.Unitary.Schrodinger`);
`Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean`, lines 173 (`IsHerm`) and 326–327
(`hTens`); `Definitions/Divisors/UnipVal.lean`, lines 53 (`pr`), 76–108 (`mat`, `mat_inv`,
`mem_sieg`); `Proofs/DivisorProofs/HermitianMatrixColumnPairingAlgebraicProperties.lean` (whole).
The source's `Proofs/DivisorProofs/QuadExtTopology.lean` is in
`Langlands/HarmonicAnalysis/QuadraticExtensionTopology.lean`. The repository
has no licence file; the text is used with attribution, see
`licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespaces `GlobalTheory.SplitUnitary`, `GlobalTheory.KSp`, `GlobalTheory.WeilM` →
  `Langlands.Theta` (public), `Langlands.UnitaryGroup` (the action) and
  `Langlands.Theta.Unitary.Internal`.
- Renamed: `hTens` → `hermitianTensor`, `form` → `hermitianSymplecticForm`, `prLin` →
  `hermitianPairing` (public; the function `pr` stays internal), `form_mul` →
  `hermitianSymplecticForm_mul`; `quadExt_topological_properties` (a wrapper),
  `isSelfDualCompactOpenGroup_of_finiteDimensional` and the source's `Good` (`UnipVal.lean`,
  lines 17–25) are replaced by the lemmas `IsQuadraticInvolution.isTopologicalRing`, … of
  `Langlands.HarmonicAnalysis.QuadraticExtensionTopology` and the Library's
  `compactOpenExhaustion_of_finiteDimensional` and companions.
- `stdJ` → `UnitaryGroup.hyperbolicForm` (`Langlands/Group/Unitary/Hyperbolic.lean`); `SB` →
  `schwartzBruhatSubmodule`; the source's `isLocallyConstant_addChar` and `nonarch_field` → the
  Library's `isLocallyConstant_of_continuous_addChar` and instance.
- `form_swap` assumes only that `Q` is Hermitian (the source: Hermitian and invertible).
- New: `hermitianSymplecticForm_fromCols`, `UnitaryGroup.rightMulInvEquiv`,
  `UnitaryGroup.heisenbergAction` and their lemmas.

## Declarations

- `Langlands.Theta.hermitianTensor`, `hermitianSymplecticForm`, `hermitianSymplecticForm_fromCols`,
  `hermitianSymplecticForm_mul`
- `Langlands.Theta.hermitianPairing`, `hermitianPairing_apply`,
  `hermitianPairing_eq_hermitianSymplecticForm`
- `Langlands.UnitaryGroup.val_inv_mul_val`, `val_mul_val_inv`, `rightMulInvEquiv`,
  `rightMulInvEquiv_apply`, `polarizedForm_rightMulInvEquiv`, `heisenbergAction`,
  `heisenbergAction_apply`

## Dependencies

`Langlands.Group.Unitary.Hyperbolic`, `Langlands.Theta.Heisenberg.Schrodinger` (`polarizedForm`),
`Langlands.HarmonicAnalysis.QuadraticExtensionTopology`,
`Langlands.HarmonicAnalysis.Bicharacter.SelfDual`, `Langlands.HarmonicAnalysis.LinearHaarScaling`;
Mathlib: `RingTheory.Trace.Basic`, `Data.Matrix.ColumnRowPartitioned`,
`Topology.Algebra.Module.ModuleTopology`.

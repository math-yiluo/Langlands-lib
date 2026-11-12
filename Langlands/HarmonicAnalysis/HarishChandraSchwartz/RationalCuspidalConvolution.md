# Functions with vanishing constant term and wave packets on actual points (Waldspurger, proof of Lemma VIII.2.3)

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module:
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalConvolution`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedConstantTermFourier` (this
  author's Unit 26, candidate `dad71a9b-6886-4dca-86a4-ff7b4af9f7cd`, review-accepted, not yet in
  the Library). From it this module uses `integrable_rationalCoefficientPairingIntegrand` (the
  absolute convergence in the proof of Lemma VII.1.2) and `rationalLeviL2Weights`. Through its
  imports come the published units: `rationalInducedOrbitWavePacket` (`f_ψ`),
  `rationalInducedSmoothOrbitSections` (`C^∞(O, P)`), `leviRationalUnitaryCoordinates` with
  `_hasLaurent`, `compactOpenCofinal_standardLevi`, `rationalLeviXi_inv`,
  `rationalLeviTranslationWeights`, `RationalSchwartzSpace`, `rationalXi`, `rationalL2Weights`,
  `rationalXi_inv`, `rationalHeight_inv`, `rationalHasTemperedCoefficients_normalizedInduction`,
  `IsRationalLeviTempered`, `rationalLeviXi`, `rationalLeviData`, `rationalMinimalModulus_eq_one`,
  `isUnimodularModulus_standardUnipotentPoints`, and from `RationalConstantTerm` the actual
  constant term `rationalConstantTerm` with `rationalConstantTermData`, `rationalIsConjModulus` and
  `rationalTranslationWeights`.
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalConvolution` (Library):
  `IsUnipotentCuspidal`, `constantTermIndVanishes_of_isUnipotentCuspidal`,
  `isUnipotentCuspidal_of_constantTermIndVanishes`, `convolution_inducedOrbitWavePacket_eq_zero`,
  `convolution_inducedOrbitWavePacket_left_eq_zero`, and `Space.complexConj`.
- `Langlands.Group.GL.LeviCentralQuotientMeasure` (Library):
  `isInvInvariant_of_isMulRightInvariant`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers are printed
pages; the PDF page is the printed page minus 234. The author checked the quotations below on
the rendered images of PDF pages 38, 87 and 88. Overlines in the source (complex conjugation) are written
`\overline{…}`.

- III.6, printed p. 272: "On définit un homomorphisme `G × G` équivariant
  `C(G) → I_{P×P}^{G×G} C(M)`, `f ↦ f^{(P),Ind}` par
  `f^{(P),Ind}(g_1, g_2) = (ρ(g_1)λ(g_2)f)^{(P)}` pour tous `g_1, g_2 ∈ G`."
- Lemma VIII.2.1, printed p. 321: "Pour `f ∈ C(G)`, `f` appartient à `°C(G)` si et seulement si
  `f^{(P),Ind} = 0` pour tout sous-groupe parabolique semi-standard propre `P` de `G`."
- Lemma VIII.2.3, printed p. 322: "Pour `f_1 ∈ °C(G)` et `f_2 ∈ C(G)`, on a les égalités
  `f_1 ∗ f_2 = f_1 ∗ °f_2`, `f_2 ∗ f_1 = °f_2 ∗ f_1`."
- Its proof, printed p. 322: "Il suffit de prouver que si `(O, P) ∈ Θ`, `P ≠ G`, et si
  `ψ ∈ C^∞(O, P)`, on a `f_1 ∗ f_ψ = f_ψ ∗ f_1 = 0`. Soit `g ∈ G`, notons `f'_1` la fonction
  définie par `f'_1(h) = \overline{f_1(gh^{−1})}`. On a l'égalité
  `(f_1 ∗ f_ψ)(g) = (f'_1, f_ψ)_G`. On montre comme en VII.2 (1) que
  `(f'_1, f_ψ)_G = ∫_O µ(ω)(\hat{f'_1}(ω, P), ψ_ω) dω`. Mais `f'_1 ∈ °C(G)` d'après le Lemme
  VIII.2.1, donc `\hat{f'_1}(ω, P) = 0` pour tout `ω`. On en déduit `f_1 ∗ f_ψ = 0`. Idem
  `f_ψ ∗ f_1 = 0`."

`CuspidalConvolution.md` (Library) explains how the abstract results relate to these statements.
This module adds no new analysis: it supplies the actual data of `P_I(F)`.

Correspondence:

- `RationalConstantTermIndVanishes … f` is the condition `f^{(P),Ind} = 0` of Lemma VIII.2.1 for
  the actual standard parabolic `P = P_I(F)`: for all `g₁, g₂ ∈ G(F)`,
  `rationalConstantTerm … (Space.translate … g₁ g₂ f) = 0`. Here `Space.translate … g₁ g₂ f` is
  `ρ(g₁) λ(g₂) f : x ↦ f(g₂⁻¹ x g₁)` and `rationalConstantTerm` is the actual constant term
  `f ↦ f^{(P)}`, `f^{(P)}(m) = δ_{U_I}(m)^{1/2} ∫_{U_I(F)} f(m u) du` (III.6). Lemma VIII.2.1 asks
  this for every proper semi-standard `P`; here it is one standard `P`.
- `isUnipotentCuspidal_iff_rationalConstantTermIndVanishes` says that this condition is
  equivalent to `∫_{U_I(F)} f(x u y) dν_U(u) = 0` for all `x, y ∈ G(F)` (the Library's
  `IsUnipotentCuspidal`). This form is the one the proof uses to see that `f'_1` again satisfies
  the condition (the source's "`f'_1 ∈ °C(G)` d'après le Lemme VIII.2.1").
- `convolution_rationalInducedOrbitWavePacket_eq_zero` is `f_1 ∗ f_ψ = 0` from the proof of Lemma
  VIII.2.3, and `convolution_rationalInducedOrbitWavePacket_left_eq_zero` is "Idem
  `f_ψ ∗ f_1 = 0`", for the orbit `O` of `π` and `P = P_I(F)`, with the hypothesis
  `f_1^{(P),Ind} = 0` for this `P` in place of `f_1 ∈ °C(G)`. The convolution is the Library's
  `convolution μG φ₁ φ₂ g = ∫ φ₁(h) φ₂(h⁻¹ g) dμG(h)` (III.6), and `f_ψ` is
  `rationalInducedOrbitWavePacket`, with a weight `w` on the orbit in place of `µ(ω)`, as in
  Unit 20.
- Not formalized here: `°C(G)`, Lemma VIII.2.1, `°f_2`, and Lemma VIII.2.3 itself (which also needs
  the wave-packet decomposition of `κ(ψ)` over all `(O, P)`).

## Setting

As in Unit 26, `RationalInducedConstantTermFourier.md`:

- `G` connected reductive over a nonarchimedean local field `F` (`hG`), with a maximal split torus
  `i` (`hi`), a generic cocharacter `ν` (`hν`) and `I` a finite set of simple roots; `P = P_I(F)`
  with Levi factor `M_I(F)` (the subtype `𝐌`) and unipotent radical `U_I(F)`; `𝐉` is local
  notation for `rootSet i ν I`;
- `K` an open subgroup with `hKc : IsCompact K` and `hPK : IsIwasawaPair P₀(F) K`;
- a matrix representation `ρ : MatrixRepresentation G (Fin N)` defining `σ = rationalHeight ρ`,
  so that `C(G) = RationalSchwartzSpace hKc hPK ρ` (the Library's `Space Ξ σ` for
  `Ξ = rationalXi hKc hPK`);
- `hM : IsIwasawaPair (P₀(F) ∩ M_I(F)) (K ∩ M_I(F))`, which defines `Ξ^{M_I} = rationalLeviXi`.

Section `Cuspidal` (the definition and the equivalence): a Haar measure `νU` on `U_I(F)` with
`hE : ConstantTermEstimate νU δ_{U_I} Ξ σ Ξ^{M_I} σ` (the conclusion of Proposition II.4.5), which
`rationalConstantTerm` needs.

Section `Convolution` (the two vanishing theorems), the data of Unit 26's section `Orbit`:

- `hρ : IsClosedSubgroup ρ` and `hKρ : K ≤ rationalHeightSubgroup ρ`;
- an irreducible admissible representation `π` of `M_I(F)`, a normal subgroup `C` of the centre
  (`hC`), a Haar measure `μM` on `M_I(F)/C` (inverse-invariant) with `hsq` (square integrable
  modulo `C`), `hTA` (temperedness of every representative `A` of the unitary unramified orbit of
  `π`, `UnitaryOrbitRepresentative (leviRationalNormCharacters i ν I) π`) and `hcoeffA`
  (Corollary III.1.2 for every such `A`);
- `μL` on `M_I(F)` (left and right invariant, inverse-invariant, s-finite) with
  `hswM : SquareIntegrableWeight μL Ξ^{M_I} σ` (Lemma II.1.5 for `M_I`) and
  `hMK : μL(M_I ∩ K) = 1`;
- a Haar measure `νU` on `U_I(F)`, right invariant and s-finite, with `hE` and
  `hUK : νU(U_I ∩ K) = 1`;
- `μG` on `G(F)` (left and right invariant, inverse-invariant, σ-finite) with
  `hsw : SquareIntegrableWeight μG Ξ σ` (Lemma II.1.5 for `G`) and `hμK : μG(K) = 1`;
- `[MeasurableInv 𝐌]` and `hPKiw : ∀ m n, m n ∈ K ↔ m ∈ K ∧ n ∈ K` (`P ∩ K = (M_I ∩ K)(U_I ∩ K)`);
- `[Finite]` for the stabilizer of the class of `π` in `Im X(M_I)`, a measure `ρX` on `Im X(M_I)`
  and a weight `w` on the orbit.

Each theorem takes in addition `[IsFiniteMeasure ρX]`, `hwm` (`w` a.e. strongly measurable for the
orbit measure), `hwb : ∀ ω, ‖w ω‖ ≤ b`, `hcoeff` (Corollary III.1.2 for `π`), a section
`q ∈ C^∞(O, P)`, `f₁ ∈ C(G)`, `h0 : RationalConstantTermIndVanishes … f₁` and `g ∈ G(F)`.

## Contents

- **`rationalUnipotentHaar_isInvInvariant νU`**: a right-invariant Haar measure `νU` on `U_J(F)`
  (any `J`) is invariant under inversion.
- **`RationalConstantTermIndVanishes hG hi hν I hKc hPK ρ hM νU hE f`** (definition, the recorded
  declaration): `∀ g₁ g₂ : G(F), rationalConstantTerm … (Space.translate … g₁ g₂ f) = 0`.
- **`isUnipotentCuspidal_iff_rationalConstantTermIndVanishes … f`**:
  `IsUnipotentCuspidal νU f ↔ RationalConstantTermIndVanishes … f`, where
  `IsUnipotentCuspidal νU f` is `∀ x y, ∫ u, f(x u y) dνU(u) = 0`.
- **`convolution_rationalInducedOrbitWavePacket_eq_zero … hwm hwb hcoeff q f₁ h0 g`**:
  `convolution μG f₁ (rationalInducedOrbitWavePacket … π … ρX w q) g = 0`.
- **`convolution_rationalInducedOrbitWavePacket_left_eq_zero … hwm hwb hcoeff q f₁ h0 g`**:
  `convolution μG (rationalInducedOrbitWavePacket … π … ρX w q) f₁ g = 0`.

## Proofs

- `rationalUnipotentHaar_isInvInvariant`: `U_J(F)` is closed in `G(F)`
  (`isClosed_standardUnipotentPoints`), hence locally compact; it is second countable and
  metrizable as a subspace, so `νU` is regular
  (`Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure`); then
  `isInvInvariant_of_isMulRightInvariant`.
- The equivalence: forward, `constantTermIndVanishes_of_isUnipotentCuspidal` with
  `rationalConstantTermData`, `hE` and the translation weights, unfolded to
  `rationalConstantTerm`; backward, `isUnipotentCuspidal_of_constantTermIndVanishes` with
  `fun x => h0 x.1 x.2`.
- The two convolution theorems apply `convolution_inducedOrbitWavePacket_eq_zero` and
  `convolution_inducedOrbitWavePacket_left_eq_zero` to the actual data of `P_I(F)` (as in Units
  20–26): the semidirect decomposition `isSemidirectDecomposition_standard`, closedness of
  `U_I(F)` and `P_I(F)`, the factorization `G = P K`, unimodularity of `G(F)` and `U_I(F)`, the
  modulus of `P_I(F)`, the norm characters and circle coordinates of Unit 20 with their Laurent
  property and continuity, `compactOpenCofinal_standardLevi`, `rationalL2Weights … hsw`,
  temperedness of the induced representations from
  `rationalHasTemperedCoefficients_normalizedInduction`, `rationalLeviData`,
  `rationalMinimalModulus_eq_one`, `rationalLeviL2Weights … hswM`, the constant-term data
  `rationalConstantTermData` and `rationalIsConjModulus`, the translation weights and the
  normalizations. Cuspidality of `f₁` comes from `h0` by the equivalence, and inversion invariance
  of `νU` from `rationalUnipotentHaar_isInvInvariant`. The Library lemma's integrability
  hypothesis, for `f'_1 = \overline{ρ(g⁻¹)(f₁ˇ)} : h ↦ \overline{f₁(g h⁻¹)}` (respectively
  `\overline{λ(g)(f₁ˇ)} : h ↦ \overline{f₁(h⁻¹ g)}` for the left convolution), is supplied for each
  representative `A` by `integrable_rationalCoefficientPairingIntegrand … (hcoeffA A) hsw`. The goal
  is unfolded to `inducedOrbitWavePacket` and closed by `with_reducible_and_instances exact`.

## Scope and hypotheses

- Only standard parabolics `P_I ⊇ P₀` are covered, and the results concern one parabolic and one
  orbit; the hypothesis is `f₁^{(P),Ind} = 0` for this `P`, not `f₁ ∈ °C(G)`.
- Analytic inputs whose actual statements are published but unproved enter as hypotheses: `hsw`
  and `hswM` (Lemma II.1.5 for `G` and `M_I`), `hE` (Proposition II.4.5), `hTA` (temperedness),
  `hcoeff` and `hcoeffA` (Corollary III.1.2 for `π` and for each representative of its orbit; the
  bound for the representatives is not derived from the bound for `π`).
- The structural fact `hPKiw` (ledger row S5) and the measure normalizations `hμK`, `hMK`, `hUK`
  are hypotheses, as in Lemma VII.1.2 of the Library.
- `K`, `hPK`, `hM`, `ρ`, `hρ`, `hKρ` are data (ledger rows S3, S4, S5).
- The Plancherel density `µ` (V.2) is not formalized; the wave packet uses the weight `w`.

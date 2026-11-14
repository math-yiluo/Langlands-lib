# Wave packets detect `ψ_f[O, P]` on actual points, for a weight positive on a dense set (Waldspurger VII.2, proof of Corollary VII.2.3)

Author: Worker 5, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module:
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitWavePacketOrthogonalityDense`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitWavePacketOrthogonality`
  (Library, Worker 3642). This module copies that module's setting (section variables, local
  instances, notation and `include` lists). Through its imports come
  `rationalFourierOrbitSmoothSectionLinear` with `_val`, `rationalFourierOrbitSection` with
  `_apply`, `rationalInducedOrbitWavePacket`, `rationalInducedSmoothOrbitSections`,
  `leviRationalUnitaryCoordinates` with `_hasLaurent`, `rationalInducedFourierTransform` and the
  actual data of `P_I(F)`. `RationalInducedOrbitWavePacketOrthogonality.md` describes them.
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedOrbitWavePacketOrthogonalityDense`
  (same candidate). It provides `unitaryOrbitWeightedProductCore_of_dense` and
  `fourierOrbitSection_eq_zero_iff_forall_pairing_inducedOrbitWavePacket_eq_zero_of_dense`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers are printed
pages.

- V.2 and Lemma V.2.1, first item, printed p. 292: `µ(ω) = j(ω)^{-1} ∏_α γ(M_α|M)^2`, and
  "Pour tout `ω ∈ O`, on a `µ(ω) ⩾ 0`".
- Corollary VII.2.3, its proof, formula (1) of the proof of Proposition VII.2.2 and the product
  of VII.2, all printed p. 319, quoted in `RationalInducedOrbitWavePacketOrthogonality.md`. The
  product is a sum of terms `∫_O µ(ω) (ψ'[O, P]_ω, ψ[O, P]_ω) dω`, and the source says: "Cela
  définit un produit hermitien défini positif".

## Provenance

The statements are those of `RationalInducedOrbitWavePacketOrthogonality` with the hypothesis
`hupos : ∀ ω, 0 < u ω` replaced by `hu0 : ∀ ω, 0 ≤ u ω` and `hud : Dense {ω | 0 < u ω}`. This
change is internal derived content, not a statement of the paper. The source's weight is the
Plancherel density `µ`. It is only `≥ 0` on `O` (Lemma V.2.1) and vanishes at a unitary `ω` where
`j` has a pole, so it need not satisfy `hupos`. `InducedOrbitWavePacketOrthogonalityDense.md`
explains why `hu0` and `hud` suffice for the definiteness of the weighted product.

The correspondence with the source is the one in `RationalInducedOrbitWavePacketOrthogonality.md`
("Correspondence"). The roles of `O`, `P = P_I(F)`, `q` and `f`, and the conclusion at each
representative, are unchanged. Only the hypotheses on the weight `u` differ.

## Setting

The setting is that of `RationalInducedOrbitWavePacketOrthogonality.md` ("Setting"): `G`, `i`,
`ν`, `I`, `K`, `hKc`, `hPK`, `π`, `C`, `hC`, `μM`, `hsq`, the two finiteness instances, the measure
`ρX` on `Im X(M_I)` and the real weight `u : O → ℝ`. The two theorems also use, through
`include`, all the hypotheses of `rationalFourierOrbitSmoothSectionLinear`. The three local
instances are those of the Library module, renamed
`instRationalInducedOrbitWavePacketOrthogonalityDense1`–`3`.

The core and the theorems take:

- `[IsFiniteMeasure ρX]` and `[ρX.IsOpenPosMeasure]`;
- `hu : Continuous u`;
- `hu0 : ∀ ω, 0 ≤ u ω` and `hud : Dense {ω | 0 < u ω}`;
- a real `b` and `hub : ∀ ω, u ω ≤ b`.

The two theorems also take `hcoeff` and `f : RationalSchwartzSpace hKc hPK ρ`, and the last one
takes `h0` and a representative `A`.

## Contents

Write `f_ψ = rationalInducedOrbitWavePacket … ρX (fun ω => (u ω : ℂ)) q` for the actual wave
packet of weight `u` of `q ∈ C^∞(O, P)`, and `(φ₁, φ₂)_G = pairing μG φ₁ φ₂`.

- **`rationalUnitaryOrbitWeightedProductCore_of_dense … ρX u hu hu0 hud hub`** (definition, the
  recorded declaration, `@[instance_reducible]`):
  `InnerProductSpace.Core ℂ (rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)`. It is
  `unitaryOrbitWeightedProductCore_of_dense` with the actual data of `P_I(F)` and the circle
  coordinates `leviRationalUnitaryCoordinates`. As for every `InnerProductSpace.Core`, it is
  conjugate-linear in the first argument, additive, hermitian, with nonnegative real part on the
  diagonal, and definite.
- **`rationalUnitaryOrbitWeightedProductCore_of_dense_inner`**: its inner product is
  `⟪q, r⟫ = ∫_O u(ω) (q_ω, r_ω) dω`, the measure being `discreteSeriesOrbitMeasure` for `ρX`
  (by `rfl`).
- **`rationalFourierOrbitSection_eq_zero_iff_forall_pairing_rationalInducedOrbitWavePacket_eq_zero_of_dense
  … hu hu0 hud hub hcoeff f`**: `rationalFourierOrbitSection … f = 0` (that is,
  `ψ_f[O, P] = 0`) if and only if `(f_ψ, f)_G = 0` for every `q ∈ C^∞(O, P)`.
- **`rationalInducedFourierTransform_eq_zero_of_forall_pairing_rationalInducedOrbitWavePacket_eq_zero_of_dense
  … hu hu0 hud hub hcoeff f h0 A`**: if `h0 : ∀ q, (f_ψ, f)_G = 0`, then for every representative
  `A` of the orbit, `rationalInducedFourierTransform … A.val.obj … f = 0`, that is
  `f̂(A, P) = 0`.

## Proofs

The proofs are those of the Library module, with the dense versions of the generic results:

- The core is `unitaryOrbitWeightedProductCore_of_dense` applied to the same actual data as the
  Library's `rationalUnitaryOrbitWeightedProductCore`, with the local compactness of `P_I(F)`.
  `_inner` holds by `rfl`.
- The equivalence:
  1. `hsm : ψ_f[O, P] ∈ C^∞(O, P)` is the `property` of
     `rationalFourierOrbitSmoothSectionLinear … f`, rewritten with
     `rationalFourierOrbitSmoothSectionLinear_val`.
  2. `fourierOrbitSection_eq_zero_iff_forall_pairing_inducedOrbitWavePacket_eq_zero_of_dense` is
     applied with the actual data, `hu hu0 hud hub`, `hcoeff`, `f` and `hsm`.
  3. The goal is unfolded (`rationalFourierOrbitSection`, `rationalInducedOrbitWavePacket`,
     `delta rationalXi`) and closed by `with_reducible_and_instances exact`.
- The corollary rewrites `f̂(A, P)` as `ψ_f[O, P]_A` (`rationalFourierOrbitSection_apply`,
  backwards), replaces `ψ_f[O, P]` by `0` using the equivalence and `h0`, and closes by `rfl`.

## Intended use

The intended weight `u` is the Plancherel weight on the orbit. The module
`PlancherelWeightPositivity` (candidate `4a929a37-8a95-4d82-bca2-b20030228811`, not yet in the
Library) defines its real form `standardLeviPlancherelWeightReal`. It proves this weight
continuous and bounded. Assuming `j_P⁻¹` regular and nonnegative at the unitary characters, it
proves the weight nonnegative; assuming also `j_P ≠ 0`, positive on a dense open set. This module
does not import it, and the instantiation is left to a later unit.

## Scope and hypotheses

- Only standard parabolics `P_I ⊇ P₀` are covered.
- Corollary VII.2.3 itself is not proved: as in the Library module, the vanishing hypothesis `h0`
  is Proposition VII.2.2 (i), which is not proved on actual points.
- This module does not show that the Plancherel weight satisfies `hu`, `hu0`, `hud` and `hub`.
- The hermitian product on `C^∞(Θ)^inv` (the sum over `Θ` with its constants) and its `G × G`
  invariance are not formalized.
- The hypotheses inherited from `rationalFourierOrbitSmoothSectionLinear`, `hcoeff` and the
  finiteness instances are those listed in `RationalInducedOrbitWavePacketOrthogonality.md`
  ("Scope and hypotheses").

## Axioms

The results use only `propext`, `Classical.choice` and `Quot.sound`.

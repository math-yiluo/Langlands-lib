# Functions with vanishing constant term are orthogonal to wave packets (Waldspurger, Lemmas VIII.2.1 and VIII.2.3)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalWavePacketOrthogonality`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedConstantTermFourier` (Worker 249):
  `Space.constantTermInd` (`f^{(P),Ind}`), `constantTermInducedFourierTransform`
  (`f̂^{(P),Ind}(ω)`) and Lemma VII.1.2,
  `inducedFourierTransform_eq_constantTermInducedFourierTransform`; through it
  `coefficientFourierTransform`, `inducedFourierTransform`, `ConstantTermData`, `IsConjModulus`,
  `ConstantTermEstimate`, `TranslationWeights`, `L2Weights`, `HasTemperedCoefficients`;
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedOrbitWavePacketPairing`
  (Worker 249): `pairing_inducedOrbitWavePacket_eq_zero`, `factorization_mem_of_subtype`; through
  it `fourierOrbitSection` and `fourierOrbitSection_apply` (`InducedFourierCoherence`, the
  section `ψ_f[O, P]`), the wave packet `inducedOrbitWavePacket` (`OrbitWavePacket`), `pairing`
  (`(φ₁, φ₂)_G = ∫ conj(φ₁) φ₂`), `UnitaryOrbitRepresentative`,
  `unitaryOrbitRepresentative_isDiscreteSeries` and Worker 200's orbit and section data.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234. Overlines, hats and calligraphic letters in the quotes below were checked on the
rendered PDF pages 87 and 88.

- Lemma VIII.2.1, printed p. 321 (PDF p. 87): "Pour `f ∈ 𝒞(G)`, `f` appartient à `°𝒞(G)` si et
  seulement si `f^{(P),Ind} = 0` pour tout sous-groupe parabolique semi-standard propre `P` de
  `G`." Its proof begins: "Si `f` vérifie cette dernière condition, on a `ψ_f[𝒪, P] = 0` pour tout
  `(𝒪, P) ∈ Θ` tel que `P ≠ G`, d'après le Lemme VII.1.2. Donc `f = °f`."
- Lemma VIII.2.3, printed p. 322 (PDF p. 88): "Pour `f_1 ∈ °𝒞(G)` et `f_2 ∈ 𝒞(G)`, on a les
  égalités `f_1 ∗ f_2 = f_1 ∗ °f_2`, `f_2 ∗ f_1 = °f_2 ∗ f_1`." Proof: "Il suffit de prouver que si
  `(𝒪, P) ∈ Θ`, `P ≠ G`, et si `ψ ∈ C^∞(𝒪, P)`, on a `f_1 ∗ f_ψ = f_ψ ∗ f_1 = 0`. Soit `g ∈ G`,
  notons `f'_1` la fonction définie par `f'_1(h) = \overline{f_1(gh^{−1})}`. On a l'égalité
  `(f_1 ∗ f_ψ)(g) = (f'_1, f_ψ)_G`. On montre comme en VII.2 (1) que
  `(f'_1, f_ψ)_G = ∫_𝒪 µ(ω)(\hat{f'_1}(ω, P), ψ_ω) dω`. Mais `f'_1 ∈ °𝒞(G)` d'après le
  Lemme VIII.2.1, donc `\hat{f'_1}(ω, P) = 0` pour tout `ω`. On en déduit `f_1 ∗ f_ψ = 0`. Idem
  `f_ψ ∗ f_1 = 0`." (The bar in `f'_1(h)` is complex conjugation.)
- Lemma VII.1.2 (`f̂(ω, P) = f̂^{(P),Ind}(ω)`, printed p. 315) and the definitions of
  `f^{(P),Ind}` and `f̂^{(P),Ind}(ω)` are quoted in `InducedConstantTermFourier.md`; formula (1)
  of the proof of Proposition VII.2.2 (VII.2 (1)) in `InducedOrbitWavePacketPairing.md`.

The abstraction, the hypotheses and the proof route are internal to this project.

## Relation to the source

- `ConstantTermIndVanishes hD hE ht htM f` is the condition `f^{(P),Ind} = 0` for one parabolic
  subgroup `P = M U` (for every `(g₁, g₂) ∈ G × G`). Lemma VIII.2.1 asks it for every proper
  semi-standard `P`; `°𝒞(G)`, `°f`, `κ` and the converse direction of Lemma VIII.2.1 (which uses
  Theorem VII.2.5) are not formalized here.
- `fourierOrbitSection_eq_zero_of_constantTermInd_eq_zero` is the first sentence of the proof of
  Lemma VIII.2.1 for one orbit `𝒪` of `P`: `ψ_f[𝒪, P] = 0`, by Lemma VII.1.2.
- `pairing_inducedOrbitWavePacket_eq_zero_of_constantTermInd_eq_zero` is the vanishing
  `(f, f_ψ)_G = 0` in the proof of Lemma VIII.2.3, for the wave packets of one orbit and one `P`,
  stated as `(f_ψ, f)_G = 0` (the two differ by complex conjugation, `pairing_conj_symm`). The
  wave packet carries a weight `w` on the orbit in place of `µ(ω)` and the measure data of
  `OrbitWavePacket`, as in `InducedOrbitWavePacketPairing`. In the source the function is
  `f'_1(h) = \overline{f_1(g h^{−1})}`, which lies in `°𝒞(G)` when `f_1` does; that translates and
  conjugates of `f` satisfy `ConstantTermIndVanishes`, the convolution identity
  `(f_1 ∗ f_ψ)(g) = (f'_1, f_ψ)_G` and Lemma VIII.2.3 itself are not formalized here.
- The hypotheses `hint`, `hμK`, `hPKiw`, `hMK` (resp. `hMKμ`), `hUK` and the constant-term data
  are those of Lemma VII.1.2 (`InducedConstantTermFourier.md`), required at every representative
  of the orbit; the integrability hypotheses of the wave packet are those of
  `InducedOrbitWavePacketPairing.md`.

## Contents

### Definition

`ConstantTermIndVanishes hD hE ht htM f` (definition; section variables: `G` a topological group
with `MeasurableSpace`, `BorelSpace` and `Nonempty (CompactOpenSubgroup G)`, subgroups `M U`, a
measure `ν` on `U`, `δ : M →* ℝ≥0ˣ`, weights `Ξ σ : G → ℝ`, `ΞM σM : M → ℝ`,
`hD : ConstantTermData ν δ`, `hE : ConstantTermEstimate ν δ Ξ σ ΞM σM`,
`ht : TranslationWeights Ξ σ`, `htM : TranslationWeights ΞM σM`), for `f : Space Ξ σ`: the
proposition `∀ x : G × G, Space.constantTermInd hD hE ht htM f x = 0`.

### Results

- `constantTermInducedFourierTransform_eq_zero` (section `Definition`, the variables of the
  section `Definition` of `InducedConstantTermFourier`: `h`, `hU`, `hδU`, `A`, `μL`, `hwM`, `hA`,
  `hTM`, `hΞM`, `hσM`, `d`, `ν`, `hD`, `hν`, `hE`, `ht`, `htM`): for `f : Space Ξ σ` with
  `h0 : ConstantTermIndVanishes hD hE ht htM f`,
  `constantTermInducedFourierTransform h hU hδU A hwM hA hTM hΞM hσM d hD hν hE ht htM f = 0`.
- `inducedFourierTransform_eq_zero_of_constantTermInd_eq_zero` (section `Main`, the variables of
  the section `Main` of `InducedConstantTermFourier`, listed in `InducedConstantTermFourier.md`):
  with the further hypotheses of Lemma VII.1.2, `[MeasurableInv G]`, `[μ.IsInvInvariant]`,
  `[SigmaFinite μ]`, `hμK : μ K = 1`, `[MeasurableInv M]`, `[μL.IsInvInvariant]`,
  `[SFinite μL]`, `[SFinite ν]`, `hPKiw`, `hMK : μL (M ∩ K) = 1`, `hUK : ν (U ∩ K) = 1`,
  `f : Space Ξ σ` and `hint` (integrability for every `ψ ∈ L(ω, P)`), and
  `h0 : ConstantTermIndVanishes hD hE ht htM f`:
  `inducedFourierTransform h hU hP hm K hK hPK hG hδ A hcof C hC μM hsq hi hw hT hΞ hσ f = 0`.
- `fourierOrbitSection_eq_zero_of_constantTermInd_eq_zero` (section `Orbit`: the variables of
  the section `Orbit` of `InducedFourierCoherence` — `h`, `hU`, `hP`, `hm`, `K`, `hK`, `hPK`,
  `hG`, `hδ`, `ν`, `π`, `hcof`, `C`, `hC`, `μM`, `hsq : ∀ A, …`, a measure `μ` on `G`, `hw`,
  `hT : ∀ A, …`, `hΞ`, `hσ` — and the constant-term data `hδU`, `μL`, `hwM`,
  `hTM : ∀ A : UnitaryOrbitRepresentative ν π, HasTemperedCoefficients ΞM σM A.val.obj.representation`,
  `hΞM`, `hσM`, a measure `νU` on `U` with `hD`, `hνU`, `hE`, `ht`, `htM`): with the further
  hypotheses of Lemma VII.1.2 as above (for `νU`), `f`,
  `hint : ∀ A ψ, Integrable (fun x : G × K => conj (integrand A x.1 ψ x.2) * f x.1) …` for every
  representative `A`, and `h0`:
  `fourierOrbitSection h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ f = 0`.
- `pairing_inducedOrbitWavePacket_eq_zero_of_constantTermInd_eq_zero` (section `Pairing`: the
  variables of the section `Pairing` of `InducedOrbitWavePacketPairing`, listed in its Markdown,
  with `Ξ = xi hP₀K δ₀`): hypotheses `[SigmaFinite μG]`, `[IsFiniteMeasure ρ]`, `hLaurent`, `he`,
  `hwm`, `b` with `hwb`, `hδU`, `hL`, `hMK : IsIwasawaPair (P₀ ∩ M) (K ∩ M)`, `hδ₀`, `hcoeff`,
  a section `q`; the constant-term data `[Nonempty (CompactOpenSubgroup M)]`, `μL` (left and right
  invariant), `ΞM σM`, `hwM`, `hTM : ∀ A, …`, `hΞM`, `hσM`, `νU` (left and right invariant), `hD`,
  `hνU`, `hE` (for `Ξ = xi hP₀K δ₀` and `σ`), `ht`, `htM`; `hμK : μG K = 1`, `[MeasurableInv M]`,
  `[μL.IsInvInvariant]`, `[SFinite μL]`, `[SFinite νU]`, `hPKiw`, `hMKμ : μL (M ∩ K) = 1`,
  `hUK : νU (U ∩ K) = 1`; `f : Space (xi hP₀K δ₀) σ`, `hint : ∀ A ψ, …` (for `μG`) and
  `h0 : ConstantTermIndVanishes hD hE ht htM f`. Conclusion:
  `pairing μG (inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w q) f = 0`.

## Proof

`constantTermInducedFourierTransform_eq_zero`: the induced function
`f̂^{(P),Ind}(ω)` is built (`Induction.smoothFunctionOf`) from
`x ↦ coefficientFourierTransform (Space.constantTermInd … f x)`; by `h0` and linearity of the
Fourier transform each value is `0`, so the function is the zero element.

`inducedFourierTransform_eq_zero_of_constantTermInd_eq_zero`: rewrite with Lemma VII.1.2,
`inducedFourierTransform_eq_constantTermInducedFourierTransform`, and apply the previous lemma
with `hA = hsq.1`.

`fourierOrbitSection_eq_zero_of_constantTermInd_eq_zero`: the value of `ψ_f[𝒪, P]` at a
representative `A` is `inducedFourierTransform … A.val.obj … f` (`fourierOrbitSection_apply`),
which vanishes by the previous lemma for `A.val.obj`, with `hsq A`, `A.val.property.1`
(irreducibility), `hT A`, `hTM A` and `hint A`.

`pairing_inducedOrbitWavePacket_eq_zero_of_constantTermInd_eq_zero`: the Library's
`pairing_inducedOrbitWavePacket_eq_zero` with its hypothesis `ψ_f[𝒪, P] = 0` supplied by the
previous lemma, for `hPK` in the form `factorization_mem_of_subtype hPK` and the square
integrability of the representatives `unitaryOrbitRepresentative_isDiscreteSeries`.

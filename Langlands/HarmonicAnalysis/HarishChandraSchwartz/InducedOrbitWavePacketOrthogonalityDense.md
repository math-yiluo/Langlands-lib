# Wave packets detect `f̂(ω, P)` for a weight positive on a dense set (Waldspurger, proof of Corollary VII.2.3)

Author: Worker 5, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module:
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedOrbitWavePacketOrthogonalityDense`,
namespace `Langlands.HarishChandraSchwartz`. Its only import is the Library module
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedOrbitWavePacketOrthogonality` (Worker
3642). From that module it uses:

- `isOpenPosMeasure_discreteSeriesOrbitMeasure`;
- the pointwise lemmas `unitaryOrbitProductPairing_add_left`, `_smul_left`, `_conj_symm` and
  `re_unitaryOrbitProductPairing_self_nonneg`;
- `integrable_ofReal_mul_unitaryOrbitProductPairing`.

Through its imports it also uses:

- `unitaryOrbitProductPairing`, `unitaryOrbitProductPairing_representative`,
  `continuous_unitaryOrbitProductPairing` and `unitaryOrbitRepresentativeProductForm`;
- `unitaryOrbitWeightedProductPairing`, `pairing_inducedOrbitWavePacket_eq_integral_productPairing`
  and `pairing_inducedOrbitWavePacket_eq_zero`;
- `productInducedSmoothOrbitSections`, `inducedOrbitWavePacket`, `fourierOrbitSection`,
  `discreteSeriesOrbitMeasure` and `unitaryOrbitRepresentativeDiscreteSeriesOrbit`.

`InducedOrbitWavePacketOrthogonality.md` describes all of these.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers are printed
pages; the PDF page is the printed page minus 234.

- V.2, printed p. 292: "Pour `ω ∈ O`, on pose `µ(ω) = j(ω)^{-1} ∏_α γ(M_α|M)^2`, où `α` parcourt
  les racines réduites de `A_M` au signe près."
- Lemma V.2.1, printed p. 292, first item: "La fonction `µ` est une fonction rationnelle
  régulière sur `O`. Pour tout `ω ∈ O`, on a `µ(ω) ⩾ 0`".
- Corollary VII.2.3 and its proof, printed p. 319, quoted in
  `InducedOrbitWavePacketOrthogonality.md`. The proof ends: "Cette égalité valant pour tout
  `ψ'`, elle entraîne `f̂_ψ(ω'', P') = 0` pour tout `ω'' ∈ O'`."
- VII.2, printed p. 319, after Corollary VII.2.3, quoted in the same file: the sum over
  `(O, P) ∈ Θ` of `c(G|M)^{-2} γ(G|M)^{-1} |W^M| |W^G|^{-1} |𝒫(M)|^{-1} ∫_O µ(ω)
  (ψ'[O, P]_ω, ψ[O, P]_ω) dω`. The source says: "Cela définit un produit hermitien défini
  positif".

## Provenance

The statements are those of `InducedOrbitWavePacketOrthogonality` with one hypothesis changed.
That module takes `hupos : ∀ ω, 0 < u ω`. This one takes:

- `hu0 : ∀ ω, 0 ≤ u ω`;
- `hud : Dense {ω | 0 < u ω}`.

The change is internal derived content, not a statement of the paper. Its reason is the weight
that the source actually uses. In the source, the weight of the product of VII.2 and of formula
(1) of the proof of Proposition VII.2.2 is the Plancherel density `µ`. Lemma V.2.1 gives only
`µ ≥ 0` on `O`. Since `µ(ω) = j(ω)^{-1} ∏_α γ(M_α|M)^2`, `µ` vanishes at a unitary `ω` where `j`
has a pole. So the strict positivity `0 < u` everywhere is not available for `u = µ`.

What the source's argument needs is definiteness: `∫_O µ(ω) (r_ω, r_ω) dω = 0` only for `r = 0`.
The proof here shows that `u ≥ 0` together with density of `{u > 0}` suffices. The integral
vanishes, so the continuous integrand vanishes everywhere. Then `(r_ω, r_ω)` vanishes on the dense
set `{u > 0}`, hence everywhere by continuity.

The everywhere-positive case is the special case `{u > 0} = O`: `dense_pos_of_forall_pos` turns
`hupos` into `hud`, and `hupos` gives `hu0`.

## Setting

The section variables of section `Orthogonality` and of its subsection `Corollary` are those of
`InducedOrbitWavePacketOrthogonality`, listed in the "Scope and hypotheses" section of its
Markdown file:

- the group `G` and its instances;
- `P`, `M`, `U`, `h`, `hU`, `hP`, `K`, `hK`, `hPK`, `hG`, `hδ`;
- `ν`, `π`, `hν`, `hr`, `J`, `e`, `P₀`, `δ₀`, `δ₀M`;
- the compactness instances of `K` and `K ∩ M`, and `hcof`;
- `C`, `hC`, `μ`, `hsq`, and the two finiteness instances;
- a measure `ρ` on `unitaryUnramifiedCharacters ν`;
- a real weight `u : O → ℝ` on the orbit `O = discreteSeriesOrbit C hC μ ν (discreteSeriesClass C
  hC μ π hsq)`;
- in `Corollary`: `hP₀K`, `μG`, `σ`, `hwt`, `hT`, `hΞ`, `hσ`.

The `omit … in` and `include hwt in` declarations are copied from that module.

Each result below also takes:

- `[IsFiniteMeasure ρ]` and `[ρ.IsOpenPosMeasure]`;
- `he : Continuous e` and `hu : Continuous u`;
- `hu0 : ∀ ω, 0 ≤ u ω` and `hud : Dense {ω | 0 < u ω}`;
- a real `b` and `hub : ∀ ω, u ω ≤ b`.

The two theorems of `Corollary` also take the remaining hypotheses of their Library counterparts:
`[SFinite μG]`, `hLaurent`, `hδU`, `hL`, `hMK`, `hδ₀`, `hcoeff`, `f`, `hsm` (and `h0` for the
first).

## Results

Write `(q_ω, r_ω)` for `unitaryOrbitProductPairing … q r ω`, the product of V.2 on the fibre at
`ω`. The weighted orbit product is
`⟪q, r⟫_u = unitaryOrbitWeightedProductPairing … ρ (fun ω => (u ω : ℂ)) q r = ∫_O u(ω) (q_ω, r_ω)
dω`, for the measure `discreteSeriesOrbitMeasure` of `ρ`.

- **`dense_pos_of_forall_pos`** (outside the section): for any topological space `X` and
  `u : X → ℝ`, if `0 < u x` for every `x` then `{x | 0 < u x}` is dense.
- **`unitaryOrbitWeightedProductPairing_self_eq_zero_iff_of_dense`**: `⟪r, r⟫_u = 0 ↔ r = 0` for
  `r ∈ C^∞(O, P)` (`productInducedSmoothOrbitSections`).
- **`unitaryOrbitWeightedProductCore_of_dense`** (definition, `@[instance_reducible]`): an
  `InnerProductSpace.Core ℂ (productInducedSmoothOrbitSections …)` whose inner product is
  `⟪q, r⟫_u`. As for every `InnerProductSpace.Core`, it is conjugate-linear in the first
  argument, additive, hermitian, with nonnegative real part on the diagonal, and definite.
- **`unitaryOrbitWeightedProductCore_of_dense_inner`**: its inner product is `⟪q, r⟫_u`, by `rfl`.
- **`fourierOrbitSection_eq_zero_of_forall_pairing_inducedOrbitWavePacket_eq_zero_of_dense`**: if
  `hsm : ψ_f[O, P] ∈ C^∞(O, P)` and `h0 : ∀ q, pairing μG (inducedOrbitWavePacket … ρ (fun ω =>
  (u ω : ℂ)) q) f = 0`, then `fourierOrbitSection … f = 0`, that is, `f̂(ω, P) = 0` at every
  representative of every class of the orbit.
- **`fourierOrbitSection_eq_zero_iff_forall_pairing_inducedOrbitWavePacket_eq_zero_of_dense`**:
  under `hsm`, `fourierOrbitSection … f = 0` if and only if `(f_ψ, f)_G = 0` for the wave packet
  `f_ψ` of weight `u` of every `q ∈ C^∞(O, P)`.

## Proof notes

1. Definiteness. The proof follows the Library's
   `unitaryOrbitWeightedProductPairing_self_eq_zero_iff` up to one step:
   - The integrand `u Re (r_ω, r_ω)` is continuous and nonnegative (`hu0` and
     `re_unitaryOrbitProductPairing_self_nonneg`).
   - Its integral is the real part of `⟪r, r⟫_u = 0` (`integral_re`).
   - So it vanishes almost everywhere (`integral_eq_zero_iff_of_nonneg`), and everywhere
     (`Continuous.ae_eq_iff_eq`, the orbit measure being positive on open sets by
     `isOpenPosMeasure_discreteSeriesOrbitMeasure`).

   The new step: on `{u > 0}`, `Re (r_ω, r_ω) = 0` (`mul_eq_zero`). `ω ↦ Re (r_ω, r_ω)` is
   continuous (`continuous_unitaryOrbitProductPairing`), and so `Continuous.ext_on` with `hud`
   gives `Re (r_ω, r_ω) = 0` for every `ω`.

   The rest is as in the Library. At a representative `A`, `unitaryOrbitProductPairing_representative`
   turns this into `Re ⟪r_A, r_A⟫_A = 0`. The imaginary part vanishes by hermitian symmetry, and
   `definite` of `unitaryOrbitRepresentativeProductForm` gives `r.val A = 0`. The converse
   direction uses `unitaryOrbitProductPairing_smul_left` with `c = 0`.
2. Integrability: `integrable_ofReal_mul_unitaryOrbitProductPairing` needs `|u| ≤ b`, which is
   `hub` rewritten with `abs_of_nonneg (hu0 ω)`.
3. The core: the fields are proved as in the Library's `unitaryOrbitWeightedProductCore`, with
   `hu0` in place of `(hupos ω).le` in `re_inner_nonneg`. `definite` is step 1.
4. The two theorems of `Corollary` follow the Library proofs. The bound `‖u ω‖ ≤ b` uses
   `Real.norm_of_nonneg (hu0 ω)`, and definiteness is step 1.

## Relation to the Library

- `InducedOrbitWavePacketOrthogonality` has the same results under `hupos : ∀ ω, 0 < u ω`
  (`unitaryOrbitWeightedProductPairing_self_eq_zero_iff`, `unitaryOrbitWeightedProductCore`,
  `fourierOrbitSection_eq_zero_of_forall_pairing_inducedOrbitWavePacket_eq_zero`,
  `fourierOrbitSection_eq_zero_iff_forall_pairing_inducedOrbitWavePacket_eq_zero`). With
  `dense_pos_of_forall_pos`, those are special cases of the results here. The Library module is
  not modified.
- `RationalInducedOrbitWavePacketOrthogonalityDense` (same candidate) applies these results to
  actual standard parabolics.

## Open obligations

- Corollary VII.2.3 itself is not proved: as in the Library module, the hypothesis `h0` is
  Proposition VII.2.2 (i), which is not in the Library.
- This module does not show that the Plancherel weight meets `hu0`, `hud`, `hu` and `hub`; it
  takes any weight `u`.
- The hermitian product on `C^∞(Θ)^inv` (the sum over `Θ` with its constants) and its `G × G`
  invariance are not formalized.
- `hcoeff`, `hL`, `hP₀K`, `hMK`, `hδ₀`, `hT` and `hsm` are hypotheses, as in the Library module.

## Axioms

The results use only `propext`, `Classical.choice` and `Quot.sound`.

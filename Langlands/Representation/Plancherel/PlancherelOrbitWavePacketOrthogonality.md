# The Plancherel product on `C^∞(O, P)` and detection by Plancherel wave packets (Waldspurger VII.2, proof of Corollary VII.2.3, with the weight `µ`)

Author: Worker 5, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.Representation.Plancherel.PlancherelOrbitWavePacketOrthogonality`,
namespace `Langlands.Plancherel`. It imports:

- `Langlands.Representation.Plancherel.PlancherelWeightPositivity` (candidate
  `4a929a37-8a95-4d82-bca2-b20030228811`, review accepted, not yet in the Library). It provides
  the real Plancherel weight `standardLeviPlancherelWeightReal` on the orbit `O` with
  `continuous_`, `_nonneg`, `exists_…_le`, `dense_…_pos` and
  `ofReal_standardLeviPlancherelWeightReal`. Through it come the complex Plancherel weight
  `standardLeviPlancherelWeight` (candidate `f1478940-20ed-4d17-96de-4906bd124712`, review
  accepted) and the canonical scalar `conditionalCanonicalRationalScalar` (Library).
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitWavePacketOrthogonalityDense`
  (candidate `5ab951a5-2fa0-426e-bbb9-e1645c17a6ab`, review accepted, not yet in the Library). It
  provides `rationalUnitaryOrbitWeightedProductCore_of_dense` and the two detection theorems
  `…_of_dense` for a bounded continuous weight `u ≥ 0` with `{u > 0}` dense.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers are printed
pages.

- V.2 and Lemma V.2.1, first item, printed p. 292: `µ(ω) = j(ω)^{-1} ∏_α γ(M_α|M)^2`, and
  "Pour tout `ω ∈ O`, on a `µ(ω) ⩾ 0`".
- VII.2, printed p. 319: for `ψ, ψ' ∈ C^∞(Θ)_inv`,
  `(ψ', ψ) = ∑_{(O, P = MU) ∈ Θ} c(G|M)^{-2} γ(G|M)^{-1} |W_M| |W_G|^{-1} |P(M)|^{-1}
  ∫_O µ(ω) (ψ'[O,P]_ω, ψ[O,P]_ω) dω`, and "Cela définit un produit hermitien défini positif
  invariant par `G × G` sur `C^∞(Θ)_inv`".
- Corollary VII.2.3 and its proof, printed p. 319: from formula (1) of the proof of
  Proposition VII.2.2, `∫_{O'} µ(ω'') (ψ'_{ω''}, f̂_ψ(ω'', P')) dω'' = 0` for every `ψ'`, and
  "Cette égalité valant pour tout `ψ'`, elle entraîne `f̂_ψ(ω'', P') = 0` pour tout
  `ω'' ∈ O'`".

## Provenance

The module instantiates the weight `u` of `RationalInducedOrbitWavePacketOrthogonalityDense` with
Waldspurger's Plancherel weight, in its real form `standardLeviPlancherelWeightReal`. The
statements are then rewritten with the complex weight `µ = standardLeviPlancherelWeight` itself,
using `ofReal_standardLeviPlancherelWeightReal`.

Correspondence with the source, for one pair `(O, P)`:

- `P = P_I(F) = M_I(F) ⋉ U_I(F)` is an actual standard parabolic, `M = M_I`, and `O` is the
  orbit under `Im X(M_I)` of the class of a square-integrable representation `π` of `M_I(F)`
  modulo `C` (`discreteSeriesOrbit`).
- `µ(ω)` is `standardLeviPlancherelWeight … hreg ω` (candidate `f1478940`). There,
  `µ = j_P^{-1} ∏_α γ(M_α|M)^2`, transported from `Im X(Z_G(ζ ∘ i))` to `O` along
  `e : Z_G(ζ ∘ i)(F) ≃ M_I(F)`. Here `j_P = conditionalCanonicalRationalScalar … (π ∘ e) …` is
  the canonical scalar of the inducing representation `π ∘ e`.
- `C^∞(O, P)` is `rationalInducedSmoothOrbitSections`, and `∫_O µ(ω) (s_ω, t_ω) dω` is the
  summand of the product of VII.2 for `(O, P)`, without its constant.
- The wave packet of `ψ ∈ C^∞(O, P)` for the weight `µ` is
  `rationalInducedOrbitWavePacket … ρX (standardLeviPlancherelWeight … hreg) ψ`, that is
  `f_ψ(g) = ∫_O µ(ω) (E_P^G ψ_ω)(g) dω`. The same object appears in the decay bound
  `exists_norm_standardLeviPlancherelWavePacket_le_rationalXi_rpow` (candidate `f1478940`).
- `ψ_f[O, P]` is `rationalFourierOrbitSection … f`, and `f̂(A, P)` is
  `rationalInducedFourierTransform … A.val.obj … f`.

Three hypotheses on `j_P` are taken, not proved (see "Scope and hypotheses").
`standardLeviPlancherelWeightRealBound` is internal: it is a chosen upper bound of the weight on
the compact orbit, needed only as an argument of the dense product.

## Setting

Section variables:

- the field `F`, `G` connected reductive (`hG`), a maximal split torus `i` (`hi`), a generic
  cocharacter `ν` (`hν`), a set `I` of simple roots with root set `𝐉`, and a standard cocharacter
  `ζ` for `𝐉` (`hζ`). Write `𝐌` for `M_I(F)` as a subtype of `G(F)`;
- `π : IrreducibleAdmissibleRep 𝐌`, a central subgroup `C` (`hC`), a Haar measure `mu` on
  `𝐌 ⧸ C`, and `hsq` (square integrability of `π` modulo `C`);
- the data of `j_P` copied from `PlancherelWeightPositivity`: `hRefl`, `hCST`, a compact open
  subgroup `K` of `G(F)` with `hK`, `hPK`, `hOppK`, the continuations `p` and `q`, the regions
  `DForward`, `DReverse`, `D` with their hypotheses, and `hirr`;
- from `standardLeviPlancherelOrbitProductCore` on: `[BorelSpace (𝐌 ⧸ C)]`,
  `[mu.IsInvInvariant]`, a second compact open subgroup `Kw` with `hKw` and the Iwasawa pair
  `hPKw`, the two finiteness instances of the dense module, and a measure `ρX` on `Im X(M_I)`;
- for the two detection theorems: the hypotheses of `rationalFourierOrbitSmoothSectionLinear`
  (`ρ`, `hρ`, `hKρ`, `hM`, `hTA`, `μG`, `hsw`, `hμK`, `μL`, `hswM`, `hTπ`, `νU`, `hE`, `hPKiw`,
  `hMK`, `hUK`, `Cn`, `hnσ`, `hint`), with `Kw` in place of the dense module's `K`. They are
  included as in that module.

`K` enters only through `j_P`, and `Kw` through `C^∞(O, P)`, the wave packets and `C(G)`. They
are independent variables, as in `exists_norm_standardLeviPlancherelWavePacket_le_rationalXi_rpow`.

The hypotheses on `j_P`, written `jP`, are:

- `hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹` (regularity of `j_P⁻¹` at every unitary
  character);
- `hj : jP ≠ 0`;
- `hnn`: at every unitary character `z`, `RationalFunctionNonnegAt … (jP)⁻¹ (unitaryToUnramified
  MS z)` (the value of `j_P⁻¹` is a nonnegative real).

The product and the theorems also take `[IsFiniteMeasure ρX]` and `[ρX.IsOpenPosMeasure]`. The
detection theorems take `hcoeff` (bounds of the coefficients of `π` by `Ξ^{M}`) and
`f : RationalSchwartzSpace hKw hPKw ρ`.

## Contents

- **`ofReal_comp_standardLeviPlancherelWeightReal … hreg hnn`**:
  `(fun x => (standardLeviPlancherelWeightReal … hreg x : ℂ)) = standardLeviPlancherelWeight …
  hreg`.
- **`standardLeviPlancherelWeightRealBound … hreg`** (definition): a real number, chosen with
  `Classical.choose` from `exists_standardLeviPlancherelWeightReal_le`;
  **`standardLeviPlancherelWeightReal_le_bound`**: the real weight is at most this number at
  every point of `O`.
- **`standardLeviPlancherelOrbitProductCore … ρX hreg hj hnn`** (definition, the recorded
  declaration, `@[instance_reducible]`):
  `InnerProductSpace.Core ℂ (rationalInducedSmoothOrbitSections hG hi hν I hKw hPKw π)`. As for
  every `InnerProductSpace.Core`, it is conjugate-linear in the first argument, additive,
  hermitian, with nonnegative real part on the diagonal, and definite: `⟪s, s⟫ = 0` only for
  `s = 0`.
- **`standardLeviPlancherelOrbitProductCore_inner … hreg hj hnn s t`**: its inner product is
  `⟪s, t⟫ = ∫_O µ(ω) (s_ω, t_ω) dω`, with `µ = standardLeviPlancherelWeight … hreg`, the pairing
  `unitaryOrbitProductPairing` and the measure `discreteSeriesOrbitMeasure` for `ρX`.
- **`rationalFourierOrbitSection_eq_zero_iff_forall_pairing_standardLeviPlancherelWavePacket_eq_zero
  … hreg hj hnn hcoeff f`**: `rationalFourierOrbitSection … f = 0` (that is, `ψ_f[O, P] = 0`)
  if and only if, for every `s ∈ C^∞(O, P)`,
  `pairing μG (rationalInducedOrbitWavePacket … ρX (standardLeviPlancherelWeight … hreg) s) f = 0`.
- **`rationalInducedFourierTransform_eq_zero_of_forall_pairing_standardLeviPlancherelWavePacket_eq_zero
  … hreg hj hnn hcoeff f h0 A`**: if `h0` states the vanishing of all these pairings, then
  `rationalInducedFourierTransform … A.val.obj … f = 0` (that is, `f̂(A, P) = 0`) for every
  representative `A` of the orbit.

## Proofs

- `ofReal_comp_…` is `funext` of `ofReal_standardLeviPlancherelWeightReal`.
- `…_le_bound` is `Classical.choose_spec` of `exists_standardLeviPlancherelWeightReal_le`.
- The product is `rationalUnitaryOrbitWeightedProductCore_of_dense` with `u` the real Plancherel
  weight. Its four hypotheses on `u` come from candidate `4a929a37`:
  `continuous_standardLeviPlancherelWeightReal`, `standardLeviPlancherelWeightReal_nonneg` (from
  `hnn`), `dense_standardLeviPlancherelWeightReal_pos` (from `hj` and `hnn`) and
  `standardLeviPlancherelWeightReal_le_bound`.
- `_inner` rewrites `µ` backwards with `ofReal_comp_…` and closes by `rfl`, since
  `rationalUnitaryOrbitWeightedProductCore_of_dense_inner` holds by `rfl`.
- The equivalence rewrites `µ` backwards with `ofReal_comp_…`. It is then
  `rationalFourierOrbitSection_eq_zero_iff_forall_pairing_rationalInducedOrbitWavePacket_eq_zero_of_dense`
  with the same four facts.
- The corollary is
  `rationalInducedFourierTransform_eq_zero_of_forall_pairing_rationalInducedOrbitWavePacket_eq_zero_of_dense`
  with the same four facts. Its hypothesis is `h0` rewritten with `ofReal_comp_…`.

## Scope and hypotheses

- `j_P ≠ 0`, the regularity of `j_P⁻¹` at the unitary characters and the nonnegativity of its
  unitary values are hypotheses. The last is the content of Lemma V.2.1 (first item), which is
  not proved here.
- Only one pair `(O, P)` with `P = P_I ⊇ P₀` standard is treated. The sum over `Θ`, its constants
  `c(G|M)^{-2} γ(G|M)^{-1} |W_M| |W_G|^{-1} |P(M)|^{-1}`, the restriction to `C^∞(Θ)_inv` and the
  `G × G` invariance are not formalized.
- The measure `ρX` on `Im X(M_I)` is any finite measure charging every nonempty open set.
  Waldspurger's normalization of the measure on `O` is not fixed.
- Corollary VII.2.3 itself is not proved: as in the Library module
  `RationalInducedOrbitWavePacketOrthogonality`, the vanishing hypothesis `h0` is
  Proposition VII.2.2 (i), which is not proved on actual points.
- The hypotheses inherited from `rationalFourierOrbitSmoothSectionLinear`, `hcoeff` and the
  finiteness instances remain hypotheses, as listed in
  `RationalInducedOrbitWavePacketOrthogonality.md` ("Scope and hypotheses").

## Axioms

The results use only `propext`, `Classical.choice` and `Quot.sound`.

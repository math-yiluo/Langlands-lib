# Proposition VII.1.3 on actual points: continuity of `f ↦ ψ_f[O, P]`

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalFourierOrbitContinuity`,
namespace `Langlands.HarishChandraSchwartz`. It imports two published modules:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalFourierOrbitSmoothness` (this
  author's Unit 24). It provides:
  - `rationalFourierOrbitSmoothSectionLinear`, the linear map `f ↦ ψ_f[O, P]` from `C(G)` into
    `C^∞(O, P)` on actual points, with `rationalFourierOrbitSmoothSectionLinear_val`;
  - `rationalLeviXi_inv`, `rationalLeviTranslationWeights` and
    `laurentExponent_leviRationalUnitaryCoordinates`.
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.FourierOrbitContinuity` (Worker 249). It
  provides:
  - `fourierOrbitLaurentSectionCLM`, the abstract continuous linear map `f ↦ ψ_f[O, P]`, with
    `toSections_fourierOrbitLaurentSectionCLM`;
  - `productInducedOrbitRepresentation_fourierOrbitSection` (Lemma VII.1.1 (i) for `ψ_f[O, P]`).

Through these imports the module also uses:

- the topology of `C^∞(O, P)` (`OrbitSectionTopology`: `OrbitSectionSpace`,
  `orbitSectionLevelSubmodule`, `OrbitSectionSpace.toSections`) and
  `productInducedOrbitRepresentation`;
- `rationalFourierOrbitSection` (`ψ_f[O, P]`, Unit 23) and `rationalInducedSmoothOrbitSections`
  (Unit 20);
- the actual data of `P_I(F)`: `isSemidirectDecomposition_standard`,
  `isClosed_standardUnipotentPoints`, `isClosed_standardParabolicPoints_rootSet`,
  `continuous_projection_standard`, `exists_standardParabolicPoints_rootSet_mul`,
  `factorization_subtype`, `locallyCompactSpace_standardParabolicPoints_rootSet`,
  `modularCharacter_standardParabolicPoints`, `leviRationalUnitaryCoordinates` with
  `_hasLaurent`, `compactOpenCofinal_standardLevi`, `compactSpace_subgroupOf_standardLevi`;
- the analytic data: `rationalL2Weights`, `rationalXi_inv`, `rationalHeight_inv`,
  `rationalTranslationWeights`, `rationalHasTemperedCoefficients_normalizedInduction`,
  `rationalLeviXi_pos`, `rationalConstantTermData`, `rationalIsConjModulus`,
  `isUnimodularModulus_standardUnipotentPoints`, `unitaryOrbitRepresentative_isDiscreteSeries`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers are printed
pages; the PDF page is the printed page minus 234. The author checked the quotations below on the
rendered PDF pages 67, 80 and 82.

- Proposition VII.1.3, printed p. 316: "Pour tout `f ∈ C(G)`, la fonction `ψ_f[O, P]` appartient
  à `C^∞(O, P)`. L'application `C(G) → C^∞(O, P)`, `f ↦ ψ_f[O, P]` est continue."
- Topology of `C^∞(O, P)`, VI.3, printed p. 301: "Pour tout sous-groupe ouvert compact `H` de `K`,
  l'espace des invariants `L_K(ω, P)^{H×H}` est de dimension finie, donc muni d'une topologie
  canonique. L'espace `C^∞(Im X(M)) ⊗_ℂ L_K(ω, P)^{H×H}` est muni de la topologie produit. Grâce
  à la description donnée en VI.1, son sous-espace `C^∞(O, P)^{H×H}` se retrouve muni d'une
  topologie. On munit `C^∞(O, P)` de la toplogie limite inductive des topologies de ces
  sous-espaces quand `H` décrit l'ensemble des sous-groupes ouverts compacts de `K`." (The
  misspelling "toplogie" is in the source.)
- Lemma VII.1.1 (i), printed p. 314: "Soient `f ∈ C(G)`, `g, h ∈ G` et `ψ ∈ L(ω, P)`. On a les
  égalités (i) `(ρ(g)λ(h)f)^(ω, P) = (π(g) ⊗ π̌(h))(f̂(ω, P))`".

`FourierOrbitContinuity.md` explains how the Library's abstract `fourierOrbitLaurentSectionCLM`
models the second assertion of Proposition VII.1.3. `OrbitSectionTopology` models the VI.3
topology: the levels are the sections fixed by `H × H` for open subgroups `H ⊆ K`, each with the
topology given by the seminorms of all derivatives of all linear forms of the values.

What this module adds:

- `rationalFourierOrbitSectionCLM` is the second assertion of Proposition VII.1.3 (source
  content) for a standard parabolic `P = P_I(F) ⊇ P₀(F)` of `G(F)`. The domain is `C(G)` with
  the topology of III.6 (`RationalSchwartzSpace`). The target is `C^∞(O, P)` with the topology
  of VI.3 (`rationalInducedOrbitSectionSpace`).
- `productInducedOrbitRepresentation_rationalFourierOrbitSection` is the consequence of
  Lemma VII.1.1 (i) that `ψ_f[O, P]` is fixed by `H × H` when `f` is bi-invariant under `H`.
  The source uses it in the proof of Proposition VII.1.3 to work level by level.
- `rationalInducedOrbitSectionSpace` is the space `C^∞(O, P)` with the topology of VI.3, on the
  actual data.
- The level membership and the two `toSections` lemmas are internal glue.

## Setting

As in Unit 24 (`RationalFourierOrbitSmoothness.md`):

- `G` connected reductive over a nonarchimedean local field `F`, with `hG`, a maximal split torus
  `i` (`hi`), a generic cocharacter `ν` (`hν`), and a finite set `I` of simple roots;
  `P = P_I(F)`, `M = M_I(F)` (local notation `𝐌`), `𝐉 = rootSet i ν I`;
- a compact open subgroup `K` (`hKc`) with the Iwasawa decomposition `hPK` for `P₀(F)`, and `hM`
  for `M_I(F)`;
- `ρ` with `hρ` and `hKρ`, which define the height `σ`;
- `π` an irreducible admissible representation of `M_I(F)`; its orbit `O` under the unitary
  unramified characters `Im X(M_I)` (the norm characters `leviRationalNormCharacters`);
- `C`, `hC`, `μM`, `hsq` (square integrability modulo the central subgroup `C`);
- `hTA`: every representative of the orbit is tempered;
- `μG` with `hsw` (Lemma II.1.5 for `G`).

The continuous linear map and the level membership also take, as in Unit 24:

- `μG` inverse-invariant and σ-finite with `hμK : μG(K) = 1`;
- `μL` on `M_I(F)` with `hswM` (Lemma II.1.5 for `M_I`) and `hMK : μL(K ∩ M_I(F)) = 1`;
- `hTπ` (`π` tempered);
- `νU` on `U_I(F)` with `hUK : νU(K ∩ U_I(F)) = 1`, and
  `hE : ConstantTermEstimate νU δ_{U_I} Ξ σ Ξ^{M_I} σ|_{M_I}` (Proposition II.4.5);
- `hPKiw : m u ∈ K ↔ m ∈ K ∧ u ∈ K` for `m ∈ M_I(F)`, `u ∈ U_I(F)`;
- `hnσ : ‖n_{M_I}(m)‖ ≤ Cn (1 + σ(m))` for the lattice coordinates `n_{M_I}` of `H_{M_I}`;
- `hint`: the integrability of `(g, k) ↦ conj(⟨ψ(k g, k)⟩) f(g)` on `G(F) × K`.

## Contents

- **`rationalInducedOrbitSectionSpace hG hi hν I hKc hPK π`** (abbreviation): the Library's
  `OrbitSectionSpace` on the actual data of `P_I(F)`. This is `C^∞(O, P)` with the inductive
  limit topology of VI.3, whose elements are those of `rationalInducedSmoothOrbitSections`.
- **`productInducedOrbitRepresentation_rationalFourierOrbitSection hf x hx₁ hx₂`**: let
  `f ∈ C(G)` be bi-invariant under a subgroup `H`, and let `x = (x₁, x₂)` with `x₁, x₂ ∈ H`.
  Then `x` fixes `ψ_f[O, P] = rationalFourierOrbitSection f`. Here `x` acts at each
  representative `ω` by `(I_P^G ω)(x₁) ⊗ (I_P^G ω)ˇ(x₂)` (`productInducedOrbitRepresentation`).
- **`rationalFourierOrbitSmoothSectionLinear_mem_orbitSectionLevelSubmodule H hf`**: for an open
  subgroup `H` and `f` bi-invariant under `H`, `ψ_f[O, P]` lies in the level
  `C^∞(O, P)^{H × H}` (`orbitSectionLevelSubmodule … H`).
- **`rationalFourierOrbitSectionCLM …`** (definition, the recorded declaration): the continuous
  ℂ-linear map `C(G) → C^∞(O, P)`, `f ↦ ψ_f[O, P]`. It is the Library's
  `fourierOrbitLaurentSectionCLM` with the inputs of Unit 24.
- **`toSections_rationalFourierOrbitSectionCLM f`**: the image of `f` in
  `rationalInducedSmoothOrbitSections` is `rationalFourierOrbitSmoothSectionLinear … f` (Unit 24).
- **`rationalFourierOrbitSectionCLM_apply_val f`**: the underlying section is
  `rationalFourierOrbitSection f`.

## Proofs

- `productInducedOrbitRepresentation_rationalFourierOrbitSection` applies the Library's
  `productInducedOrbitRepresentation_fourierOrbitSection` with `(G := rationalPoints G)`,
  `(M := standardLeviPoints …)` and the actual data of Units 19–23. It then unfolds
  `rationalFourierOrbitSection` and closes with `with_reducible_and_instances exact`.
- The level membership pairs the smoothness of the section (the property of
  `rationalFourierOrbitSmoothSectionLinear … f`) with the fixedness above, after rewriting with
  `rationalFourierOrbitSmoothSectionLinear_val`.
- `rationalFourierOrbitSectionCLM` passes to `fourierOrbitLaurentSectionCLM` the same inputs as
  Unit 24's definition passes to `fourierOrbitLaurentSmoothSectionLinear`:
  - `Nonempty (CompactOpenSubgroup M_I(F))` from `K ∩ M_I(F)`;
  - `L2Weights` on `M_I` from `rationalLeviXi_pos` and `hswM`;
  - the inverse invariance of `Ξ^{M_I}` and `σ`, the constant-term data with `hE`, and the
    translation weights of `G` and `M_I`;
  - the Laurent property of the coordinates, and the bound of the Laurent exponent obtained
    from `hnσ` with `laurentExponent_leviRationalUnitaryCoordinates`.
- `toSections_rationalFourierOrbitSectionCLM` unfolds both definitions and closes by `rfl`.
  `rationalFourierOrbitSectionCLM_apply_val` rewrites with it and applies
  `rationalFourierOrbitSmoothSectionLinear_val`.

## Scope and hypotheses

- Only standard parabolics `P_I ⊇ P₀` are covered, not all semi-standard ones.
- The hypotheses are those of Unit 24's `rationalFourierOrbitSmoothSectionLinear`:
  - analytic inputs whose actual statements are published but unproved: `hsw` and `hswM`
    (Lemma II.1.5 for `G` and `M_I`), `hE` (Proposition II.4.5), and `hTA` and `hTπ`
    (Corollary III.1.2);
  - the structural fact `hPKiw`;
  - the measure normalizations `hμK`, `hMK` and `hUK`;
  - the height bound `hnσ` and the integrability `hint`.
- The fixedness result `productInducedOrbitRepresentation_rationalFourierOrbitSection` needs only
  the setting variables up to `hsw`.

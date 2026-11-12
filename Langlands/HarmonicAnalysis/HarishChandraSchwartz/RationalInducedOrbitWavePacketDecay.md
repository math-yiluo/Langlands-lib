# The first bound of Proposition VI.3.1 for actual standard parabolic subgroups

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitWavePacketDecay`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitWavePacket` (this
  author's Unit 20, candidate `32489085-08ba-4b12-be15-d1eee77e42b3`). It provides:
  - the wave packet `rationalInducedOrbitWavePacket` (`f_ψ`) and the space
    `rationalInducedSmoothOrbitSections` (`C^∞(O, P)`);
  - the circle coordinates `leviRationalUnitaryCoordinates` on `Im X(M_I)`, with
    `leviRationalUnitaryCoordinates_hasLaurent`;
  - `isConnectedReductive_leviScheme_rootSet`.

  Through its imports (Unit 19, candidate `181a067e`, and the published Units 11–14) come the
  actual data of `P_I(F)`:
  - `isSemidirectDecomposition_standard`, `isClosed_standardUnipotentPoints`,
    `isClosed_standardParabolicPoints_rootSet`, `exists_standardParabolicPoints_rootSet_mul`,
    `continuous_projection_standard`;
  - `modularCharacter_standardParabolicPoints`, `isUnimodularModulus_standardUnipotentPoints`;
  - `rationalLeviData`, `rationalLeviXi`, `compactSpace_subgroupOf_standardLevi`;
  - `rationalXi`, `rationalMinimalModulus_eq_one`.
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitWavePacketDecay` (Worker 249): the
  abstract bound `exists_norm_inducedOrbitWavePacket_le_xi_rpow`. Through its imports come
  `torusCharacter`, `finiteTorusMonomial` and `IsSmoothFiniteTorusFunction`.
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalValuationCoordinates` (Worker 249).
  It provides:
  - the lattice coordinates `rationalValuationCoordinates G hG` (`n_G(g) ∈ ℤ^r`), with
    `rationalValuationCoordinates_mul`, `rationalValuationCoordinates_one`,
    `rationalValuationLatticeEquiv`;
  - the character formula `rationalUnitaryUnramifiedCharacter_apply`.

  Through its imports come:
  - `rationalValuationImageProjection` with `rationalValuationImageProjection_surjective` and
    `rationalValuationImageProjection_ker`;
  - `rationalCanonicalUnitaryUnramifiedCharacterCoordinates`, `rationalImageRank`;
  - `rationalCommonNormKernel`, with `rationalCommonNormKernel_le_comap` and
    `compactSubgroup_le_rationalCommonNormKernel`.
- `Langlands.Representation.CuspidalSupport.RationalCuspidalBlockVisibility`:
  `CuspidalSupport.standardUnipotent_le_rationalCommonNormKernel` (`U_I(F) ⊆ G(F)¹`). Its
  hypothesis `StandardCocharacterStatement` is the Library's proved `standardCocharacter`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers are printed
pages; the PDF page is the printed page minus 234. The author checked the quotations below on the
text of PDF pages 5, 6 and 69.

- I.1, printed pp. 239–240: "On pose `Im X(G) = {χ ∈ X(G); Re(χ) = 0}`. C'est le sous-ensemble
  des éléments unitaires de `X(G)`." and "On définit un homomorphisme `H_G : G → 𝔞_G` par la
  relation `q^{−⟨χ, H_G(g)⟩} = |χ|_F(g)` pour tout `χ ∈ Rat(G)`. [...] Les définitions
  ci-dessus s'appliquent à tout sous-groupe de Lévi `M`, en remplaçant `G` par `M`."
- Proof of Proposition VI.3.1, printed p. 303: "Pour `χ ∈ Im X(M)`, `λ ∈ Im X(G)` et `g ∈ G`,
  on a `(E_P^G sp_{λχ} ψ)(g) = λ(g)(E_P^G sp_χ ψ)(g)`. [...] La théorie usuelle de la
  transformation de Fourier sur le groupe abélien compact `Im X(G)` nous dit qu'il existe
  `D ∈ D_G` tel que pour tout `ϕ' ∈ C^∞(Im X(G))` et tout `g ∈ G`, on ait
  `|∫_{Im X(G)} ϕ'(λ)λ(g) dλ| ⩽ (1 + (H_G(g)))^{−r} ν_G(D, ϕ')`. (4) En utilisant le Lemme
  VI.2.2, on en déduit qu'il existe `D ∈ D_M` tel que pour tout `ϕ ∈ C^∞(Im X(M))` et tout
  `g ∈ G`, on ait l'inégalité `|f_{ϕ,ψ}(g)| ⩽ (1 + |H_G(g)|)^{−r} Ξ(g) ν_M(D, ϕ)`."

`OrbitWavePacketDecay.md` records how the Library's abstract bound relates to this inequality:
- the weight `w` stands for `µ ϕ`;
- one constant `c` is given for a fixed `w`, instead of the seminorm `ν_M(D, ϕ)`;
- a lattice homomorphism `n_G` stands for `H_G`.

This module adds no new analysis. It constructs, on actual points, the data that the abstract
theorem assumes:
- `n_G`;
- its triviality on `K` and on `U_I(F)`;
- the restriction `Im X(G) → Im X(M_I)` in coordinates, the step `χ ↦ λχ` of the quotation.

### Relation of `n_G` to `H_G`

`n_G(g)` is the coordinate vector of the valuation image of `g`, that is, of
`χ ↦ ord_F(χ(g))` on the rational characters `χ` of `G`, in the basis
`rationalReductiveValuationBasis` of the image lattice. By Waldspurger's definition,
`⟨χ, H_G(g)⟩ = −log_q |χ(g)|_F = ord_F(χ(g))` (`q` the residue cardinality). So `n_G(g)` are
the coordinates of `H_G(g)` in a basis of the lattice `H_G(G)`. Any two norms on `𝔞_G` are
equivalent, so `(1 + ‖n_G(g)‖)^{-r}` and `(1 + |H_G(g)|)^{-r}` agree up to constants depending
on `r`. This comparison is not formalized; the theorem is stated with `‖n_G(g)‖`, the sup norm
on `Fin r → ℤ`.

## Setting

As in `RationalInducedOrbitWavePacket`:

- `F` is a nonarchimedean local field.
- `G` is a group scheme over `Spec F` with `[IsAffineHom G.X.hom]` and
  `[LocallyOfFiniteType G.X.hom]`, and `hG : IsConnectedReductive G`.
- `i` is a maximal split torus (`hi`) and `ν` a generic cocharacter (`hν`).
- `I` is a finite set of simple roots, and `P_I(F) = M_I(F) ⋉ U_I(F)`.
- `K` is an open subgroup of `G(F)` with `hKc` (`K` is compact) and `hPK : IsIwasawaPair P₀(F) K`.
- `M_I(F)` is written as the subtype `𝐌` of `rationalPoints G`.
- `π` is an irreducible admissible representation of `M_I(F)`.
- The orbit data are `C`, `hC`, `mu`, `hsq`, with `[Finite S]` for the stabilizer `S`.
- `hM : IsIwasawaPair (P₀(F) ∩ M_I(F)) (K ∩ M_I(F))`.
- `ρ` is a measure on `Im X(M_I)` and `w : O → ℂ` a weight.

## Contents

### Factorization of lattice homomorphisms (section `LatticeFactor`)

This section works for an arbitrary group `H`, with finite types `J`, `L`.

- `torusCharacter_eq_coe_prod`: `torusCharacter m y` is the image in `ℂ` of `∏ₖ yₖ^{mₖ} ∈ Circle`.
- `torusCharacter_finiteTorusMonomial a n z`:
  `torusCharacter n (finiteTorusMonomial a z) = torusCharacter (Σⱼ nⱼ aⱼ) z`.
  In words, `∏ⱼ (∏ₗ z_l^{a_{jl}})^{n_j} = ∏ₗ z_l^{Σⱼ n_j a_{jl}}`.
- `latticeFactorMatrix nH hs φ hk` (definition). Here:
  - `nH : H →* ℤ^J` is surjective (`hs`);
  - `φ : H →* ℤ^L`;
  - `ker nH ≤ ker φ` (`hk`).

  Then `φ` factors as `θ ∘ nH` for a homomorphism `θ : ℤ^J → ℤ^L` (Mathlib's
  `MonoidHom.liftOfRightInverse`, with the right inverse `Function.surjInv hs`). Row `j` of the
  matrix is `θ(e_j)`.
- `toAdd_eq_sum_latticeFactorMatrix`: `φ(h) = Σⱼ nH(h)ⱼ aⱼ`. This is
  `LinearMap.pi_apply_eq_sum_univ` for `θ`.
- `torusCharacter_latticeFactorMatrix`:
  `torusCharacter (nH h) (finiteTorusMonomial a z) = torusCharacter (φ h) z`.

### `n_G` as a homomorphism (section `ValuationHom`)

- `rationalValuationCoordinatesHom G hG : G(F) →* Multiplicative (Fin r → ℤ)` (definition). It
  is `g ↦ n_G(g) = rationalValuationCoordinates G hG g`; `toAdd_rationalValuationCoordinatesHom`
  unfolds it by `rfl`.
- `surjective_rationalValuationCoordinatesHom`: from the surjectivity of
  `rationalValuationImageProjection` and the coordinate isomorphism.
- `ker_rationalValuationCoordinatesHom`: the kernel is `rationalCommonNormKernel G = G(F)¹`.

### The Levi subgroup (section `Levi`)

Here `j : M_I → G` is the Levi inclusion `Standard.leviHom`.

- `ker_rationalValuationCoordinatesHom_levi_le`: `ker n_{M_I} ≤ ker (n_G ∘ j)`. Both kernels
  are common norm kernels, and `rationalCommonNormKernel_le_comap` gives `M_I(F)¹ ⊆ j⁻¹(G(F)¹)`:
  rational characters of `G` restrict to rational characters of `M_I`.
- **`leviValuationRestrictionMatrix hG hi hν I`** (definition, the recorded declaration). It is
  `latticeFactorMatrix` for `nH = n_{M_I}` and `φ = n_G ∘ j`, an integer matrix of size
  `rank(M_I) × rank(G)`, with `n_G(j(m)) = Σⱼ n_{M_I}(m)ⱼ aⱼ`.
- **`leviRationalUnitaryCoordinates_symm_finiteTorusMonomial_apply m z`**. Let `χ_z` be the
  character of `G(F)` with circle coordinates `z`. Then the character of `M_I(F)` with
  coordinates `finiteTorusMonomial a z` (for `leviRationalUnitaryCoordinates`) has, at
  `m ∈ M_I(F)`, the value `torusCharacter (n_G(m)) z = χ_z(m)`. So it is the restriction of
  `χ_z` to `M_I(F)`, and the restriction `Im X(G) → Im X(M_I)` is the monomial map of `a` in
  coordinates. This is the hypothesis `hnM` of the abstract theorem.
  - Proof: the coordinates of `M_I(F)` are those of the Levi scheme, transported along
    `leviRationalPointHomeomorph` (definitional unfolding).
  - `rationalUnitaryUnramifiedCharacter_apply` for the Levi scheme then gives
    `torusCharacter (n_{M_I}(m')) (finiteTorusMonomial a z)`, where `m'` is the point of the
    Levi scheme corresponding to `m`.
  - `torusCharacter_latticeFactorMatrix` finishes, with `j(m') = m`
    (`leviRationalPointHomeomorph_apply_coe`).
- `rationalValuationCoordinatesHom_eq_one_of_mem_standardUnipotent`: `n_G(u) = 1` for
  `u ∈ U_I(F)`. This comes from `standardUnipotent_le_rationalCommonNormKernel` (with
  `standardCocharacter`) and the kernel.

### The bound (section `WavePacket`)

- `rationalValuationCoordinatesHom_eq_one_of_mem_compact hG hKc`: `n_G(k) = 1` for `k ∈ K`.
  This comes from `compactSubgroup_le_rationalCommonNormKernel` and the kernel.
- **`exists_norm_rationalInducedOrbitWavePacket_le_rationalXi_rpow hws hcoeff q r`**. Assume:
  - `ρ` is finite and left invariant;
  - `hws`: the weight `w`, composed with the orbit map and the circle coordinates of `Im X(M_I)`,
    is a smooth function on the torus (`IsSmoothFiniteTorusFunction`);
  - `hcoeff`: the coefficients of `π` are bounded by multiples of `Ξ^{M_I}`.

  Then for every `q ∈ C^∞(O, P)` and `r ∈ ℝ` there is `c > 0` with
  `|f_ψ(g)| ≤ c Ξ(g) (1 + ‖n_G(g)‖)^{-r}` for all `g ∈ G(F)`, where `Ξ = rationalXi hKc hPK`.

## Proofs

The main theorem applies `exists_norm_inducedOrbitWavePacket_le_xi_rpow` with:
- the actual data of `P_I(F)`, as in Unit 20;
- `nG = rationalValuationCoordinatesHom G hG` and `a = leviValuationRestrictionMatrix`;
- `hnK`, `hnU`, `hnM` from the three lemmas above;
- the Laurent property and continuity of `leviRationalUnitaryCoordinates`;
- the structural hypotheses of Lemma VI.2.2 used in Unit 20.

The two sides then differ only by:
- `Ξ = xi hPK δ₀` (definition of `rationalXi`);
- `toAdd (nG g) = n_G(g)` (by `rfl`).

As in Unit 20, the definition `rationalInducedOrbitWavePacket` is unfolded. The final step is
`with_reducible_and_instances exact`, because the remaining differences are instance terms.

## Scope and hypotheses

- Only standard parabolics `P_I ⊇ P₀` are covered.
- `w` replaces Waldspurger's `µ ϕ`. The smoothness of `µ` (needed to apply this to Waldspurger's
  `f_ψ`) is not proved, and the constant is not shown to be a continuous seminorm of `ϕ`.
- The theorem uses `‖n_G(g)‖` in place of `|H_G(g)|`. The norm comparison described above is not
  formalized.
- `K`, `hKc`, `hPK` and `hM` are data (ledger rows S3 and S5). `hcoeff` is a hypothesis: for `π`
  square integrable modulo the centre, it is the conclusion of Corollary III.1.2
  (`RationalSquareIntegrableRapidDecayStatement`, not yet proved).
- The remaining steps of Proposition VI.3.1 are not treated here: the estimates near the walls
  through constant terms, and the conclusion `f_ψ ∈ C(G)`.

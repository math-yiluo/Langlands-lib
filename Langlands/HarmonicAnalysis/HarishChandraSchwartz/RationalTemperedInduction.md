# Tempered representations and normalized induction on actual rational points (III.2, Lemma III.2.3)

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalTemperedInduction`,
namespace `Langlands.HarishChandraSchwartz`.

The setting is a connected reductive group `G` over a nonarchimedean local field, with a maximal
split torus, a generic cocharacter and an actual standard parabolic subgroup `P_J = M_J U_J ⊇ P₀`.
The module does three things:

- it defines tempered representations of `G(F)` (`IsRationalTempered`, the recorded declaration)
  and of `M_J(F)` (`IsRationalLeviTempered`), following Waldspurger III.2;
- it proves that both notions do not depend on the closed matrix representation `ρ` that defines
  the height `σ`;
- it proves Waldspurger's Lemma III.2.3 for the actual normalized parabolic induction `I_{P_J}^G`
  (the Library's `Aubert.General.normalizedInductionFunctor`).

Lemma III.2.3 says: let `A` be an admissible smooth representation of `M_J(F)` whose coefficients
have tempered growth for `Ξ^{M_J}` and `σ|_{M_J}`. Then the coefficients of `I_{P_J}^G A` have
tempered growth for `Ξ` and `σ`.

The Library already proves the abstract lemma, `hasTemperedCoefficients_normalizedInduction_of_tempered`.
Every hypothesis of that lemma is verified here on actual points, except for the data `K`, `hM`
and `ρ(K) ⊆ GL_N(𝒪)` described below. In particular, the height bound for Levi components is
proved here, not assumed.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers are printed
pages; the PDF page is the printed page minus 234. The author checked the quotations below on the
text of PDF pages 31 and 32.

- III.2, printed p. 265: "Notons `C^w_{lisse}(G)` le sous-espace des `f ∈ C_{lisse}(G)` pour
  lesquelles il existe `c > 0` et `r ∈ ℝ` tels que pour tout `g ∈ G`,
  `|f(g)| ⩽ c Ξ(g)(1 + σ(g))^r`. On pose `A_w(G) = A(G) ∩ C^w_{lisse}(G)`. Soit `(π, V)` une
  représentation admissible de `G`. On dit que `π` est tempérée si `A(π) ⊂ A_w(G)`."
- Lemme III.2.3, printed p. 266: "Soient `P = MU` un sous-groupe parabolique semi-standard de `G`
  et `(π, V)` une représentation admissible tempérée de `M`. Alors la représentation
  `(I_P^G π, I_P^G V)` de `G` est tempérée." The proof begins "On peut supposer `P` standard."

The Library's `HasTemperedCoefficients Ξ σ ρ` says that every coefficient `g ↦ ℓ(ρ(g) v)` (with
`v ∈ V` and `ℓ` a smooth functional) has growth at most `c Ξ(g)(1 + σ(g))^r`. This is the
condition `A(π) ⊂ A_w(G)` above.

## Setting

- `F` is a nonarchimedean local field of any characteristic.
- `G` is a group scheme over `Spec F` with `[IsAffineHom G.X.hom]` and
  `[LocallyOfFiniteType G.X.hom]`, and `hG : IsConnectedReductive G`.
- `i : S → G` is a maximal split torus (`hi`) and `ν` a generic cocharacter (`hν`).
- `J ⊆ simpleRelativeRoots i ν` (`hJ`) is the root set of a finite set `I` of simple roots
  (`hI : rootSet i ν I = J`, the Library's `Aubert.General.RationalPointFamily` indexing).
- `G(F) = rationalPoints G` carries the canonical topology, through the local instances of
  `RationalWeights`, `rationalPoint_secondCountableTopology`, `rationalPoint_t2Space` and
  `Plancherel.rationalPoints_nonarchimedeanGroup`.
- `P_J(F) = M_J(F) ⋉ U_J(F)` is the published decomposition `isSemidirectDecomposition_standard`.
  Its projection `m_P : P_J(F) → M_J(F)` is the Levi projection.
- `Ξ = rationalXi`, `σ = rationalHeight ρ` (both from `RationalWeights`) and
  `Ξ^{M_J} = rationalLeviXi` (from `RationalXiLevi`) are the published definitions.

## Contents

### Heights (section `Height`)

- **`exists_rationalHeight_projection_le ρ hG hi hν hJ hρ`**: for a closed matrix representation
  `ρ` there is `c ≥ 0` with `σ(m_P(q)) ≤ c + σ(q)` for every `q ∈ P_J(F)`.
  - Proof: by the proved `standardCocharacter`, `P_J`, `M_J` and `U_J` are the dynamic subgroups of
    a cocharacter `χ`. The Library's `MatrixRepresentation.exists_rationalMatrixNorm_levi_le` gives
    `‖ρ(m)‖ ≤ C ‖ρ(q)‖` whenever `q = m u` with `m ∈ Z(χ)(F)` and `u ∈ U(χ)(F)`.
  - It applies to `m = m_P(q)` because `m_P(q)⁻¹ q ∈ U_J(F)` (`projection_inv_mul_mem`). Taking
    `q = 1` shows `C ≥ 1`, and `c = log C`.
- **`rationalLeviSigmaBound ρ hG hi hν hJ hρ hKc`**: the Library's
  `LeviSigmaBound (isSemidirectDecomposition_standard …) K σ σ|_{M_J}`, for every compact set `K`.
  It says there is `c` with `σ(m_P(q)) ≤ c (1 + σ(q k))` for all `q ∈ P_J(F)` and `k ∈ K`.
  - Proof: `σ(q) ≤ σ(q k) + σ(k⁻¹)`, and `σ(k⁻¹) = σ(k)` is bounded on the compact set `K`
    (continuity of `σ`). Then combine with the previous bound and `σ ≥ 0`.
  - This is the consequence of Lemma II.3.1 that Waldspurger's argument needs. The second
    inequality of Lemma II.3.1 itself (the Library's `SigmaProductBound`) is not proved here.

### Tempered representations (section `Tempered`)

- `HasTemperedGrowth.of_one_add_le`: an abstract lemma. Tempered growth for a height `σ'` implies
  tempered growth for a height `σ` whenever `1 + σ' ≤ C (1 + σ)` and `Ξ, σ, σ' ≥ 0`. The exponent
  `r` becomes `max r 0`.
- **`exists_one_add_rationalHeight_le ρ hρ τ`**: for a closed matrix representation `ρ` and any
  matrix representation `τ` there is `C` with `1 + σ_τ ≤ C (1 + σ_ρ)` on `G(F)`. It follows from
  the Library's proved `Plancherel.rationalMatrixNormComparison`, `‖τ(g)‖ ≤ c ‖ρ(g)‖^d`, by
  taking logarithms.
- **`IsRationalTempered hKc ρ hPK A`** (definition, the recorded declaration): for a compact
  subgroup `K` with `G(F) = P₀(F) K`, a matrix representation `ρ` and a smooth representation `A`
  of `G(F)`, it is `HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight ρ)
  A.representation`. That is, every coefficient `g ↦ ℓ(π(g) v)` (with `v` a vector and `ℓ` a
  smooth functional) satisfies `|ℓ(π(g) v)| ≤ c Ξ(g) (1 + σ(g))^r` for some `c` and `r`. For
  admissible `A` this is Waldspurger's `A(π) ⊂ A_w(G)` (III.2).
- **`IsRationalLeviTempered hKc ρ hM A`** (definition): the same notion for a smooth
  representation `A` of `M_J(F)`, with `Ξ^{M_J} = rationalLeviXi hKc hM` (`RationalXiLevi`) and
  the restriction of `σ = rationalHeight ρ` to `M_J(F)`.
- `rationalXi_nonneg`, `rationalLeviXi_nonneg`: `Ξ, Ξ^{M_J} ≥ 0`.
- **`isRationalTempered_iff hKc ρ hPK ρ' hρ hρ' A`** and **`isRationalLeviTempered_iff`**: for
  closed matrix representations `ρ` and `ρ'`, temperedness for `σ_ρ` and for `σ_{ρ'}` agree. Both
  follow from the height comparison in both directions.

### Moduli and the main theorem (section `Induction`)

- `isUnimodularModulus_standardUnipotentPoints hG hi hν I hI`: `U_J(F)` is unimodular. This is the
  Library's `standardUnipotent_isUnimodular_of_standardCocharacterStatement` with the proved
  `standardCocharacter`.
- `modularCharacter_standardParabolicPoints hG hi hν I hI hJ q`: Mathlib's modular character of
  `P_J(F)` at `q` is the Haar modulus of conjugation by `q` on `U_J(F)`.
  - This is the second clause of the Library's `RationalParabolicModulusStatement`, obtained from
    `rationalParabolicModulus_of_reductiveUnimodularity` with the proved
    `rationalReductiveUnimodularity` and `GroupScheme.dynamicCentralizerReductive`.
  - The `RationalPointFamily` presentation `parabolic i ν I` is by definition
    `standardParabolicPoints i ν (rootSet i ν I)`, so no further comparison is needed.
- **`rationalHasTemperedCoefficients_normalizedInduction ρ hG hi hν hJ I hI K hKc hPK hM hρ hKρ A
  hA hT`** (Lemme III.2.3). The data:
  - `K` is a compact open subgroup with `G(F) = P₀(F) K` (`hPK`) and
    `M_J(F) = (P₀(F) ∩ M_J(F))(K ∩ M_J(F))` (`hM`);
  - `ρ` is a closed matrix representation (`hρ`) with `K ⊆ ρ⁻¹(GL_N(𝒪))` (`hKρ`, the source's
    `τ(K) ⊂ GL_n(𝒪)`);
  - `A` is an admissible smooth representation of `M_J(F)` (`hA`).

  The conclusion: if
  `HasTemperedCoefficients (rationalLeviXi hKc hM) (σ|_{M_J}) A.representation` (`hT`), then
  `HasTemperedCoefficients (rationalXi hKc hPK) σ ((normalizedInductionFunctor h hU).obj A).representation`,
  where `h = isSemidirectDecomposition_standard hG hi hν hJ` and
  `hU = isClosed_standardUnipotentPoints i ν J`.

  Proof: the Library's `hasTemperedCoefficients_normalizedInduction_of_tempered`, with these
  verified hypotheses:
  - `P_J(F)` is closed (`isClosed_standard_parabolic`);
  - `m_P` is continuous (`continuous_projection_standard`);
  - `G(F) = P_J(F) K` follows from `P₀(F) ⊆ P_J(F)`;
  - `G(F)` is unimodular (`rationalReductiveUnimodularity`);
  - the modulus of `P_J(F)` is given by the previous item;
  - `U_J(F)` is unimodular;
  - the `LeviData` is `rationalLeviData` of `RationalXiLevi`;
  - `δ₀ = 1` on `P₀(F) ∩ K` (`rationalMinimalModulus_eq_one`);
  - `σ ≥ 0`, and `σ` is left `K`-invariant (`rationalHeight_mul_mul`, from `hKρ`);
  - the Levi bound is `rationalLeviSigmaBound`.

- **`IsRationalLeviTempered.normalizedInduction`**: the predicate form of Lemma III.2.3 for an
  arbitrary closed `ρ'`. It assumes the hypotheses of the main theorem for one closed `ρ` with
  `ρ(K) ⊆ GL_N(𝒪)`. If `A` is admissible and tempered for `ρ'`, then `I_{P_J}^G A` is tempered
  for `ρ'`. Proof: transfer to `ρ`, apply the main theorem, and transfer back with the two
  independence results.

## Relation to the source and scope

- **Route.** Waldspurger proves Lemma III.2.3 by the exponent criterion of Proposition III.2.2 and
  the computation of Jacquet modules in I.3. The Library's abstract lemma follows the analytic
  route of the proofs of Corollary III.1.2 and Lemma VI.2.2 instead: a coefficient of
  `I_P^G π` is an integral over `K`, it is bounded through Lemma II.1.6, and the conclusion is the
  same. The module uses that route.
- **Parabolics.** Only standard `P_J ⊇ P₀` indexed by a finite set of simple roots are treated.
  The source also reduces to standard `P` ("On peut supposer `P` standard"); the reduction from
  semi-standard `P` (conjugation by `K`) is not formalized.
- **Data and hypotheses.** No structural Chapter V input is assumed beyond the data `K` with
  `G(F) = P₀(F) K` and the Iwasawa decomposition `hM` of `M_J(F)`. Both hold for a special `K`
  by Renard V.5.1 (row S19 of the Library's `notes/renard/chapter-v-structural-inputs.md`), whose
  existence is not proved in the Library. `RationalXiLevi.isIwasawaPair_standardLevi` derives
  `hM` from `K ∩ P_J = (K ∩ M_J)(K ∩ U_J)`. The condition `ρ(K) ⊆ GL_N(𝒪)` is Waldspurger's
  normalization of `τ` in I.1.
- **Choices in the definition.** `IsRationalTempered` depends on `K`, on `P₀` (through `ν`) and on
  `ρ`. Independence of `ρ` among closed matrix representations is proved here. Independence of `K`
  and `P₀` is not proved: Waldspurger fixes a special `K` and notes that `Ξ` does not depend on
  `P₀`, since all minimal parabolics are conjugate under `K` (II.1, printed p. 252). Admissibility
  is not part of the predicate; Waldspurger defines temperedness for admissible representations,
  and Lemma III.2.3 here assumes admissibility of `A` separately.
- **Moduli.** The induced representation is normalized by the Haar modulus of conjugation on
  `U_J(F)`, which is also Mathlib's modular character of `P_J(F)` by
  `modularCharacter_standardParabolicPoints`. This matches Waldspurger's `δ_P^{1/2}`
  normalization.
- **Height on the Levi.** Temperedness on `M_J(F)` is measured with `σ|_{M_J}`, the restriction of
  the height of `G`. Waldspurger defines `σ = log ‖τ(·)‖` on `G` (I.1, printed p. 242) and
  applies the notions of III.2 to `M` with `M` in place of `G`. The restriction of `τ` to `M` is an
  algebraic embedding of `M` with `τ(K ∩ M) ⊂ GL_n(𝒪)`, and its height is exactly `σ|_M`.
- **Dependencies.** The module imports `RationalXiLevi` (candidate `765686ac`, review-accepted)
  for `rationalLeviXi` and `rationalLeviData`.

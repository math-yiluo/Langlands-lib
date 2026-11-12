# The coefficient map `E_P^G` on actual rational points and Lemma VI.2.2

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedCoefficients`,
namespace `Langlands.HarishChandraSchwartz`. It imports

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalTemperedInduction` (this author's
  Unit 14): `isUnimodularModulus_standardUnipotentPoints`,
  `modularCharacter_standardParabolicPoints`, and through it `RationalXiLevi`
  (`rationalLeviXi = Ξ^{M_J}`, `rationalLeviData`, `compactSpace_subgroupOf_standardLevi`) and
  `RationalWeights` (`rationalXi = Ξ`, `rationalMinimalModulus = δ₀`,
  `rationalMinimalModulus_eq_one`, the local topology instances);
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedCoefficientTwistXi`: the abstract
  Lemma VI.2.2 in its two forms, `norm_coefficientMap_le_xi` (from its import
  `InducedCoefficientXi`) and `norm_twist_coefficientMap_le_xi`; the section `twistedSection`;
  and, through its imports, the compact picture `ProductInducedCompactPicture`
  (`Plancherel.ProductCompactPicture`) and Worker 200's `CompactInduction.coefficientMap` with
  its lemmas (`Plancherel.CompactProductInducedCoefficients`);
- `Langlands.Representation.Aubert.General.RationalLeviNormTopology`: the norm characters
  `RationalPointFamily.leviRationalNormCharacters i ν I` of the rational characters of the
  standard Levi scheme, and their continuity.

## What the module does

The setting is a connected reductive group `G` over a nonarchimedean local field `F`, with a
maximal split torus, a generic cocharacter, and an actual standard parabolic subgroup
`P = P_I(F) = M_I(F) ⋉ U_I(F) ⊇ P₀(F)`, where `I` is a finite set of simple roots.

1. It instantiates Waldspurger's coefficient map `E_P^G : L(ω, P) → C_lisse(G)` (V.1) on actual
   rational points. This is the recorded definition `rationalInducedCoefficientMap`. It also
   transfers the Library's basic properties of the abstract map to it: the integral formula,
   equivariance, bi-invariance, and the image.
2. It proves Waldspurger's Lemma VI.2.2 on actual rational points in two forms:
   - for one admissible representation `A` of `M_I(F)`;
   - uniformly over the unitary unramified twists `A ⊗ χ`, `χ ∈ Im X(M_I)`, for a fixed element
     of the compact picture. This is the reduced assertion in Waldspurger's proof.

The Library already has both forms of Lemma VI.2.2 for an abstract semidirect decomposition
(`norm_coefficientMap_le_xi`, `norm_twist_coefficientMap_le_xi`). This module checks every
structural hypothesis of those lemmas on actual points, using published results. The only
remaining inputs are the subgroup `K` with its two Iwasawa decompositions (see "Hypotheses
kept as data") and the coefficient bound `hcoeff` on `M_I(F)`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers are printed
pages; the PDF page is the printed page minus 234. The author checked the quotations below on the
text of PDF pages 54, 64 and 65.

- V.1, printed p. 288: "Pour `P ∈ P(M)` et `(ω, E) ∈ O_ℂ`, on pose
  `L(ω, P) = I_{P×P}^{G×G}(E ⊗ Ě)`. [...] On définit une application
  `E_P^G : L(ω, P) → C_lisse(G)` de la façon suivante. Identifions `L(ω, P)` à
  `(I_P^G E) ⊗ (I_P^G E)ˇ`. Pour `v ∈ I_P^G E`, `v̌ ∈ (I_P^G E)ˇ` et `g ∈ G`, on pose
  `E_P^G(v ⊗ v̌)(g) = ⟨π(g)v, v̌⟩`, où `π = I_P^G ω`. Par linéarité, on prolonge `E_P^G` à
  `L(ω, P)` tout entier. Il est clair que l'image de `E_P^G` est `A(π)`."
- Lemme VI.2.2, printed p. 298: "Soit `ψ ∈ C^∞(O, P)`. Il existe `C > 0` tel que pour tout
  `ω ∈ O` et tout `g ∈ G`, on ait l'inégalité `|(E_P^G ψ_ω)(g)| ⩽ C Ξ(g)`."
  - The proof begins: "On se ramène facilement à prouver l'assertion suivante: soient
    `(ω, E) ∈ O`, `v ∈ I_{K∩P}^K E`, `v̌ ∈ I_{K∩P}^K Ě`; alors il existe `C > 0` tel que pour
    tous `χ ∈ Im X(M)` et tout `g ∈ G`, on ait `|⟨I_P^G(ω ⊗ χ)(g) v, v̌⟩| ⩽ C Ξ(g)`. Notons
    `v_χ` l'élément de `I_P^G E_χ` dont la restriction à `K` est `v`."
  - It continues on printed p. 299: "D'après le Corollaire III.1.2, il existe donc `C > 0` tel
    que, pour tout `g ∈ G` et tout `k ∈ K`, on ait
    `|⟨ω(m_P(kg)) v(k_P(kg)), v̌(k)⟩| ⩽ C Ξ^M(m_P(kg))`. [...] et il reste à appliquer le
    Lemme II.1.6."

## Setting

- `F` is a nonarchimedean local field (`[IsNonarchimedeanLocalField F]`).
- `G` is a group scheme over `Spec F` with `[IsAffineHom G.X.hom]` and
  `[LocallyOfFiniteType G.X.hom]`, and `hG : IsConnectedReductive G`.
- `i : S → G` is a maximal split torus (`hi`) and `ν` a generic cocharacter (`hν`).
- `I` is a finite set of simple roots (`RationalPointFamily.SimpleRoot i ν`). The parabolic is
  `P_I(F) = standardParabolicPoints i ν (rootSet i ν I)`, with Levi
  `M_I(F) = standardLeviPoints i ν (rootSet i ν I)` and unipotent radical
  `U_I(F) = standardUnipotentPoints i ν (rootSet i ν I)`. The decomposition
  `P_I(F) = M_I(F) ⋉ U_I(F)` is the published `isSemidirectDecomposition_standard`.
- `G(F) = rationalPoints G` has its canonical topology and Borel measurable structure. These come
  from the local instances of `RationalWeights` together with `rationalPoint_secondCountableTopology`,
  `rationalPoint_t2Space` and `Plancherel.rationalPoints_nonarchimedeanGroup`.
- `K` is an open subgroup of `G(F)` with
  - `hKc`: `K` is compact;
  - `hPK : IsIwasawaPair P₀(F) K`, i.e. `G(F) = P₀(F) K`.
- `A : SmoothRep ℂ M_I(F)` is a smooth representation, with `hA : A.IsAdmissible`.
- `L(A, P)` is the Library's `productInducedCoefficientObject` for the actual decomposition. It
  is the normalized induction from `P × P` to `G × G` of `A ⊠ A^∨`, i.e. Waldspurger's
  `I_{P×P}^{G×G}(E ⊗ Ě)`.

## Contents

### Topological facts about `P_I(F)`

- `isClosed_standardParabolicPoints_rootSet hG hi hν I`: `P_I(F)` is closed in `G(F)`. This is
  the Library's `RationalPointFamily.isClosed_standard_parabolic` with the proved
  `standardCocharacter`.
- `locallyCompactSpace_standardParabolicPoints_rootSet`: hence `P_I(F)` is locally compact.
- `exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK g`: `G(F) = P_I(F) K`. This follows
  from `G(F) = P₀(F) K` and `P₀(F) ⊆ P_I(F)` (`standardParabolicPoints_empty_le`).
- `compactSpace_leftQuotient_standardParabolicPoints_rootSet`: `P_I(F) \ G(F)` is compact, being
  the image of the compact set `K`.

### The coefficient map

- **`rationalInducedCoefficientMap hG hi hν I hKc hPK A hA`** (definition, the recorded
  declaration). This is a ℂ-linear map from `L(A, P)` to `LocallyConstant G(F) ℂ`. It is the
  Library's `CompactInduction.coefficientMap`, applied to the following actual data:
  - the decomposition `isSemidirectDecomposition_standard` and the closedness of `U_I(F)` and
    `P_I(F)`;
  - the continuity of the Levi projection (`continuous_projection_standard`);
  - `G(F) = P_I(F) K`, and the compactness of `K`;
  - the unimodularity of `G(F)` (`RationalPointFamily.rationalReductiveUnimodularity`);
  - the identification of Mathlib's modular character of `P_I(F)` with the Haar modulus of
    conjugation on `U_I(F)` (`modularCharacter_standardParabolicPoints`);
  - the admissibility of `A`.

  The abstract map is the coefficient map of the normalized induction `I_P^G A` (the Library's
  `normalizedCoefficientMap`), composed with the Library's identification
  `coefficientTensorEquiv` of `L(A, P)` with `(I_P^G A) ⊗ (I_P^G A)^∨`. This identification is
  Waldspurger's "Identifions `L(ω, P)` à `(I_P^G E) ⊗ (I_P^G E)ˇ`". The duality between
  `I_P^G A` and `I_P^G A^∨` is the one given by integration over `K` against the Haar probability
  measure of `K`.
  - On the image of a pure tensor `f ⊗ f^∨`, the value at `g` is `∫_K ⟨f^∨(k), f(k g)⟩ dk`.
    This is the Library's `CompactInduction.coefficientMap_tmul`, Waldspurger's
    `⟨π(g) f, f^∨⟩`. The module does not restate it.
  - What the module proves instead is the integral formula for every element
    (`rationalInducedCoefficientMap_integral`).
- `rationalInducedCoefficientMap_eq_coefficientMap`: the definition unfolded (by `rfl`). Its
  only role is to transfer the Library's lemmas.
- **`rationalInducedCoefficientMap_integral Φ g`**: for every `Φ ∈ L(A, P)` and `g ∈ G(F)`,
  `E_P^G(Φ)(g) = ∫_K ⟨Φ(k g, k)⟩ dk`. Here `⟨Φ(k g, k)⟩` is the contraction of
  `Φ(k g, k) ∈ A ⊗ A^∨` by the pairing (`CompactInduction.integrand`), and `dk` is the Haar
  probability measure of `K` (`CompactInduction.measure`).
- **`rationalInducedCoefficientMap_action x Φ g`**: `E_P^G` intertwines the action of
  `G(F) × G(F)` on `L(A, P)` with the translation `φ ↦ (g ↦ φ(x₂⁻¹ g x₁))`.
- `rationalInducedCoefficientMap_biInvariant Φ`: every `E_P^G(Φ)` is invariant on both sides
  under one open subgroup `L` of `G(F)`.
- **`range_rationalInducedCoefficientMap`**: the image of `E_P^G` equals the image of the
  Library's `normalizedCoefficientMap` for `I_P^G A`, i.e. the space of matrix coefficients of
  `I_P^G A`. This is Waldspurger's "l'image de `E_P^G` est `A(π)`".

### Lemma VI.2.2

Further datum: `hM : IsIwasawaPair (P₀(F) ∩ M_I(F)) (K ∩ M_I(F))` (both as `subgroupOf
M_I(F)`), the Iwasawa decomposition of `M_I(F)` that defines `Ξ^{M_I} = rationalLeviXi hKc hM`.

- **`norm_rationalInducedCoefficientMap_le_rationalXi hcoeff Φ`** (Lemma VI.2.2 for one
  representation). The hypothesis `hcoeff` says that every coefficient of `A` is bounded by a
  multiple of `Ξ^{M_I}`:

  `∀ v ℓ, ∃ C > 0, ∀ m ∈ M_I(F), |ℓ(A(m) v)| ≤ C Ξ^{M_I}(m)`.

  This is the conclusion of Corollary III.1.2 for `M_I` that Waldspurger uses. The theorem then
  gives, for every `Φ ∈ L(A, P)`, some `C > 0` with `|E_P^G(Φ)(g)| ≤ C Ξ(g)` for all
  `g ∈ G(F)`, where `Ξ = rationalXi hKc hPK`.
- `rationalTwistedSection hG hi hν I hKc hPK A χ F₀` (definition). This is Waldspurger's `v_χ`.
  - `χ` is a unitary unramified character of `M_I(F)`: an element of the Library's
    `unramifiedCharacters (leviRationalNormCharacters i ν I)`. These are the continuous
    characters `M_I(F) → ℂˣ` that are trivial on the common kernel of the norms `|χ'|_F` of all
    rational characters `χ'` of the standard Levi scheme. This is `X(M_I)`.
  - `F₀` is an element of the compact picture `ProductInducedCompactPicture`, i.e.
    Waldspurger's `L_K(ω, P) = I_{K∩P × K∩P}^{K×K}(E ⊗ Ě)` (VI.1).
  - `rationalTwistedSection χ F₀` is the element of `L(A ⊗ χ, P)` whose restriction to `K × K`
    is `F₀`. It is the Library's `twistedSection` on actual data.
  - `rationalTwistedSection_eq_twistedSection` is its unfolding (by `rfl`).
- **`norm_rationalInducedCoefficientMap_twist_le_rationalXi hcoeff F₀`** (Lemma VI.2.2,
  uniform form). Under the same `hcoeff`, for a fixed `F₀` there is a single `C > 0` such that
  for every `χ` as above with `|χ(m)| = 1` for all `m` (Waldspurger's `χ ∈ Im X(M_I)`) and every
  `g ∈ G(F)`:

  `|E_P^G(v_χ)(g)| ≤ C Ξ(g)`.

  Here `E_P^G` is `rationalInducedCoefficientMap` for the twist
  `A ⊗ χ = SmoothRep.twist χ A`, which is admissible by `SmoothRep.isAdmissible_twist_iff`.
  This is the reduced assertion in Waldspurger's proof, with `v ⊗ v̌` replaced by an arbitrary
  element `F₀` of `L_K(ω, P)`.

## Proofs

Every theorem about `E_P^G` and `v_χ` applies the corresponding Library lemma, with the same
actual data as the definition:

- `CompactInduction.coefficientMap_integral`, `coefficientMap_action`,
  `coefficientMap_biInvariant` and `range_coefficientMap` for the general properties;
- `norm_coefficientMap_le_xi` and `norm_twist_coefficientMap_le_xi` for Lemma VI.2.2.

The proof of Lemma VI.2.2 supplies the following extra hypotheses of the abstract lemmas:

- `U_I(F)` is unimodular: `isUnimodularModulus_standardUnipotentPoints`.
- The Levi data of `P_I(F)` for `K`: `rationalLeviData`. This is the input of the Library's
  Lemma II.1.6 (`LeviData.norm_compactIntegral_le_xi`).
- `δ₀ = 1` on `P₀(F) ∩ K`: `rationalMinimalModulus_eq_one`.
- The compactness of `K` and of `K ∩ M_I(F)`: `compactSpace_subgroupOf_standardLevi`.
- `Ξ = xi hPK δ₀` holds by definition of `rationalXi`.

The abstract lemmas themselves follow Waldspurger's route: Corollary III.1.2 (here `hcoeff`),
`|χ| = 1`, and Lemma II.1.6.

Technical point. The Library declares `standardLeviPoints` as a subgroup of the unfolded point
type `Over.mk (𝟙 _) ⟶ G.X` rather than of `rationalPoints G`. For this reason:

- the statements write the Levi subgroup as the subtype
  `{x : rationalPoints G // @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
  (standardLeviPoints …) x}`;
- every Library lemma is instantiated with `(G := rationalPoints G)`;
- the final steps use `with_reducible_and_instances exact`. The remaining differences between
  goal and lemma are only instance terms (`rationalWeightsTopology` against
  `rationalPointTopology F G.X`, and the group structure of the Levi subtype). At this
  transparency they are compared argument by argument, without unfolding the coefficient map.

## Hypotheses kept as data, and scope

- `K`, `hKc`, `hPK` and `hM` are data. For a special maximal compact `K`, Bruhat–Tits theory
  (Renard V.5.1) gives both decompositions, `G(F) = P₀(F) K` and
  `M_I(F) = (P₀(F) ∩ M_I(F))(K ∩ M_I(F))`. The existence of such a `K` is not proved in the
  Library (structural rows S3 and S5 of the ledger `notes/plancherel/actual-point-ledger.md`).
  The Library's `isIwasawaPair_standardLevi` (module `RationalXiLevi`) derives `hM` from
  `G(F) = P₀(F) K` and `m_P(P_I(F) ∩ K) ⊆ K`.
- `hcoeff` is a hypothesis. For square-integrable `A` modulo the centre it is the conclusion of
  Corollary III.1.2. The actual statement of III.1.2 is the Library's
  `RationalSquareIntegrableRapidDecayStatement` (unproved; proof task published).
- Only standard parabolics `P_I ⊇ P₀` are covered. The semi-standard case, and the passage from
  Waldspurger's `ψ ∈ C^∞(O, P)` to fixed elements of the compact picture, are not formalized
  here. The Library proves the abstract version of the latter for families of finite type
  (`finiteSmoothFamilies`, module `InducedCoefficientTwistXi`), but it is not instantiated here.
- The formula `E_P^G(f ⊗ f^∨)(g) = ∫_K ⟨f^∨(k), f(k g)⟩ dk` is the Library's
  `CompactInduction.coefficientMap_tmul`. It is not restated for `rationalInducedCoefficientMap`.

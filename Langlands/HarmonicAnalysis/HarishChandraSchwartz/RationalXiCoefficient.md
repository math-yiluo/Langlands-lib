# `Ξ` as a matrix coefficient of the actual `I_{P₀}^G 1`

Author: Worker 3642 (formerly Worker 19), task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927`
(revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiCoefficient`, namespace
`Langlands.HarishChandraSchwartz`. It uses:

- `RationalWeights`: `rationalMinimalModulus` (`δ₀`, the Haar modulus of conjugation by `P₀(F)`
  on `U₀(F)`), `rationalMinimalModulus_eq_one`, `rationalXi` (`Ξ`), and the local instances
  `rationalWeightsTopology` etc. (the canonical rational-point topology on
  `G(F) = rationalPoints G` and its Borel structure);
- `Spherical`: `IsIwasawaPair`, `iwasawaWeight` (`φ(p k) = δ(p)^{1/2}`) with
  `iwasawaWeight_mul_left`, `iwasawaWeight_mul_right`, `iwasawaWeight_of_mem`, `xi`,
  `normalizedHaar`;
- `Aubert.General.Parabolic`: `IsSemidirectDecomposition`, `normalizedInductionFunctor`,
  `inducingRepresentation`; `Aubert.General.RationalInductionDualityReduction`:
  `normalizedInductionFunctor_obj_isAdmissible`; `Induction.smoothFunctionOf`,
  `Induction.eval_isLocallyConstant`;
- `CoefficientIndependence`: `coefficientFunctionSpace` (`A(π)`) and
  `matrixCoefficient_mem_coefficientFunctionSpace`;
- `StandardCocharacterProof`: `standardCocharacter`; `EndpointReductions`:
  `isStandardCocharacter_empty_self`; `Aubert.General.DynamicParabolic` and
  `DynamicInductionExactness`: `dynamic_isSemidirectDecomposition`,
  `continuous_dynamic_projection`; `Plancherel.rationalPoints_nonarchimedeanGroup`;
- `Jacquet.DynamicCasselmanConstantTerm` (Worker 3642): `HasDynamicConstantTerm`,
  `IsDynamicConstantTerm`, `dynamicConstantTerm`, `dynamicConstantTerm_spec`, `dynamicLeviPoints`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Printed page numbers; the
PDF page is the printed page minus 234. The quotations were checked against the rendered PDF.

- II.1, printed pp. 250–251: "Notons `(1, ℂ)` la représentation triviale de `M_0`,
  `(π, V) = (I_{P_0}^G 1, I_{P_0}^G ℂ)`, `e` l'unique élément de `V` invariant par `K` et tel que
  `e(1) = 1`. Remarquons que `(π̌, V̌) = (π, V)`. Pour `g ∈ G`, on pose `Ξ(g) = ⟨π(g)e, e⟩`." and
  "On a l'égalité: `Ξ(g) = ∫_K δ_0(m_0(kg))^{1/2} dk`."
- I.6, printed p. 249: "pour toute représentation admissible `π` de `G`, notons `A(π)` le
  sous-espace de `C_lisse(G)` engendré par les coefficients de `π`." Proposition I.6.2: "Soient
  `f ∈ A(G)` et `P = MU` un sous-groupe parabolique semi-standard de `G`. Il existe un unique
  élément `f_P ∈ A(M)` vérifiant la propriété suivante: pour tout `m ∈ M`, il existe `ε > 0` tel
  que pour tout `a ∈ A_M` vérifiant `|α(a)|_F < ε` pour tout `α ∈ Σ(P)`, on ait l'égalité
  `δ_P(ma)^{-1/2} f(ma) = f_P(ma)`."

## Definitions

Setting: a nonarchimedean local field `F`, a group scheme `G` over `F` with
`[IsAffineHom G.X.hom]` and `[LocallyOfFiniteType G.X.hom]`, a split torus `i : S → G`, a
cocharacter `ν`, and a decomposition
`h : IsSemidirectDecomposition P₀(F) M₀(F) U₀(F)` of the minimal standard parabolic
`P₀(F) = standardParabolicPoints i ν ∅` (supplied as a hypothesis in the general part; proved below
for connected reductive `G` and generic `ν`).

- `trivialSmoothCharacter`: the trivial character of a topological group, as a Library
  `Induction.SmoothCharacter`.
- `normalizedInducedOfSmoothFunctions`: a smooth induced function of
  `inducingRepresentation h hU A`, read as a vector of
  `(normalizedInductionFunctor h hU).obj A`. The two carriers are equal by definition. This
  wrapper is generic in `A`, so the kernel checks the identification only once.
- **`rationalMinimalInduced h`** (Waldspurger's `(π, V) = I_{P₀}^G 1`): the Library's normalized
  induction `normalizedInductionFunctor h hU` of the trivial character of `M₀(F)`. Its vectors are
  the smooth functions `f` on `G(F)` with `f(p g) = δ₀(p)^{1/2} f(g)`, and `G(F)` acts by right
  translation (`rationalMinimalEval_representation`). `rationalMinimalInducing h` is the inducing
  representation, and `rationalMinimalInducing_apply` computes it as
  `p · z = δ₀(p)^{1/2} z`. `rationalMinimalEval h f g` is the value of `f` at `g`.
- **`rationalSphericalVector h hKo hKc hPK`** (Waldspurger's `e`): for a compact open subgroup `K`
  with `G(F) = P₀(F) K`, the function `e_K = iwasawaWeight`, `e_K(p k) = δ₀(p)^{1/2}`. It is
  right `K`-invariant and satisfies `e_K(1) = 1` (`rationalMinimalEval_sphericalVector_one`). It
  is built as `rationalSphericalFunction` via `Induction.smoothFunctionOf`. Covariance is
  `iwasawaWeight_mul_left` with `δ₀ = 1` on `P₀(F) ∩ K`; right invariance is
  `iwasawaWeight_mul_right`.
- **`rationalSphericalFunctional h hKo hKc`**: the smooth functional
  `ℓ_K(f) = ∫_K f(k) dk` on `I_{P₀}^G 1`, for the Haar probability measure of `K`. It is linear
  because smooth induced functions are locally constant (`continuous_rationalMinimalEval`,
  `integrable_rationalMinimalEval`). It is fixed by `K` under the contragredient action
  (`rationalSphericalLinearFunctional_mem_fixedVectors`), by right invariance of the Haar measure
  of the compact group `K`.

## Results

- `compactSpace_leftQuotient_of_isIwasawaPair`: if `G = P K` with `K` compact, then `P \ G` is
  compact (the image of `K`).
- **`rationalXi_eq_sphericalCoefficient`** (Waldspurger II.1): for every `g ∈ G(F)`,
  `Ξ(g) = ℓ_K(π(g) e_K)` (as complex numbers), where `π = I_{P₀}^G 1`. Proof:
  `ℓ_K(π(g) e_K) = ∫_K e_K(k g) dk`, which is the definition of `xi`.
- **`ofReal_rationalXi_mem_coefficientFunctionSpace`**: `Ξ ∈ A(I_{P₀}^G 1)`, i.e. `Ξ` is the
  matrix coefficient of `I_{P₀}^G 1` for `ℓ_K` and `e_K`.
- **`rationalMinimalInduced_isAdmissible`**: if the Levi projection of `h` is continuous, then
  `I_{P₀}^G 1` is admissible. Proof: the Library's `normalizedInductionFunctor_obj_isAdmissible`,
  using compactness of `P₀(F) \ G(F)` and the finite dimensionality of the trivial character.
- **`isSemidirectDecomposition_minimalStandard`**: for connected reductive `G`, a maximal split
  torus `i` and a generic cocharacter `ν`, `P₀(F) = M₀(F) ⋉ U₀(F)`. Proof: the Library's
  `standardCocharacter` (with the standard cocharacter `ν` of the empty face) identifies
  `P_∅, M_∅, U_∅` with the dynamic subgroups of `ν`, whose decomposition is
  `dynamic_isSemidirectDecomposition`.
- **`continuous_projection_minimalStandard`**: in the same setting, the projection of every such
  decomposition is continuous. It is the dynamic one after rewriting the three subgroups, and that
  one is continuous by `continuous_dynamic_projection`.
- **`exists_admissible_ofReal_rationalXi_mem`**: for connected reductive `G` and generic `ν`, `Ξ`
  lies in `A(A)` for an admissible smooth representation `A` of `G(F)` (namely `I_{P₀}^G 1`), so
  `Ξ ∈ A(G)` in Waldspurger's sense.
- **`rationalXi_hasDynamicConstantTerm`**: for connected reductive `G`, generic `ν`, every
  cocharacter `χ : 𝔾_m → G` and every unit `t` with `tⁿ → 0`, `Ξ` has a constant term along the
  powers of `χ(t)`, in the sense of `HasDynamicConstantTerm`. It satisfies `IsDynamicConstantTerm`,
  and `dynamicConstantTerm χ t Ξ` lies in `A(B)` for an admissible smooth representation `B` of
  `M = Z(χ)(F)`. This is Proposition I.6.2 for `f = Ξ` in the dynamic form of
  `DynamicCasselmanConstantTerm`, applied through `dynamicConstantTerm_spec`. It holds along the
  tail `{χ(t)^r ; r ≥ r₀}` in place of Waldspurger's cone `|α(a)|_F < ε`, with `δ_U` (modulus of
  conjugation on `U(χ)(F)`) in place of `δ_P`; `DynamicCasselmanConstantTerm.md` explains both
  differences.

No structural hypothesis is used in any of these results. The reductive results use only
`IsConnectedReductive G`, `IsMaximalSplitTorus i` and `IsGenericCocharacter i ν`, and the general
results only the displayed decomposition, continuity and Iwasawa data.

## Correspondence with the source and scope

- Waldspurger pairs `π(g)e` with `e` viewed in `V̌` through his identification `(π̌, V̌) = (π, V)`.
  Here `e` is replaced by the smooth functional `ℓ_K`. Under the standard pairing
  `⟨f, f'⟩ = ∫_K f(k) f'(k) dk` between `I_{P₀}^G 1` and itself, `ℓ_K` is the image of `e_K`,
  since `e_K = 1` on `K` (mathematical background). The identification `(π̌, V̌) = (π, V)` itself is not formalized here, and
  is not needed for `Ξ ∈ A(π)`.
- Waldspurger fixes the special maximal compact subgroup `K`. Here `K` is any compact open
  subgroup with `G(F) = P₀(F) K` (`IsIwasawaPair`), as in `RationalWeights`.
- The induced representation is the Library's `normalizedInductionFunctor`, normalized by the
  positive square root of the modulus of conjugation on `U₀(F)`. For connected reductive `G` this
  is the normalization by `δ_{P₀}^{1/2}` of the source (the identification of the two moduli on
  `P₀(F)` is the standard one and is not proved here).
- The uniqueness of a `K`-fixed vector with `e(1) = 1` is not formalized.

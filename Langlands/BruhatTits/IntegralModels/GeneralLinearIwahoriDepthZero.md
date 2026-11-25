# Depth-zero theory of the `GL_N` Iwahori model

Module `Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriDepthZero`.

Let `F` be a nonarchimedean local field with valuation ring `𝒪 = 𝒪[F]`,
residue field `𝓀 = 𝓀[F]` and `q = Nat.card 𝓀`. The published modules
`GeneralLinearIwahoriModel` and `GeneralLinearIwahoriQuotient` construct the
Iwahori model data `iwahoriModelData F N` of `GL_N` and a reductive quotient
`iwahoriQuotientData F N` of its special fibre. The radical is the unipotent
kernel `1 + J` and the quotient is the diagonal torus `diagTorus F N`, the unit
group scheme of `𝓀^N`. The published comparison module
`GeneralLinearIwahoriComparison` defines the group-level Iwahori subgroup
`I = generalLinearIwahoriPoints F N`, its subgroup
`I^+ = generalLinearIwahoriPositivePoints F N` and the projection
`generalLinearIwahoriDiagonal : I →* (singletons N).Levi 𝓀` (reduce, then take
the diagonal blocks).

This module applies the Library's general depth-zero results on supplied model
data to the Iwahori data. These are `SpecialFibreQuotientData.parahoricReduction`,
`depthZeroQuotientEquiv` and `ker_parahoricReduction` (module
`DepthZeroReduction`), `localField_index_positivePoints_subgroupOf` (module
`FiniteReductiveQuotient`), `localField_isOpen_positivePoints` and
`localField_isCompact_positivePoints` (module `DepthZeroCompactOpen`), and the
published `IntegralModel.isOpen_integralPoints_localField` and
`IntegralModel.isCompact_integralPoints_localField`. It computes their values
and compares them with the group-level description. This is the
non-hyperspecial counterpart of the published `GeneralLinearDepthZero`, which
does the same for the standard model `GL_{N,𝒪}`.

## Provenance

The module is derived. Its statements apply published Library results to the
published Iwahori data and compare the values with the published group-level
Iwahori subgroup. The module is a proved regression example, and it recovers
the Library's concrete `GL_n` results from the general theory with proved
comparisons.

The comparison values come from Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`
(SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`).

- Definition 7.4.5(2) (printed p. 256 / PDF p. 287): when `Ω` is a chamber,
  `G(k)^0_Ω` is the Iwahori subgroup associated to `Ω`.
- 13.2.6 (printed p. 470 / PDF p. 501): the kernel of the reduction
  `P_{x,0} → Ḡ_x(f)` is `P_{x,0+}`, and `P_{x,0}/P_{x,0+}` is identified with
  `Ḡ_x(f)`, the `f`-points of the maximal reductive quotient of the special
  fibre. For the Iwahori subgroup of `GL_N` the reductive quotient is the
  diagonal torus, so the expected values are `(𝓀ˣ)^N` and
  `[P_{x,0} : P_{x,0+}] = (q - 1)^N`.

The authors' corrections of 1 November 2024
(`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`) do not
amend either item. In §7.4 they amend only the sentence before Remark 7.4.2,
Remark 7.4.2 and Lemma 7.4.4(2). In Chapter 13 they amend 13.5.2, 13.6.2 and
13.8.5.

KP's objects are not used in the Lean statements. The values above are the ones
the Library's general results are compared against. No external code is
adapted.

## Setting

The general lemma is stated for `R : CommRingCat` in universe `u` and the
published unit group schemes `FiniteFreeAlgebraUnits.groupScheme b` of finite
free `R`-algebras. The rest is stated for a field `F` in universe `u` with
`ValuativeRel F`, `TopologicalSpace F` and `IsNonarchimedeanLocalField F`, and
`N : ℕ`. A point `g` of `GL_N` over `F` is read as a matrix through the
published `GeneralLinear.rationalPointsEquiv N (CommRingCat.of F) g`. The
topological statements use the canonical topology
`rationalPointTopology F (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).X`
on the `F`-points, as in `DepthZeroCompactOpen`.

## Declarations

### A section-unit lemma

Namespace `Langlands.GroupScheme.FiniteFreeAlgebraUnits`.

- `sectionUnitsEquiv_baseChange_congr_map`: take a section `x` over `Spec R`.
  Base change it along `Spec R' → Spec R`, transport it by `baseChangeIso` and
  by `congrIso` along an algebra isomorphism `e : R' ⊗[R] A ≃ₐ[R'] A₁`, and map
  it by `map b₁ b' f`. The unit of the result is `f (e (1 ⊗ u))`, where `u` is
  the unit of `x`. It chains the published `sectionUnitsEquiv_map`,
  `sectionUnitsEquiv_congrIso` and `sectionUnitsEquiv_baseChange`.

### The residue-field points of the diagonal torus

Namespace `Langlands.BruhatTits.IntegralModels`, as is everything below.

- `diagTorusPointsEquiv F N` (definition): `rationalPoints (diagTorus F N) ≃*
  (Fin N → 𝓀ˣ)`. It is the published `sectionUnitsEquiv (diagBasis F N)`
  followed by Mathlib's `MulEquiv.piUnits`.
- `card_diagTorus_rationalPoints`: the diagonal torus has `(q - 1)^N`
  residue-field points, by `Nat.card_pi` and `Nat.card_units`.

### The reduction map is the diagonal of the residue matrix

- `diagTorusPointsEquiv_reductiveReduction`: for an integral section `x`, the
  `i`-th entry of the reduction `(iwahoriQuotientData F N).reductiveReduction x`
  is the residue of the `(i, i)` entry of the published `sectionUnit F N x`. The
  reduction is the composite that defines the quotient's projection in
  `GeneralLinearIwahoriQuotient`, so the lemma above applies with the published
  `specialDiag_one_tmul`.
- `diagTorusPointsEquiv_parahoricReduction`: let `g` be a point of the neutral
  integral points and `v ∈ GL_N(𝒪)` with matrix of `g` equal to the image of
  `v`. Then the `i`-th entry of `parahoricReduction g` is the residue of
  `v i i`. The integral section of `g` has the matrix of `g` as unit (published
  `iwahoriIntegralPointMap_matrix`), and `𝒪 → F` is injective.
- `iwahoriModelData_integralPoints`: the neutral integral points of
  `iwahoriModelData F N` are `I`, from the published `neutralPoints_eq` and
  `iwahoriModelData_neutralPoints`.
- `generalLinearIwahoriDiagonal_apply`: if the matrix of `g ∈ I` is the image
  of `v ∈ GL_N(𝒪)`, then every entry of the `i`-th block of
  `generalLinearIwahoriDiagonal F N g` is the residue of `v i i`. It uses the
  published `generalLinearReductionPreimageResidue_apply`, `singletons_index`
  and `glResidueMap_apply`.
- `singletonLevi_parahoricReduction`: **comparison with the group-level
  projection.** For `g` in the neutral integral points,
  `singletonLevi 𝓀 (diagTorusPointsEquiv F N (parahoricReduction g))` equals
  `generalLinearIwahoriDiagonal F N g`, with `g` viewed in `I`. Here
  `singletonLevi` is the published identification of `N`-tuples of units with
  the Levi of the singleton block shape.

### `I` modulo `I^+` and the index

- `iwahoriDepthZeroQuotientEquiv F N` (definition, the declared one): the
  neutral integral points modulo the kernel of `parahoricReduction` are
  isomorphic to `Fin N → 𝓀ˣ`. It is the published `depthZeroQuotientEquiv`,
  with the radical and fppf clauses of the published
  `iwahoriQuotientData_isReductiveQuotient`, followed by
  `diagTorusPointsEquiv`. `iwahoriDepthZeroQuotientEquiv_mk` records that the
  class of `g` goes to `diagTorusPointsEquiv F N (parahoricReduction g)`.
- `iwahoriQuotientData_ker_parahoricReduction`: the kernel of
  `parahoricReduction` is `I^+` (as `subgroupOf` the neutral integral points).
  This is the published `ker_parahoricReduction` with the published
  `iwahoriQuotientData_positivePoints`.
- `iwahori_index_positivePoints_subgroupOf`: the index of
  `(iwahoriQuotientData F N).positivePoints` in the neutral integral points is
  `(q - 1)^N`. It is the published
  `localField_index_positivePoints_subgroupOf` with
  `card_diagTorus_rationalPoints`. With `iwahoriModelData_integralPoints` and
  `iwahoriQuotientData_positivePoints` this is the index `[I : I^+]` of the
  published `generalLinearIwahoriPositivePoints_relIndex`, which was computed
  there from finite group theory. The general theory gives the same value.

### `I` and `I^+` are compact open

- `isOpen_generalLinearIwahoriPoints` and `isCompact_generalLinearIwahoriPoints`:
  `I` is open and compact in `GL_N(F)`. They rewrite with
  `iwahoriModelData_integralPoints` and apply the published
  `isOpen_integralPoints_localField` and `isCompact_integralPoints_localField`
  to the neutral model.
- `isOpen_generalLinearIwahoriPositivePoints` and
  `isCompact_generalLinearIwahoriPositivePoints`: `I^+` is open and compact in
  `GL_N(F)`. They rewrite with `iwahoriQuotientData_positivePoints` and apply
  the published `localField_isOpen_positivePoints` and
  `localField_isCompact_positivePoints`. These need `GL_N` over `F` to be
  locally of finite type, which follows from the published
  `GeneralLinear.smoothStatement`.

A local instance, `generalLinearIwahoriDepthZeroAffine`, supplies the
published `GeneralLinear.isAffine_groupScheme` for `GL_N` over `F`, as other
Library modules do.

## Not claimed

No building and no point appear. Nothing here identifies `iwahoriModelData F N`
with KP's parahoric model attached to a chamber, so `I` and `I^+` are not
identified with KP's `P_{x,0}` and `P_{x,0+}`. The agreement with the values
of KP 13.2.6 is only through the explicit descriptions above. Only the
standard Iwahori subgroup (upper triangular modulo the maximal ideal) is
treated; other chambers and other groups are not covered.

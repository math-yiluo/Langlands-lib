# The actual standard Levi subgroups as group schemes: `Ξ`, `σ`, `P₀` and `δ₀`

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviScheme`,
namespace `Langlands.HarishChandraSchwartz`.

The published modules of this program define Waldspurger's `Ξ^M`, temperedness and the Schwartz
space `C(M)` for an actual standard Levi subgroup `M_J(F)` as a *subgroup* of `G(F)`
(`rationalLeviXi`, `IsRationalLeviTempered`, the target of `rationalConstantTerm`). The statements
for a group (Lemma II.1.5, Corollary III.1.2, Theorem VIII.1.2, ...) are stated for the rational
points of a connected reductive *group scheme*. This module connects the two. For the Levi group
scheme `L = Standard.leviScheme i ν J` with its closed embedding `j = Standard.leviHom i ν J`, it
proves:

- `L` is connected reductive, the torus `i` factors through a maximal split torus of `L`, and `ν`
  is generic for it;
- the minimal standard parabolic of `L` and its radical are the preimages of `P₀` and `U₀`, so
  that on rational points they are `P₀(F) ∩ M_J(F)` and `M_J(F) ∩ U₀(F)`;
- the modulus `δ₀` of `L` is `δ₀^{M_J}`;
- `Ξ` of `L`, for the compact subgroup `j⁻¹(K)`, is `Ξ^{M_J}` read through `j`;
- the height of `ρ ∘ j` is `σ` restricted to `M_J(F)`.

The comparisons are proved with the hypotheses recorded below; the Iwasawa and
Xi comparisons retain the supplied Levi decomposition `hM`. The recorded declaration is the
definition `leviSchemeCompact`, the subgroup `j⁻¹(K)` of `L(F)`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers below are the
printed ones; the PDF page is the printed page minus 234. The author checked the quotations
against the text of PDF pages 6 and 18.

- I.1, printed p. 240: "le groupe `M ∩ K` vérifie relativement à `M` les mêmes propriétés que `K`
  relativement à `G`" (for a semi-standard Levi subgroup `M`).
- II.1, printed p. 252: "Soit `P = MU` un sous-groupe parabolique semi-standard de `G`. On définit
  une fonction `Ξ^M` sur `M` comme on vient de définir `Ξ` sur `G`."

Waldspurger treats a Levi subgroup `M` both as a subgroup of `G` and as a reductive group in its
own right, with the data `(M, P₀ ∩ M, M ∩ K, δ₀^M)`. The module proves that the two readings agree
for the Library's actual objects.

D. Renard, *Représentations des groupes réductifs p-adiques* (2026 version; literature id
`renard-2026-representations-groupes-reductifs-padiques`), V.5.1 (5), printed p. 122: the minimal
parabolic of a standard Levi `M` is `P_∅ ∩ M`. The Library records the scheme-level form of this
compatibility, together with the minimality assertions, as the unproved
`StandardLeviMinimalParabolicCompatibilityStatement`. This module proves the rational-point
equality `P₀^L(F) = P₀(F) ∩ M_J(F)` used below for connected reductive `G`, a maximal split torus
and a generic cocharacter. It does not prove the minimality assertions of that statement.

## Setting

`F` is a nonarchimedean local field of any characteristic. `G` is a group scheme over `Spec F`
with `[IsAffineHom G.X.hom]` and `[LocallyOfFiniteType G.X.hom]`. Where stated,
`hG : IsConnectedReductive G`, `hi : IsMaximalSplitTorus i`, `hν : IsGenericCocharacter i ν` and
`hJ : J ⊆ simpleRelativeRoots i ν`. `L = Standard.leviScheme i ν J`,
`j = Standard.leviHom i ν J : L → G` (a closed subgroup representing the standard Levi functor,
`Standard.isRepresentedBy_leviHom`, `Standard.isClosedSubgroup_leviHom`), and
`iL = Standard.leviTorusHom i ν J : S → L` (with `iL ≫ j = i`). Rational points carry the
canonical topologies and Borel σ-algebras (the local instances of `RationalWeights`).
`P₀(F) = standardParabolicPoints i ν ∅`, `U₀(F) = standardUnipotentPoints i ν ∅`,
`M_J(F) = standardLeviPoints i ν J`. For `L`: `P₀^L(F) = standardParabolicPoints iL ν ∅`,
`U₀^L(F) = standardUnipotentPoints iL ν ∅`, `δ₀^L = rationalMinimalModulus iL ν`.

## Results

### Abstract transport (section `Transport`)

For topological groups `H`, `H'` with Borel σ-algebras and a topological group isomorphism
`e : H ≃ₜ* H'`, subgroups `P, K ≤ H`, `P', K' ≤ H'` with `G = P K`, `H' = P' K'` (`hPK`, `hPK'`),
characters `δ` of `P` and `δ'` of `P'`:

- `iwasawaWeight_map e hδ' hP hK hδ g`: if `δ'` is trivial on `P' ∩ K'`, `e(P) ⊆ P'`,
  `e(K) ⊆ K'` and `δ'(e p) = δ(p)`, then the Iwasawa weights satisfy `w'(e g) = w(g)`.
- `subgroupContinuousMulEquiv e hK`: for `k ∈ K ↔ e k ∈ K'`, the restriction `K ≃ₜ* K'`.
- `xi_map e hδ' hP hK hδ g`: if moreover `K`, `K'` are compact and `k ∈ K ↔ e k ∈ K'`, then
  `Ξ'(e g) = Ξ(g)` for the spherical functions `xi` of `Spherical`. The normalized Haar measure of
  `K` is carried to that of `K'` (uniqueness of the Haar probability measure,
  `Measure.isHaarMeasure_eq_of_isProbabilityMeasure`).

### The Levi scheme (section `Scheme`)

- `leviScheme_isAffineHom`, `leviScheme_locallyOfFiniteType`: `L` is affine and locally of finite
  type over `F`, as a closed subgroup of `G`.
- The existing `BruhatTits.SpecialCompact.standardLevi_isConnectedReductive hG i hi ν hν J hJ`,
  imported from `LeviApartmentComparison`, gives connected reductivity of `L`. By the proved
  `standardCocharacter` there is a standard cocharacter `ζ` for `J` with
  `standardLevi i ν J = Dynamic.centralizer (ζ ≫ i)`. So `j` represents the centralizer of `ζ ≫ i`,
  and the proved `dynamicCentralizerReductive` applies.
- `isGenericCocharacter_leviTorusHom hν`: `ν` is generic for `iL`. The relative roots of `L` are
  relative roots of `G` (`relativeRoots_subset_of_factor`).
- `standardParabolic_leviTorusHom_empty hG hi hν hJ` and
  `standardUnipotent_leviTorusHom_empty hG hi hν hJ`: the minimal standard parabolic of `L` and
  its radical are the preimages under `j` of `standardParabolic i ν ∅` and
  `standardUnipotent i ν ∅`, as subgroup functors. `ν` is a standard cocharacter for `∅` both in
  `G` and in `L` (`isStandardCocharacter_empty_self`). So `standardCocharacter`, applied to `G` and
  to `L`, identifies both sides with dynamic subgroups of `ν`. The dynamic parabolic and
  unipotent subgroups of `L` are the preimages of those of `G`
  (`Standard.leviGenericParabolic_eq_comap_standard`,
  `Dynamic.unipotent_eq_comap_of_isClosedSubgroup`).

### Rational points (section `Points`)

- `leviSchemePointsEquiv i ν J : L(F) ≃ₜ* M_J(F)`: the Library's
  `standardLeviRationalPointsHomeomorph` for `j`; its value at `x` is `j(x)`
  (`leviSchemePointsEquiv_coe`). Also `continuous_map_leviHom`, `map_leviSchemePointsEquiv_symm`,
  `map_leviHom_injective`.
- `mem_standardParabolicPoints_leviTorusHom_iff` and `mem_standardUnipotentPoints_leviTorusHom_iff`:
  `x ∈ P₀^L(F) ↔ j(x) ∈ P₀(F)` and `x ∈ U₀^L(F) ↔ j(x) ∈ U₀(F)`.
- `leviSchemeUnipotentEquiv hG hi hν hJ : U₀^L(F) ≃ₜ* M_J(F) ∩ U₀(F)`, `u ↦ j(u)`, with
  `leviSchemeUnipotentEquiv_apply_coe` and `map_leviSchemeUnipotentEquiv_symm_apply`.
- **`standardLeviMinimalModulus_leviHom hG hi hν hJ p`**: `δ₀^{M_J}(j(p)) = δ₀^L(p)` for
  `p ∈ P₀^L(F)`. Both are Haar moduli of conjugation, on `M_J(F) ∩ U₀(F)` and on `U₀^L(F)`.
  `leviSchemeUnipotentEquiv` intertwines the two conjugations, and the Haar modulus is invariant
  under such a transport (`Aubert.General.mulEquivHaarChar_trans_symm`).

### Compact subgroups and `Ξ` (section `Compact`)

- **`leviSchemeCompact K i ν J`** (definition, the recorded declaration): `K.comap j`, the
  points `x` of `L` with `j(x) ∈ K`. `mem_leviSchemeCompact_iff`: `x ∈ j⁻¹(K)` if and only if
  `j(x) ∈ K ∩ M_J(F)`.
- `compactSpace_leviSchemeCompact`, `isCompact_leviSchemeCompact` (for compact `K`) and
  `isOpen_leviSchemeCompact` (for open `K`).
- `isIwasawaPair_leviSchemeCompact hG hi hν hJ hM`: from the Iwasawa decomposition
  `hM : M_J(F) = (P₀(F) ∩ M_J(F))(K ∩ M_J(F))`, the decomposition `L(F) = P₀^L(F) j⁻¹(K)`.
- **`rationalXi_leviScheme hG hi hν hJ hKo hKc hM x`**: for compact open `K` with `hM`,
  `rationalXi (for L, j⁻¹(K)) x = rationalLeviXi hKc hM (j(x))`. That is, `Ξ` of the Levi scheme is
  `Ξ^{M_J}`. The proof is `xi_map` with `leviSchemePointsEquiv`. Its premises are the point
  comparison for `P₀`, the definition of `j⁻¹(K)`, the moduli comparison above, and the
  triviality of `δ₀^{M_J}` on `P₀(F) ∩ M_J(F) ∩ K` (`standardLeviMinimalModulusOf_eq_one`, module
  `RationalConstantTerm`).

### Heights (section `Height`)

- `isClosedSubgroup_restrict_leviHom hρ`: for a closed matrix representation `ρ` of `G`, its
  restriction `ρ ∘ j` (`ρ.restrict j`) to `L` is closed.
- **`rationalHeight_restrict_leviHom ρ x`**: `σ_{ρ ∘ j}(x) = σ_ρ(j(x))`.
- `leviSchemeCompact_le_rationalHeightSubgroup ρ hKρ`: `ρ(K) ⊆ GL_n(𝒪)` gives
  `(ρ ∘ j)(j⁻¹(K)) ⊆ GL_n(𝒪)`.

## Use

With these results, a statement for connected reductive group schemes applies to the Levi
scheme `L`, with the data `(iL, ν, j⁻¹(K), ρ ∘ j)`. Its conclusions about `Ξ` and `σ` then read as
conclusions about `Ξ^{M_J}` and `σ|_{M_J(F)}` on `M_J(F)`, through `leviSchemePointsEquiv`. The
structural premises of such a statement for `L` (for instance `SimultaneousStandardBasisAt` and
the Cartan covering for `L` at a compact open subgroup of `L(F)`) are separate. For a special
compact subgroup they are the Levi clauses of Renard V.5.1 (5), which the Library records with
the special compact subgroup of the Levi (`SpecialLeviInheritance`, `SpecialCompactLevi`).

## Scope

- Only standard Levi subgroups `M_J` of the fixed `i`, `ν` are treated.
- Representations are not transported here. The pullback along `leviSchemePointsEquiv`
  (`SmoothRep.pullback`) is available in the Library, but the comparison of temperedness,
  square integrability and coefficients is not stated here.
- The split centre, `M_J(F)¹` and Haar measures on `M_J(F)` are not compared here.
- Provenance: the definition `leviSchemeCompact` is the source's `M ∩ K` (I.1, p. 240) read on
  the Levi scheme. `rationalXi_leviScheme` is the source's convention that `Ξ^M` is `Ξ` for `M`
  (II.1, p. 252). The remaining declarations are internal glue and comparisons.

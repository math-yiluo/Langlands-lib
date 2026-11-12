# Proof: the rational Bruhat decomposition

Author: Worker 3784 (formerly Worker 24).

This module proves the published statement
`Langlands.GroupScheme.RationalBruhatStatement` of
[`Statement`](Statement.md) at an arbitrary universe `u`, as the theorem
`Langlands.GroupScheme.rationalBruhat`. The statement and its sources (Borel–Tits
5.15, Milne 25.27 with the official errata) are described in the statement's Markdown.
That Markdown explains how the double-coset form of the Lean statement relates to the
sources. The proof below follows a different route from the sources.

The proof uses no hypothesis beyond those of the statement. There is no splitness of
`G`, perfectness, characteristic, infinitude or rational-point assumption. Finite and
infinite fields are both handled, in the rational lifting step. The theorem depends only
on the axioms `propext`, `Classical.choice` and `Quot.sound`.

Notation: `k : Type u` is a field and `S = Spec k`. `G(k)` means
`Over.mk (𝟙 S) ⟶ G.X`. `i : T ⟶ G` is a maximal split torus and `ν` a cocharacter of
`T`. `P(k)` is the carrier of `Dynamic.parabolic (groupHom ν ≫ i)` over `Over.mk (𝟙 S)`.
`int(x)` is `(G.innerIso x).hom`, conjugation by the point `x`.
`exists_parabolic_conj_into_torus` is proved in the helper module
[`GenericParabolicCocharacterConjugacy`](GenericParabolicCocharacterConjugacy.md). The published
`genericMinimalParabolic` is proved in
[`GenericMinimalParabolicProof`](GenericMinimalParabolicProof.md).

## Rational lifting from `G / P`

`exists_rational_lift_of_dynamicParabolic` takes the following data:

- a connected reductive `G` and any cocharacter `χ`;
- a closed representative `iP : P ⟶ G` of `Dynamic.parabolic χ`;
- a representative `iU` of the opposite contracting subgroup
  `Dynamic.unipotent (χ⁻¹)`, where `χ⁻¹` is `groupHom (Gm.powerHom S (-1)) ≫ χ`;
- a smooth, surjective, quasi-compact morphism `q : G.X ⟶ Q` whose fibres on every test
  scheme are the cosets of `range iP` (hypothesis `hf`).

It concludes that every rational point of `Q` is `h ≫ q` for some `h ∈ G(k)`.

*Proof.* The point is transported along `rationalPointEquiv` to a `k`-valued ring point.
There are two cases.

- **`k` finite.** `P` is smooth (`dynamicSmooth`), affine (closed in an affine group) and
  connected (`DynamicConnected.connectedSpace_of_isRepresentedBy_parabolic`). The
  published `Dynamic.rational_lifts_of_finite_torsor` applies, with the published
  `finiteFieldTorsorPointStatement` (Lang's theorem for torsors).
- **`k` infinite.** The published `oppositeCellStatement` shows that multiplication
  `U(χ⁻¹) × P → G` is an open immersion. `Dynamic.flagQuotientCell` then gives an open
  subscheme of `Q` with a section to `G`. By `range_identity_subset_flagQuotientCell` it
  contains the identity coset. The published `Dynamic.rational_lifts_of_reductive_density`
  applies, with `reductiveRationalPointDensity` (density of `G(k)`).

The lift is transported back with `rationalPointEquiv_natural`. This lemma repeats the
lifting step of the published `dynamicFlagQuotientExistence`, here for an arbitrary
quotient `q`.

## Covering for arbitrary representatives

`exists_bruhat_factorization_of_represented` assumes these hypotheses:

- `G` is connected reductive and `i` is a maximal split torus;
- `Dynamic.centralizer (groupHom ν ≫ i) = torusCentralizer i`;
- `iP` is a closed representative of `Dynamic.parabolic (groupHom ν ≫ i)`;
- `iU` is a representative of the opposite contracting subgroup.

Then every `g ∈ G(k)` is `p * n * q` with `n ∈ normalizerPoints i` and `p, q ∈ P(k)`.

*Proof.*

1. **The proper quotient.** `iP` is geometrically parabolic
   (`isParabolicSubgroup_of_range_eq_dynamicParabolic`), and in particular smooth.
   `smoothSubgroupQuotientExistence` gives a quotient `q : G.X ⟶ Q` by `P` with fibres
   `hf`. `parabolicSubgroupQuotientProper` shows that `Q` is proper. `G` acts on `Q` by left
   translation: `a = Dynamic.flagQuotientSchemeAction`, with
   `a.act g (h ≫ q) = (g * h) ≫ q` (`flagQuotientSchemeAction_act_lift`).
2. **The limit of the orbit.** Restrict `a` along `ν ≫ i`. Since `Q` is proper, the
   `𝔾_m`-orbit of `g ≫ q` extends to `e` over the affine line
   (`AffineLine.exists_extension_of_isProper`). Its value `Dynamic.evalZero e` at `0` is a
   fixed point (`SchemeAction.IsGmOrbitExtension.isFixed_evalZero`).
3. **A rational lift of the limit.** The previous section gives `h₀ ∈ G(k)` with
   `h₀ ≫ q = Dynamic.evalZero e`. So `(ν ≫ i)(t) · h₀ P = h₀ P` on every test scheme.
   The published `range_conjugate_le_of_fixed_coset` turns this into
   `range ((ν ≫ i) ≫ int(h₀⁻¹)) ≤ Dynamic.parabolic (groupHom ν ≫ i)`.
4. **Conjugation into the torus.** `exists_parabolic_conj_into_torus`, applied to the
   cocharacter `(ν ≫ i) ≫ int(h₀⁻¹)`, gives `p ∈ P(k)` and `ρ : 𝔾_m ⟶ T` with
   `(ν ≫ i) ≫ int(h₀⁻¹) ≫ int(p) = ρ ≫ i`. Set `n = h₀ * p⁻¹`. By `innerIso_mul_hom`,
   `ρ ≫ i ≫ int(n) = ν ≫ i`.
5. **`n` normalizes the torus.** By `range_le_centralizer_groupHom_comp`, applied to the
   homomorphism `i ≫ int(n)` and the cocharacter `ρ`, the points of `i ≫ int(n)` lie in
   `Dynamic.centralizer (ρ ≫ i ≫ int(n)) = Dynamic.centralizer (ν ≫ i)`. By hypothesis
   this is `torusCentralizer i`. So these points commute with the points of `i`, and
   `IsMaximalSplitTorus.mem_normalizerPoints_of_commute_conjugate` gives
   `n ∈ normalizerPoints i`.
6. **`n` lies over the limit.** Since `h₀⁻¹ n = p⁻¹ ∈ P(k)`, the fibre description `hf`
   gives `Dynamic.evalZero e = n ≫ q`.
7. **The cell argument.** The published
   `Dynamic.BruhatCellLimit.exists_eq_mul_mul_of_mem_normalizerPoints` applies to the
   orbit extension `e` and the normalizing point `n` over its limit. It gives `b₁, b₂` in
   `P(k)`, the points of `P` mapped by `iP`, with `g = b₁ * n * b₂`.

## Assembly

- `exists_bruhat_factorization` specializes the previous result to the published
  representatives `Dynamic.Affine.parabolicHom` (closed by
  `Dynamic.Affine.isClosedSubgroup_parabolicHom`) and `Dynamic.Affine.unipotentHom`.
- `rationalBruhat`: given the data of `RationalBruhatStatement` with `ν` generic, the
  published `genericCentralizer` gives
  `Dynamic.centralizer (groupHom ν ≫ i) = torusCentralizer i`. The published
  `hasRationalBruhatDecomposition_of_parabolicCovering` takes this equality and the
  covering of `exists_bruhat_factorization`. It returns `HasRationalBruhatDecomposition i ν`.
  This includes the covering and the disjointness with relative-Weyl-group indexing.

## Source comparison: `P(ν)` is a minimal parabolic

Borel–Tits 5.15 and Milne 25.27 (with the official errata) are stated for a minimal
parabolic `P` and a torus that is maximal split in `P`. The statement Markdown explains that
`RationalBruhatStatement` uses `P(ν)` with `ν` generic instead, and that the identification
of `P(ν)` with such a minimal `P` is derived and not proved there. This module establishes
the identification as `rationalBruhat_parabolic_isMinimal`. Let `j` be the canonical closed
representative `Dynamic.Affine.parabolicHom (groupHom ν ≫ i)` of `P(ν)`, with `ν` generic.
The theorem proves two things:

- `IsMinimalParabolicSubgroup j`. Parabolicity of `j` comes from the published adapter
  `Dynamic.Affine.isParabolicSubgroup_parabolicHom_of_parabolicDynamic`, applied to the
  published `parabolicDynamic` (Milne 25.1). Minimality comes from
  the published `genericMinimalParabolic` of
  [`GenericMinimalParabolicProof`](GenericMinimalParabolicProof.md), whose type is the exact
  statement `GenericMinimalParabolicStatement`. Every parabolic `j'` with
  `range j' ≤ range j = P(ν)` is a rational parabolic functor below `P(ν)`, so
  `range j' = P(ν)`.
- `i` lifts to `iP : T ⟶ P` with `iP ≫ j = i` and `IsMaximalSplitTorus iP`. This is the
  published `IsMaximalSplitTorus.exists_lift_of_parabolic_le`, applied with the identity
  inclusion of `P(ν)`.

The covering and disjointness proof above does not use this theorem. It proves the
decomposition for `P(ν)` directly, and uses only two properties of `P(ν)`: it is
geometrically parabolic, so `G / P(ν)` is proper, and `genericCentralizer` holds. The
theorem identifies the `P(ν)` of the Lean statement with the minimal `P` of the sources.

## Provenance

This is internal derived content: a composition of the published results named above and
of the helper module. It makes no new source claim. Mathematically, the argument is the
dynamic-limit proof of the Bruhat covering in `G / P(ν)`. It needs no conjugacy of
minimal parabolics or of maximal split tori in `G`. Two steps take their place: the
cocharacter fixing the limit coset is conjugated into `T` inside `P(ν)`, and the
genericity of `ν` makes the conjugating point normalize `T`.

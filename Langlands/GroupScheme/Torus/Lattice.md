# Character and cocharacter lattices, `End(𝔾_m) ≅ ℤ`, split tori and tori

Worker 274.

This module builds the lattice layer of the absolute root-datum development on
the published `Langlands.GroupScheme` architecture: character and cocharacter
lattices of commutative group schemes, the identification `End(𝔾_m) ≅ ℤ`, the
character pairing, the commutative structure and the two lattices of the split
torus `𝔾_m^I`, and the predicate `IsTorus` over a field.

## Sources

Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`
(printed page = PDF page − 16):

- §12.a, printed p.230 (PDF 246): a character of `G` is a homomorphism
  `G → 𝔾_m`, characters form a commutative group `X(G)` written additively,
  `(χ + χ')(g) = χ(g) · χ'(g)`, and a cocharacter is a homomorphism `𝔾_m → G`.
- Theorem 12.9 and its proof, printed p.233 (PDF 249):
  `End(𝔾_m) = {T^i | i ∈ ℤ} ≅ ℤ`.
- Definition 12.14 and Example 12.15, printed p.236 (PDF 252): tori, split
  tori, and the identification `X(𝔾_m × 𝔾_m) ≅ ℤ × ℤ` by
  `(m₁, m₂) ↦ ((t₁, t₂) ↦ t₁^{m₁} t₂^{m₂})`.
- §21.c, printed p.428 (PDF 444): the root datum is formed from a perfect
  pairing `X × X^∨ → ℤ`; Lemma 13.51, printed p.274 (PDF 290), uses the
  pairing `⟨λ, χ⟩` of cocharacters and characters of a split torus.

Milne works with algebraic groups over a field. The definitions here over an
arbitrary base scheme (the lattices, the commutative split torus, the
coordinate characters and cocharacters, base change of characters), the
replacement of the field by an integral domain for `End(𝔾_m) ≅ ℤ`, the pairing
and the lattice equivalences, and the bridge to the Library's Cartier
characters are **derived**: they are the evident generalisations of Milne's
definitions, and Milne's field case is the special case
`k` a field, `S = Spec k`.

## Lattices over any base scheme

For `T : CommGroupScheme S` over any scheme `S`:

- `characterLattice T := T ⟶ Gm S` and `cocharacterLattice T := Gm S ⟶ T`.
  Both are reducible abbreviations of the published Hom groups of
  `CommGroupScheme S`, so their additive group structure is the published
  pointwise one, written additively as in Milne §12.a.
- `evalPoint x` is the published additive evaluation `GroupScheme.evalHom` at a
  point `x : U ⟶ T.X`. The lemmas `comp_groupHom_add`, `comp_groupHom_zero`,
  `comp_groupHom_zsmul`, `comp_groupHom_sum` and `comp_groupHom_comp` say that on
  points sums of homomorphisms act by products, integer multiples by powers,
  and composites by composites. `CommGroupScheme.hom_ext_points` is the
  published point extensionality transported to commutative group schemes.
- `CommGroupScheme.baseChangeIdIso T` is the canonical isomorphism between the
  base change of `T` along `𝟙 S` and `T`, built from `Over.pullbackId` and the
  published `Functor.mapGrpNatIso`/`Functor.mapGrpIdIso`.
- `characterLattice.cartierEquiv T : characterLattice T ≃+
  Cartier.CharacterHom T (Over.mk (𝟙 S))` precomposes with that isomorphism. It
  bridges these characters with the published Cartier characters (actual
  homomorphisms `T_{S'} → 𝔾_{m,S'}` over the test scheme `S' = S`).
- `characterLattice.baseChange b T` for any `b : S' ⟶ S` sends `χ` to
  `(CommGroupScheme.baseChange b).map χ ≫ (Gm.commBaseChangeIso b).hom`. It is
  additive because the published base-change functor of commutative group
  schemes is additive (`Langlands.AbelianScheme.RationalBaseChange`).

## `End(𝔾_m) ≅ ℤ` over a domain (Milne 12.9)

Let `k` be a commutative ring that is an integral domain (in particular any
field) and `S = Spec k`.

- `Gm.exists_eq_C_mul_T_of_isUnit`: every unit of `k[T, T⁻¹]` is `c · T^m` with
  `c ∈ kˣ`. The proof multiplies a unit and its inverse by powers of `T` to get
  polynomials whose product is `X^N`, and uses that `X` is prime in `k[X]`.
- `Gm.laurentPoint k` is the universal point of `𝔾_m` over
  `Spec k[T, T⁻¹]`, the inverse of the published `relativeLaurentIso`. Every
  point factors through it (`Gm.comp_laurentPoint`), and its unit is `T`
  (`Gm.affinePointsEquiv_laurentPoint`).
- `Gm.powerHom S : ℤ →+ (Gm S ⟶ Gm S)` sends `m` to `m • 𝟙`, which on points is
  the `m`-th power map (`Gm.comp_zsmul_id`). Over a domain it is injective,
  because `T^m ≠ 1` for `m ≠ 0`, and surjective. For surjectivity, an
  endomorphism `f` sends the universal point to a unit `c · T^m`; evaluation at
  `T = 1` gives `c = 1`, so `f` agrees with the `m`-th power map on the
  universal point and therefore on all points.
- `gmEndEquiv k : (Gm S ⟶ Gm S) ≃+ ℤ` is the inverse of the resulting
  bijection, so `(gmEndEquiv k).symm m = m • 𝟙` is the `m`-th power map
  (`gmEndEquiv_symm_apply`, `gmEndEquiv_symm_comp`). Every endomorphism is a
  power map (`eq_gmEndEquiv_zsmul`). `gmEndEquiv_comp` says that composition
  becomes multiplication, and `gmEndEquiv_id` that the identity goes to `1`.

The task allows replacing the field by a nonzero ring with connected spectrum.
An integral domain is such a ring, and every field is an integral domain.

## The pairing

`latticePairing T : characterLattice T →ₗ[ℤ] cocharacterLattice T →ₗ[ℤ] ℤ`, for
a commutative group scheme over `Spec k` with `k` a domain, is
`⟨χ, λ⟩ = gmEndEquiv k (λ ≫ χ)` (`latticePairing_apply`). Bilinearity comes from
bilinearity of composition in the preadditive category of commutative group
schemes.

## Split tori

For any base scheme `S` and finite `I : Type u`:

- `splitTorus.isCommMonObj`: the published `splitTorus S I` is commutative,
  because its points are families of units. `splitTorus.commGroupScheme S I` is
  the commutative group scheme with underlying group scheme `splitTorus S I`.
- `splitTorus.proj S I i` is the coordinate character `t ↦ tᵢ`, and
  `splitTorus.single S I i` the coordinate cocharacter `s ↦ (1, …, s, …, 1)`,
  given on points by `Pi.mulSingle` through `splitTorus.pointsEquiv`.
  `single_comp_proj` gives `single i ≫ proj j = δᵢⱼ`, and
  `sum_proj_comp_single` gives `∑ᵢ proj i ≫ single i = 𝟙`.

Over a domain `k`, with `𝕋 = splitTorus.commGroupScheme (Spec k) I`:

- `splitTorus.characterLatticeEquiv k I : characterLattice 𝕋 ≃+ (I → ℤ)` sends
  `χ` to `(gmEndEquiv k (single i ≫ χ))ᵢ`. Its inverse sends `m` to
  `∑ᶠ i, mᵢ • proj i` (`characterLatticeEquiv_symm_eq` for `Fintype I`). On
  points this character is `t ↦ ∏ tᵢ^{mᵢ}`
  (`pointsEquiv_characterLatticeEquiv_symm`).
- `splitTorus.cocharacterLatticeEquiv k I : cocharacterLattice 𝕋 ≃+ (I → ℤ)`
  sends `λ` to `(gmEndEquiv k (λ ≫ proj i))ᵢ`. Its inverse sends `m` to
  `∑ᶠ i, mᵢ • single i`. On points this cocharacter is `s ↦ (s^{mᵢ})ᵢ`
  (`pointsEquiv_cocharacterLatticeEquiv_symm`).
- `latticePairing_eq_sum` and `latticePairing_symm_symm`: under these
  equivalences the pairing is the dot product `∑ᵢ mᵢ nᵢ`.
- `isPerfPair_latticePairing`: the pairing is perfect, as Mathlib
  `LinearMap.IsPerfPair`. This follows from `LinearMap.IsPerfPair.congr` and
  the perfect dot-product pairing `dotProductEquiv ℤ I`.

The inverses use `finsum`, so the definitions need only `Finite I`. The
lemmas giving finite-sum or finite-product formulas assume `Fintype I`.

## Tori over a field (Milne 12.14)

For a field `k`, `IsTorus T` for `T : GroupScheme (Spec k)` says that there are a
field `K : Type u` and an algebra structure `Algebra k K` such that the base
change of `T` along `Spec K ⟶ Spec k`, the published `GroupScheme.baseChange`
along `Spec.map (algebraMap k K)`, satisfies the published `IsSplitTorus`. This
is Milne's Definition 12.14 ("becomes isomorphic to a finite product of copies
of `𝔾_m` over some field containing `k`"). `IsSplitTorus.isTorus` shows that
split tori are tori, taking `K = k`.

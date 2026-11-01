# Surjectivity of the hyperext edge map

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.HyperextAbutmentFiltration` (`edgeMap_comp`; Worker 61),
`Langlands.Cohomology.HyperextSecondPage` (`isoSingleHomology`,
`heartPieceIso`, `secondPageExtAddEquiv`; Worker 61) and
`Langlands.Cohomology.HyperextDegeneration.Statement` (`edgeMap`,
`HyperextDegenerationStatement`; Worker 3), and on Mathlib's canonical
t-structure on derived categories, its truncation triangles, the long exact
cohomology sequences of distinguished triangles, and `Ext` groups.

Let `C` be an abelian category, `K` an object of its derived category and
`W` an object of `C`. Write `W₀` for `W` placed in degree `0`, and `H^i` for
the cohomology functor in degree `i`. The edge map
`HyperextDegeneration.edgeMap K W n : Hom(K, W₀⟦n⟧) → Hom(H^{-n} K, W)`
sends a morphism to the morphism it induces on `H^{-n}`.
`HyperextDegenerationStatement` asserts that the edge map is bijective when
`K` has cohomology bounded above and `Ext^i(H^k K, W) = 0` for every `k` and
every `i > 0`.

This module proves that under these hypotheses the edge map is
**surjective** (`edgeMap_surjective_of_ext`). Injectivity under the same
hypotheses is `edgeMap_injective_of_ext` of the module
`Langlands.Cohomology.HyperextGradedVanishing` (candidate c91ec78b, not
imported here). This module does not import it, does not state the
bijectivity, and does not prove `HyperextDegenerationStatement`. The
combination is left to a separate proof of that statement.

## Conventions

The section takes an abelian category `C` with objects in `Type u` and
morphisms in `Type v` and an instance `HasDerivedCategory.{w} C`. The last
two declarations also take `HasExt.{w'} C`, and `Abelian.Ext.{w'} M W i`
is Mathlib's `Ext` group in the universe `w'`. `X.IsLE m` and `X.IsGE m`
refer to the canonical t-structure `DerivedCategory.TStructure.t`: by
Mathlib's `isLE_iff` and `isGE_iff`, `H^i X = 0` for all `i > m`,
respectively for all `i < m`. `τ_{< k}` and `τ_{≥ k}` are the truncation
functors `TStructure.t.truncLT k` and `TStructure.t.truncGE k`, with maps
`τ_{< k} X ⟶ X` (`truncLTι`) and `X ⟶ τ_{≥ k} X` (`truncGEπ`).
`(singleFunctor C j).obj M` is the object `M` of `C` placed in degree `j`.

## Declarations

| Declaration | Statement |
| --- | --- |
| `eq_zero_of_iso_of_forall_eq_zero e h g` | In any category with zero morphisms: if `e : A ≅ A'` and every morphism `A' ⟶ Y` is zero (`h`), then `g : A ⟶ Y` is zero. |
| `isIso_homologyMap_truncLTι X hj` | For `j < k`, `H^j` of `τ_{< k} X ⟶ X` is an isomorphism. |
| `isIso_homologyMap_truncGEπ X hj` | For `k ≤ j`, `H^j` of `X ⟶ τ_{≥ k} X` is an isomorphism. |
| `homologyFunctor_map_surjective_of_isGE_of_isLE m u` | If `X` and `Y` both lie in degrees `≥ m` and `≤ m`, every morphism `u : H^m X ⟶ H^m Y` is `H^m(g)` for some `g : X ⟶ Y`. |
| `edgeTargetIso W n` | The isomorphism `H^{-n}(W₀⟦n⟧) ≅ W`: Mathlib's shift isomorphism `(homologyFunctor C 0).shiftIso n (-n) 0` at `W₀`, followed by `singleFunctorCompHomologyFunctorIso C 0` at `W`. A `def`. |
| `edgeMap_eq_comp K W n f` | `edgeMap K W n f = H^{-n}(f) ≫ (edgeTargetIso W n).hom`. |
| `edgeMap_surjective_of_isGE_of_isLE X W n` | If `X` lies in degrees `≥ -n` and `≤ -n`, then `edgeMap X W n` is surjective. |
| `eq_zero_of_isGE_of_isLE_self m hY f` | If `X` lies in degrees `≥ m` and `≤ m`, and every morphism from `(singleFunctor C m).obj (H^m X)` to `Y` is zero (`hY`), then every `f : X ⟶ Y` is zero. |
| `eq_zero_of_isGE_of_isLE Y a k` | For `a : ℤ` and `k : ℕ`: for every `X` lying in degrees `≥ a` and `≤ a + k`, if every morphism from `(singleFunctor C j).obj (H^j X)` to `Y` is zero for all `j` with `a ≤ j ≤ a + k`, then every morphism `X ⟶ Y` is zero. |
| `singleFunctor_hom_eq_zero_of_ext K W j d p hp h g` | For `j d : ℤ` and `p : ℕ` with `p = j + d` (`hp`): if `Abelian.Ext.{w'} (H^j K) W p` has at most one element (`h`), then every `g : (singleFunctor C j).obj (H^j K) ⟶ W₀⟦d⟧` is zero. |
| `edgeMap_surjective_of_ext K b hK W hW n` | If `H^i K = 0` for all `i > b` (`hK`) and `Abelian.Ext.{w'} (H^k K) W i` has at most one element for every `k : ℤ` and every `i : ℕ` with `0 < i` (`hW`), then `HyperextDegeneration.edgeMap K W n` is surjective, for every `n : ℤ`. |

The hypotheses `hK` and `hW` of `edgeMap_surjective_of_ext` are exactly
those of `HyperextDegenerationStatement`. The Ext hypothesis is used only
for `i ≥ 2`.

## Proofs

- `eq_zero_of_iso_of_forall_eq_zero`: `g = e.hom ≫ (e.inv ≫ g)` and
  `e.inv ≫ g = 0`.
- `isIso_homologyMap_truncLTι`: in the truncation triangle
  `τ_{< k} X ⟶ X ⟶ τ_{≥ k} X ⟶ (τ_{< k} X)⟦1⟧`, the third object lies in
  degrees `≥ k`, so its `H^j` and `H^{j-1}` vanish for `j < k`. By the long
  exact cohomology sequence (Mathlib's
  `homologySequence_mono_shift_map_mor₁_iff` and
  `homologySequence_epi_shift_map_mor₁_iff`), `H^j` of the first morphism is
  a monomorphism and an epimorphism, hence an isomorphism.
- `isIso_homologyMap_truncGEπ`: the same with the first object, which lies
  in degrees `≤ k - 1`, so its `H^j` and `H^{j+1}` vanish for `k ≤ j`
  (`homologySequence_mono_shift_map_mor₂_iff`,
  `homologySequence_epi_shift_map_mor₂_iff`).
- `homologyFunctor_map_surjective_of_isGE_of_isLE`: by Mathlib's
  `exists_iso_singleFunctor_obj_of_isGE_of_isLE`, `X ≅ (singleFunctor C m).obj A`
  and `Y ≅ (singleFunctor C m).obj B` for some `A` and `B`. The composite
  `singleFunctor C m ⋙ H^m` is isomorphic to the identity functor
  (`singleFunctorCompHomologyFunctorIso`), hence full
  (`Functor.Full.of_iso`). So the morphism
  `H^m((singleFunctor C m).obj A) ⟶ H^m((singleFunctor C m).obj B)` obtained
  from `u` by conjugating with `H^m` of these isomorphisms is the image of
  some `a : A ⟶ B`.
  Conjugating `(singleFunctor C m).map a` back gives `g`.
- `edgeMap_eq_comp`: unfolding `edgeMap` and Mathlib's `Functor.shiftMap`,
  this is associativity of composition.
- `edgeMap_surjective_of_isGE_of_isLE`: `W₀⟦n⟧` lies in degrees `≥ -n` and
  `≤ -n` (`isGE_shift`, `isLE_shift`). Given `g : H^{-n} X ⟶ W`, the
  previous fullness lemma gives `h : X ⟶ W₀⟦n⟧` with
  `H^{-n}(h) = g ≫ (edgeTargetIso W n).inv`, and then
  `edgeMap X W n h = g` by `edgeMap_eq_comp`.
- `eq_zero_of_isGE_of_isLE_self`: precompose with the Library isomorphism
  `isoSingleHomology X m : X ≅ (singleFunctor C m).obj (H^m X)` and apply
  `eq_zero_of_iso_of_forall_eq_zero`.
- `eq_zero_of_isGE_of_isLE`: by induction on `k`, for all `X` at once. For
  `k = 0` this is the previous lemma. For `k + 1`, put `m = a + k + 1` and
  use the truncation triangle `τ_{< m} X ⟶ X ⟶ τ_{≥ m} X ⟶ (τ_{< m} X)⟦1⟧`.
  The object `τ_{< m} X` lies in degrees `≥ a` and `≤ a + k` (Mathlib's
  instances for triangulated categories), and for `a ≤ j ≤ a + k` its
  `H^j` is identified with `H^j X` by `isIso_homologyMap_truncLTι`; so the
  induction hypothesis gives `(τ_{< m} X ⟶ X) ≫ f = 0`. By exactness of
  `Hom(-, Y)` on the triangle (`Triangle.yoneda_exact₂`), `f` factors through
  `X ⟶ τ_{≥ m} X` by some `f'`. The object `τ_{≥ m} X` lies in degrees
  `≥ m` and `≤ m`, and its `H^m` is identified with `H^m X` by
  `isIso_homologyMap_truncGEπ`; so `f' = 0` by the previous lemma and
  `f = 0`.
- `singleFunctor_hom_eq_zero_of_ext`: the Library equivalence
  `secondPageExtAddEquiv K W p (-j)` identifies
  `Hom(heartPiece TStructure.t K (-j), W₀⟦p + -j⟧)` with
  `Abelian.Ext (H^{-(-j)} K) W p`, which has at most one element by `h`.
  The Library isomorphism `heartPieceIso K (-j)` identifies
  `heartPiece TStructure.t K (-j)` with `(singleFunctor C (-(-j))).obj (H^{-(-j)} K)`.
  So every morphism from the latter to `W₀⟦p + -j⟧` is zero. Rewriting
  `-(-j)` as `j` and `p + -j` as `d` gives the claim.
- `edgeMap_surjective_of_ext`: `hK` gives `K.IsLE b`. Write
  `K₁ = τ_{≥ -n} K`, `Z = τ_{< 1 - n} K₁` and `X = τ_{≥ 1 - n} K₁`, so that
  `Z ⟶ K₁ ⟶ X ⟶ Z⟦1⟧` is a truncation triangle `T`. The object `Z` lies
  in degrees `≥ -n` and `≤ -n`, and `X` lies in degrees `≥ 1 - n` and
  `≤ b`. Given `g : H^{-n} K ⟶ W`, let
  `g₁ = H^{-n}(K ⟶ K₁)⁻¹ ≫ g : H^{-n} K₁ ⟶ W`
  (an isomorphism by `isIso_homologyMap_truncGEπ`). By
  `edgeMap_surjective_of_isGE_of_isLE` there is `h₀ : Z ⟶ W₀⟦n⟧` with
  `edgeMap Z W n h₀ = H^{-n}(Z ⟶ K₁) ≫ g₁`.
  - The obstruction `T.mor₃ ≫ h₀⟦1⟧' : X ⟶ W₀⟦n⟧⟦1⟧` vanishes. After
    composing with the isomorphism `W₀⟦n⟧⟦1⟧ ≅ W₀⟦n + 1⟧`
    (`shiftFunctorAdd'`), apply `eq_zero_of_isGE_of_isLE` with `a = 1 - n`
    and `k = (b - (1 - n)).toNat`. For `j ≥ 1 - n`, `H^j X` is identified
    with `H^j K` through `H^j(K₁ ⟶ X)` and `H^j(K ⟶ K₁)`
    (`isIso_homologyMap_truncGEπ` twice), and every morphism from
    `(singleFunctor C j).obj (H^j K)` to `W₀⟦n + 1⟧` is zero by
    `singleFunctor_hom_eq_zero_of_ext` with
    `p = (j + n + 1).toNat = j + n + 1 ≥ 2`, using `hW`.
  - Hence `h₀` extends to `K₁`: by exactness of `Hom(-, W₀⟦n⟧⟦1⟧)` on the
    rotated triangle (`Triangle.yoneda_exact₃` applied to
    `rot_of_distTriang`), `h₀⟦1⟧' = (-T.mor₁⟦1⟧') ≫ g'` for some `g'`. Since
    the shift functor is full, `g' = f₁⟦1⟧'` for some `f₁ : K₁ ⟶ W₀⟦n⟧`, and
    since it is faithful, `h₀ = T.mor₁ ≫ (-f₁)`.
  - By `edgeMap_comp`, `H^{-n}(Z ⟶ K₁) ≫ edgeMap K₁ W n (-f₁) = edgeMap Z W n h₀`,
    and `H^{-n}(Z ⟶ K₁)` is an isomorphism (`isIso_homologyMap_truncLTι`, since
    `-n < 1 - n`). So `edgeMap K₁ W n (-f₁) = g₁`. Finally, again by
    `edgeMap_comp`, the edge map sends `(K ⟶ K₁) ≫ (-f₁)` to
    `H^{-n}(K ⟶ K₁) ≫ g₁ = g`.

## Provenance and interpretation

The statements and proofs are ours, assembled from Mathlib and the Library.
Classically, the degeneration of the hyperext spectral sequence
`E_2^{p,q} = Ext^p(H^{-q} K, W) ⇒ Hom(K, W₀⟦p + q⟧)` when the higher `Ext`
groups vanish gives the bijectivity of the edge map. The surjectivity
proved here corresponds to the vanishing of the differentials leaving
`E_r^{0, n}`. Their targets are `E_r^{r, n - r + 1}`, subquotients of
`Ext^r(H^{r - n - 1} K, W) = 0` for `r ≥ 2`. Here the argument is carried out
directly with truncation triangles and a dévissage over the cohomology
objects of `τ_{≥ 1 - n} τ_{≥ -n} K`, without the spectral sequence. The
scope of the unit (surjectivity in a definition module, the statement
`HyperextDegenerationStatement` unchanged, its proof left to a separate
focused proof task) follows the plan agreed with Worker 13.

For this module Worker 61 reread the following passages of Harris 1999 in
the text layer of the PDF:

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39-2 (1999), 299-318 (source
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`),
  Proposition 4.10, printed p.311 (one-based PDF page 13): "There is a
  spectral sequence of `𝒪`-modules
  (4.10.1) `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̌_N, L_ℓ(n-1)), 𝒜_ℓ(GJ, ρ, H)) ⇒ H^{i+j}(S̄_{K(N)}, W̃)`.
  Here `Ext^i` denotes the `i`-th derived functor of `Hom` in the category of
  smooth `L_ℓ[GJ]`-modules."
- The same article, §5, printed p.312 (one-based PDF page 14): "since `π_v`
  is supercuspidal, the higher Ext's vanish and the spectral sequence
  (4.10.1) degenerates to an isomorphism" (5.2).

Interpretation (explanation only). In the generic setting of this
framework, the isomorphism (5.2) corresponds to the bijectivity of the edge
map `Hom(K, W₀⟦n⟧) → Hom(H^{-n} K, W)` under the vanishing of the higher
`Ext` groups. This module supplies its surjective half. In Harris's
situation `C` would be a category of smooth representations and `K` an
object of its derived category whose cohomology is the compactly supported
cohomology of the Drinfeld tower, shifted and Tate twisted. None of this is
formalized here.

## Scope

- `HyperextDegenerationStatement` is not proved here, and bijectivity is not
  stated. Injectivity is in `Langlands.Cohomology.HyperextGradedVanishing`,
  which this module does not import.
- The spectral sequence `hyperextSpectralSequence` is not used, and nothing
  about its differentials or convergence is proved.
- Boundedness above of `K` is the explicit hypothesis `hK`. The dévissage
  `eq_zero_of_isGE_of_isLE` needs objects bounded on both sides; `K` itself
  need not be bounded below, because the dévissage is applied only to
  `τ_{≥ 1 - n} τ_{≥ -n} K`.
- All maps are set-theoretic or additive. No linearity over a coefficient
  ring, equivariance or naturality is stated.
- `HasDerivedCategory.{w} C` and `HasExt.{w'} C` are hypotheses; the results
  hold for each such instance.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
pp.311-312 reread in the text layer of the PDF for the module
`Langlands.Cohomology.HyperextGradedVanishing` in the same session.

Dependencies: `Langlands.Cohomology.HyperextAbutmentFiltration` and
`Langlands.Cohomology.HyperextSecondPage`, with Mathlib pinned to Lean 4.34.0
and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

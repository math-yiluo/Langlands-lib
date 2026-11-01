# The abutment filtration of the hyperext spectral sequence

Author: Worker 61. Built on the Library module
`Langlands.Cohomology.HyperextDegeneration.Statement` (`edgeMap`, Worker 3)
and on Mathlib's t-structures (`Triangulated.TStructure`, its truncation
functors and triangles) and its canonical t-structure on derived categories
(`DerivedCategory.TStructure.t`).

Let `t` be a t-structure on a pretriangulated category `C`, and let `K` and
`B` be objects of `C`. The Library module
`Langlands.Cohomology.HyperextSpectralSequence` builds a spectral sequence
by applying `Hom(-, B)` to the truncations of `K`; its intended abutment in
total degree `n` is `Hom(K, B⟦n⟧)`. This module defines the matching
filtration of `Hom(K, B⟦n⟧)` by truncations of `K`, together with its graded
pieces. In the derived category of an abelian category, with `B` an object
`W` placed in degree `0`, it relates the first two steps of the filtration
to the edge map of `HyperextDegenerationStatement`: `F^1` is the kernel of
the edge map, and `gr^0` is isomorphic to the image of the edge map.

This module does **not** prove `HyperextDegenerationStatement`. It assumes
nothing about `Ext` groups. It does not show that the graded pieces `gr^p`
with `p > 0` vanish, and it does not show that the edge map is surjective.
It does not import `Langlands.Cohomology.HyperextSpectralSequence`, does not
compare `graded` with the pages of that spectral sequence, and proves no
convergence.

## Indexing

Mathlib's t-structures use cohomological conventions: `t.IsLE X a` and
`t.IsGE X a` say that `X` lies in degrees `≤ a` and `≥ a`, `τ_{< a}` and
`τ_{≥ a}` are the truncation functors `t.truncLT a` and `t.truncGE a`, and
`τ_{< a} K ⟶ K ⟶ τ_{≥ a} K ⟶ (τ_{< a} K)⟦1⟧` is the distinguished triangle
`t.triangleLTGE a K`.

- `F^p` uses the truncation at `p - n`: a morphism `f : K ⟶ B⟦n⟧` lies in
  `F^p` when it factors through `K ⟶ τ_{≥ p - n} K`, equivalently when it
  vanishes on `τ_{< p - n} K`.
- So `gr^p = F^p / F^{p+1}` compares vanishing on `τ_{< p - n} K` with
  vanishing on `τ_{< p - n + 1} K`, and only the cohomology of `K` in degree
  `p - n` enters. This is the classical indexing for which `gr^p`
  corresponds to the term `E_∞^{p, n - p}` of the hyperext spectral
  sequence, whose page-2 term `E_2^{p, n - p}` is `Ext^p(H^{p - n} K, B)`.
  Indeed `secondPageIso` of `HyperextSpectralSequence` puts
  `Hom(heartPiece t K q, B⟦p + q⟧)` in position `(p, q)`, where
  `heartPiece t K q` lies in the heart shifted to degree `-q`; for
  `q = n - p` that degree is `p - n`. This correspondence is the motivation
  of the indexing; it is not formalized.
- In particular `gr^0` involves `H^{-n} K`, the source of the edge map
  `Hom(K, W₀⟦n⟧) → Hom(H^{-n} K, W)`.

## Any t-structure

Section `TStructure` takes a category `C` with objects in `Type u` and
morphisms in `Type v`, preadditive, with a zero object, a shift by `ℤ` by
additive functors, and pretriangulated; `t : TStructure C`. No
`IsTriangulated C` is needed. `ShiftedHom K B n` is Mathlib's type of
morphisms `K ⟶ B⟦n⟧`, an additive group.

| Declaration | Statement |
| --- | --- |
| `filtration t K B n p` | The additive subgroup `F^p` of `ShiftedHom K B n`: the range of precomposition with `(t.truncGEπ (p - n)).app K : K ⟶ τ_{≥ p - n} K`, that is, the morphisms of the form `(t.truncGEπ (p - n)).app K ≫ g` with `g : τ_{≥ p - n} K ⟶ B⟦n⟧`. |
| `mem_filtration_iff f` | `f ∈ filtration t K B n p` if and only if there is `g` with `(t.truncGEπ (p - n)).app K ≫ g = f` (by definition). |
| `mem_filtration_iff_truncLTι_comp_eq_zero f` | `f ∈ filtration t K B n p` if and only if `(t.truncLTι (p - n)).app K ≫ f = 0`, where `(t.truncLTι (p - n)).app K : τ_{< p - n} K ⟶ K`. |
| `filtration_le_of_le hpq` | For `p ≤ q`: `filtration t K B n q ≤ filtration t K B n p`. |
| `antitone_filtration K B n` | `p ↦ filtration t K B n p` is antitone (the filtration is decreasing). |
| `filtration_eq_top hp` | If `t.IsGE B 0` and `p ≤ 0`, then `filtration t K B n p = ⊤`. |
| `filtration_eq_bot b hp` | If `t.IsLE K b` and `b < p - n`, then `filtration t K B n p = ⊥`. |
| `graded t K B n p` | The quotient group `F^p / F^{p+1}`: the quotient of `filtration t K B n p` by `filtration t K B n (p + 1)` viewed inside it (`AddSubgroup.addSubgroupOf`). An `abbrev`. |
| `subsingleton_graded_of_le h` | If `filtration t K B n p ≤ filtration t K B n (p + 1)`, then `graded t K B n p` has at most one element. |
| `subsingleton_graded_of_lt_zero hp` | If `t.IsGE B 0` and `p < 0`, then `graded t K B n p` has at most one element. |
| `subsingleton_graded_of_isLE b hp` | If `t.IsLE K b` and `b < p - n`, then `graded t K B n p` has at most one element. |

So for `B` in degrees `≥ 0` and `K` in degrees `≤ b`, the filtration is
`F^0 = Hom(K, B⟦n⟧) ⊇ F^1 ⊇ ... ⊇ F^{b + n + 1} = 0`, and only the graded
pieces `gr^p` with `0 ≤ p ≤ b + n` can be nonzero. If `b + n < 0`, it follows
that `Hom(K, B⟦n⟧) = F^0 = 0`; this consequence is not stated as a separate
lemma.

Proofs.

- `mem_filtration_iff_truncLTι_comp_eq_zero`: if `f = π ≫ g`, then
  `ι ≫ f = 0` by Mathlib's `truncLTι_comp_truncGEπ_app`. Conversely, if
  `ι ≫ f = 0`, then `f` factors through `π` because `Hom(-, B⟦n⟧)` is
  exact on the distinguished triangle `t.triangleLTGE_distinguished (p - n) K`
  (Mathlib's `Triangle.yoneda_exact₂`).
- `filtration_le_of_le`: by the previous lemma, using that
  `τ_{< p - n} K ⟶ K` factors through `τ_{< q - n} K ⟶ K`
  (`natTransTruncLTOfLE_ι_app`).
- `filtration_eq_top`: `B⟦n⟧` lies in degrees `≥ -n` (`isGE_shift`) and
  `τ_{< p - n} K` in degrees `≤ p - n - 1 < -n`, so every morphism between
  them is zero (the orthogonality axiom `t.zero`).
- `filtration_eq_bot`: `K` lies in degrees `≤ p - n - 1`, so
  `τ_{≥ p - n} K` is zero (`isZero_truncGE_obj_of_isLE`) and every
  `π ≫ g` vanishes.
- The `subsingleton_graded` lemmas: if `F^p ≤ F^{p+1}`, the subgroup by which
  `graded` is a quotient is everything (`AddSubgroup.addSubgroupOf_eq_top`),
  and a quotient by the whole group is trivial. The other two lemmas obtain
  `F^p ≤ F^{p+1}` from `filtration_eq_top` and `filtration_eq_bot`.

## Derived categories and the edge map

Section `Derived` takes an abelian category `C` with objects in `Type u` and
morphisms in `Type v`, and an instance `HasDerivedCategory.{w} C`. In
`DerivedCategory C`, `K.IsLE m` and `K.IsGE m` refer to the canonical
t-structure `DerivedCategory.TStructure.t`; by Mathlib's `isLE_iff` and
`isGE_iff` they say that `H^i K = 0` for all `i > m`, respectively all
`i < m`, where `H^i` is `DerivedCategory.homologyFunctor C i`. `W₀` denotes
`(DerivedCategory.singleFunctor C 0).obj W`, the object `W` placed in degree
`0`. `edgeMap K W n : Hom(K, W₀⟦n⟧) → Hom(H^{-n} K, W)` is
`HyperextDegeneration.edgeMap` of
`Langlands.Cohomology.HyperextDegeneration.Statement`: it applies `H^{-n}`,
using the shift compatibilities of the cohomology functors, and identifies
`H^0(W₀)` with `W` by Mathlib's `singleFunctorCompHomologyFunctorIso`.

| Declaration | Statement |
| --- | --- |
| `derivedFiltration K W n p` | `filtration DerivedCategory.TStructure.t K W₀ n p`, an additive subgroup of `ShiftedHom K W₀ n`. An `abbrev`. |
| `derivedFiltration_eq_top K W hp` | For `p ≤ 0`: `derivedFiltration K W n p = ⊤`. |
| `derivedFiltration_eq_bot K b hK W hp` | If `H^i K = 0` for all `i > b` (hypothesis `hK`) and `b < p - n`, then `derivedFiltration K W n p = ⊥`. |
| `edgeMap_comp φ W n f` | For `φ : X ⟶ K` and `f : ShiftedHom K W₀ n`: `edgeMap X W n (φ ≫ f) = H^{-n}(φ) ≫ edgeMap K W n f`. |
| `edgeMap_eq_zero_iff K W n f` | `edgeMap K W n f = 0` if and only if `H^{-n}(f) = 0`, where `f` is read as a morphism `K ⟶ W₀⟦n⟧`. |
| `edgeMapAddMonoidHom K W n` | The edge map as a morphism of additive groups `ShiftedHom K W₀ n →+ (H^{-n} K ⟶ W)`. |
| `edgeMapAddMonoidHom_apply` | Its value at `f` is `edgeMap K W n f` (a `simp` lemma, by definition). |
| `eq_zero_of_homologyFunctor_map_eq_zero_of_isGE_of_isLE m g hg` | If `X` and `Y` both lie in degrees `≥ m` and `≤ m`, and `g : X ⟶ Y` satisfies `H^m(g) = 0`, then `g = 0`. |
| `eq_zero_of_homologyFunctor_map_eq_zero m g hg` | If `X` lies in degrees `≤ m`, `Y` lies in degrees `≥ m`, and `g : X ⟶ Y` satisfies `H^m(g) = 0`, then `g = 0`. |
| `edgeMap_injective_of_isLE K W n` | If `K` lies in degrees `≤ -n`, then `edgeMap K W n` is injective. |
| `mem_derivedFiltration_one_iff K W n f` | `f ∈ derivedFiltration K W n 1` if and only if `edgeMap K W n f = 0`. |
| `derivedFiltration_one_eq_ker K W n` | `derivedFiltration K W n 1` is the kernel of `edgeMapAddMonoidHom K W n`. |
| `edgeMapRangeRestrict K W n` | The morphism of additive groups from `derivedFiltration K W n 0` to the range of `edgeMapAddMonoidHom K W n` given by the edge map. |
| `edgeMapRangeRestrict_surjective K W n` | `edgeMapRangeRestrict K W n` is surjective. |
| `addSubgroupOf_derivedFiltration_one_eq_ker K W n` | `derivedFiltration K W n 1`, viewed inside `derivedFiltration K W n 0`, is the kernel of `edgeMapRangeRestrict K W n`. |
| `gradedZeroAddEquivRange K W n` | An additive isomorphism from `graded DerivedCategory.TStructure.t K W₀ n 0`, that is `F^0 / F^1`, to the range of `edgeMapAddMonoidHom K W n`, induced by the edge map. |

In words: the first step `F^1` of the abutment filtration is the kernel of
the edge map, and the edge map induces an isomorphism from `gr^0` onto its
image in `Hom(H^{-n} K, W)`. **The edge map need not be surjective**, so
`gr^0` is in general only a subgroup of `Hom(H^{-n} K, W)`. Classically,
`Hom(H^{-n} K, W)` is the term `E_2^{0, n}`, and the differentials leaving
`E_r^{0, n}` cut it down to `E_∞^{0, n}`, which corresponds to `gr^0`; this
is not formalized. Surjectivity
of the edge map, together with the vanishing of `F^1`, is what
`HyperextDegenerationStatement` asserts under its `Ext` hypothesis; neither
is proved here.

The hypothesis `K.IsLE (-n)` of `edgeMap_injective_of_isLE` is used through
`eq_zero_of_homologyFunctor_map_eq_zero`: then `K` lies in degrees `≤ -n`
and `W₀⟦n⟧` in degrees `≥ -n`. Without it the edge map need not be
injective; its kernel is `F^1`.

Proofs.

- `derivedFiltration_eq_top` is `filtration_eq_top`, using Mathlib's instance
  that `W₀` lies in degrees `≥ 0`. `derivedFiltration_eq_bot` converts `hK`
  into `K.IsLE b` by Mathlib's `isLE_iff` and applies `filtration_eq_bot`.
- `edgeMap_comp`: Mathlib's `Functor.shiftMap_comp'` and associativity.
- `edgeMap_eq_zero_iff`: the edge map is `H^{-n}(f)` followed by two
  isomorphisms (the shift isomorphism `(homologyFunctor C 0).shiftIso n (-n) 0`
  at `W₀` and `(singleFunctorCompHomologyFunctorIso C 0).hom.app W`), and
  composing with an isomorphism does not change vanishing
  (`Preadditive.IsIso.comp_right_eq_zero`).
- `edgeMapAddMonoidHom`: `shiftMap`, the functor `H^0` and composition are
  additive.
- `eq_zero_of_homologyFunctor_map_eq_zero_of_isGE_of_isLE`: by Mathlib's
  `exists_iso_singleFunctor_obj_of_isGE_of_isLE`, `X` and `Y` are isomorphic
  to objects `A` and `B` of `C` placed in degree `m`. The functor
  `singleFunctor C m` is full, so `g` corresponds to a morphism `u : A ⟶ B`.
  The composite `singleFunctor C m ⋙ H^m` is isomorphic to the identity
  functor (`singleFunctorCompHomologyFunctorIso`), hence faithful, and the
  image of `u` under it is zero because `H^m(g) = 0`. So `u = 0` and `g = 0`.
- `eq_zero_of_homologyFunctor_map_eq_zero`: `g` factors as
  `X ⟶ τ_{≥ m} X ⟶ τ_{< m + 1} Y ⟶ Y` (Mathlib's `descTruncGE` and
  `liftTruncLT`), and the middle morphism `g₂` goes between objects
  concentrated in degree `m`. By the long exact cohomology sequences of the
  truncation triangles (Mathlib's `HomologySequence.epi_homologyMap_mor₂_iff`
  and `mono_homologyMap_mor₁_iff`), `H^m(X ⟶ τ_{≥ m} X)` is an epimorphism
  and `H^m(τ_{< m + 1} Y ⟶ Y)` is a monomorphism: the connecting morphisms
  that would obstruct this vanish because `H^{m+1}(τ_{< m} X) = 0` (it lies
  in degrees `≤ m - 1`) and `H^{m-1}(τ_{≥ m + 1} Y) = 0` (it lies in degrees
  `≥ m + 1`). Cancelling them, `H^m(g₂) = 0`, and the previous lemma gives
  `g₂ = 0`.
- `edgeMap_injective_of_isLE`: `W₀⟦n⟧` lies in degrees `≥ -n`
  (`isGE_shift`). If `edgeMap K W n f = 0`, then `H^{-n}(f) = 0` by
  `edgeMap_eq_zero_iff`, and `f = 0` by the previous lemma; this suffices
  because the edge map is additive.
- `mem_derivedFiltration_one_iff`: if `f = π ≫ g` with
  `π : K ⟶ τ_{≥ 1 - n} K`, then `edgeMap_comp` writes `edgeMap K W n f` as
  `H^{-n}(π) ≫ edgeMap _ W n g`, and `H^{-n}(τ_{≥ 1 - n} K) = 0`. Conversely,
  if `edgeMap K W n f = 0`, write `ι : τ_{< 1 - n} K ⟶ K`; then
  `edgeMap _ W n (ι ≫ f) = H^{-n}(ι) ≫ edgeMap K W n f = 0` by
  `edgeMap_comp`. Since `τ_{< 1 - n} K` lies in degrees `≤ -n`,
  `edgeMap_injective_of_isLE` gives `ι ≫ f = 0`, so `f ∈ F^1` by
  `mem_filtration_iff_truncLTι_comp_eq_zero`.
- `derivedFiltration_one_eq_ker` restates the previous lemma.
- `edgeMapRangeRestrict_surjective`: every element of the range is
  `edgeMap K W n f` for some `f`, and `f ∈ F^0` because
  `F^0 = ⊤` (`derivedFiltration_eq_top`).
- `addSubgroupOf_derivedFiltration_one_eq_ker`: unfold
  `AddSubgroup.mem_addSubgroupOf` and use `mem_derivedFiltration_one_iff`;
  an element of the range is zero exactly when its underlying morphism is.
- `gradedZeroAddEquivRange`: Mathlib's `QuotientAddGroup.quotientAddEquivOfEq`
  rewrites the subgroup by which `gr^0` is a quotient as the kernel of
  `edgeMapRangeRestrict K W n` (previous lemma), and
  `QuotientAddGroup.quotientKerEquivOfSurjective` (first isomorphism
  theorem) identifies the quotient by this kernel with the range.

## Provenance and interpretation

The definitions and statements are ours, assembled from Mathlib. Mathlib has
no abutment filtration or convergence theory for its spectral sequences of
spectral objects, and the Library's `HyperextSpectralSequence` describes only
the second page and the term `Hom(K, B⟦n⟧)` of the abutment. The filtration
by truncations of the source is the standard filtration on the abutment of
the hypercohomology spectral sequence of `RHom(-, B)`; its indexing is
explained in the section "Indexing" above. The boundary of this module
(the filtration and the identifications of `F^1` and `gr^0`, but no
degeneration) and its indexing were discussed beforehand with Worker 3
(author of `HyperextDegenerationStatement`) and Worker 13.

For this module Worker 61 read the following passages of Harris 1999 in the
PDF:

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

Classically, the abutment `H^{i+j}(S̄_{K(N)}, W̃)` of (4.10.1) carries the
filtration of the spectral sequence, and the degeneration (5.2) means that
the terms `E_2^{i,j}` with `i > 0` vanish, so that this filtration has a
single nonzero graded piece, identified by the edge homomorphism with
`E_2^{0, j}`. In the generic setting of this module, `derivedFiltration`
plays the role of that filtration, `gradedZeroAddEquivRange` identifies its
piece `gr^0` with the image of the edge map, and `derivedFiltration_one_eq_ker`
identifies the rest, `F^1`, with the kernel of the edge map. Proving
degeneration in the sense of `HyperextDegenerationStatement` thus amounts to
proving that `F^1 = 0` and that the edge map is surjective. Neither is proved
here, and no `Ext` vanishing is assumed.

Specialization (explanation only). In Harris's situation `C` would be a
category of smooth representations, `W` the coefficient module, and `K` an
object of the derived category whose cohomology is the compactly supported
cohomology of the Drinfeld tower, shifted by `2(n-1)` and Tate twisted, as in
the Markdown of `Langlands.Cohomology.HyperextSpectralSequence`. None of this
is formalized here.

## Scope

- `HyperextDegenerationStatement` is not proved. No `Ext` hypothesis
  appears; the vanishing of `F^1` and the surjectivity of the edge map are
  not proved in any case.
- `graded` is not compared with the pages `E_r` or with `E_∞` of
  `hyperextSpectralSequence`; that module is not imported. Convergence of the
  spectral sequence is not proved.
- The bounds of the filtration are proved under the explicit hypotheses
  `t.IsGE B 0` and `t.IsLE K b` (in the derived setting, vanishing of the
  cohomology of `K` above `b`); no bound below on `K` is assumed or used.
- All maps are additive or set-theoretic; no linearity over a coefficient
  ring, no equivariance and no naturality in `B` or `W` is stated. Naturality
  in the source appears only as `edgeMap_comp`.
- `HasDerivedCategory.{w} C` is a hypothesis; the results hold for each such
  instance.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
pp.311-312 read in the text layer of the PDF for this module; Worker 61 read
the same pages in the rendered scans for the modules
`Langlands.Cohomology.HyperextSpectralSequence` (p.311) and
`Langlands.Cohomology.HyperextEdgeMap` (p.312).

Dependencies: `Langlands.Cohomology.HyperextDegeneration.Statement`,
`Mathlib.Algebra.Homology.DerivedCategory.TStructure` and
`Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE`, with Mathlib
pinned to Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

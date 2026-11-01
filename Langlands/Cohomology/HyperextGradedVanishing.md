# Vanishing of graded pieces of the hyperext abutment filtration

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.HyperextAbutmentFiltration` (`filtration`, `graded`,
`derivedFiltration`, `edgeMapAddMonoidHom`, `mem_derivedFiltration_one_iff`;
Worker 61), `Langlands.Cohomology.HyperextSecondPage` (`upperTriangle`,
`heartTriangle`, `secondPageExtAddEquiv`; Worker 61),
`Langlands.Cohomology.HyperextSpectralSequence` (`heartPiece`; Worker 61) and
`Langlands.Cohomology.HyperextDegeneration.Statement` (`edgeMap`,
`HyperextDegenerationStatement`; Worker 3), and on Mathlib's t-structures and
`Ext` groups.

Let `t` be a t-structure on a pretriangulated category `C`, let `K` and `B`
be objects of `C`, and let `F^p` be the abutment filtration on
`Hom(K, B⟦n⟧)` of `HyperextAbutmentFiltration`. A morphism `f` lies in
`F^p` when it factors through `K ⟶ τ_{≥ p - n} K`, equivalently when it
vanishes on `τ_{< p - n} K`. The graded piece is `gr^p = F^p / F^{p+1}`.
Page 2 of the hyperext spectral sequence has
`Hom(heartPiece t K q, B⟦p + q⟧)` in position `(p, q)`
(`HyperextSpectralSequence.secondPageIso`). For `q = n - p` this is the
group of morphisms `heartPiece t K (n - p) ⟶ B⟦n⟧`, up to the equality
`p + (n - p) = n` of shift degrees. Here `heartPiece t K (n - p)` lies in
degrees `≥ p - n` and `≤ p - n`.

This module proves that `gr^p` vanishes when this page-2 group vanishes. It
then specializes to derived categories: under the hypotheses of
`HyperextDegenerationStatement`, `F^1 = 0`, so the edge map is injective. It
does **not** prove that the edge map is surjective, so it does not prove
`HyperextDegenerationStatement`. It reduces that statement to surjectivity
(`hyperextDegenerationStatement_of_surjective`). It does not compare `gr^p`
with the pages `E_r` or with `E_∞`, and it proves no convergence. The
vanishing of `gr^p` is proved directly with distinguished triangles.

Indexing is that of `HyperextAbutmentFiltration`: `F^p` uses the truncation
at `p - n`, and `gr^p` involves `H^{p - n} K` and corresponds classically to
`E_∞^{p, n - p}`, a subquotient of `E_2^{p, n - p} = Ext^p(H^{p - n} K, B)`.

## Any t-structure

Section `TStructure` has the hypotheses of the same section of
`HyperextAbutmentFiltration`: `C` has objects in `Type u` and morphisms in
`Type v`, is preadditive, has a zero object and a shift by `ℤ` by additive
functors, and is pretriangulated; `t : TStructure C` is implicit. No
`IsTriangulated C` is needed.

| Declaration | Statement |
| --- | --- |
| `filtration_le_succ hE` | If every morphism `heartPiece t K (n - p) ⟶ B⟦n⟧` is zero (hypothesis `hE`), then `filtration t K B n p ≤ filtration t K B n (p + 1)`. |
| `filtration_succ_eq hE` | Under the same hypothesis, `filtration t K B n (p + 1) = filtration t K B n p`. |
| `subsingleton_graded_of_heartPiece hE` | Under the same hypothesis, `graded t K B n p` has at most one element. |
| `filtration_eq_bot_of_forall b p hE` | If `t.IsLE K b` and, for every `p' ≥ p`, every morphism `heartPiece t K (n - p') ⟶ B⟦n⟧` is zero, then `filtration t K B n p = ⊥`. |

Proofs. Write `q = n - p` and `m = p - n = -q`.

- `filtration_le_succ`: let `f ∈ F^p`, so `f = π ≫ g'` with
  `π : K ⟶ τ_{≥ m} K`. The distinguished triangle `upperTriangle t K q`
  (Library) is `A ⟶ K ⟶ upperPiece t K q ⟶ A⟦1⟧`, with second morphism
  `toUpperPiece t K q`. Its first object `A` lies in degrees
  `≤ -(q + 1) = m - 1`, so the composite `A ⟶ K ⟶ τ_{≥ m} K` is zero (the
  orthogonality axiom `t.zero`), and so is `A ⟶ K ⟶ B⟦n⟧`. By exactness of
  `Hom(-, B⟦n⟧)` on this triangle (Mathlib's `Triangle.yoneda_exact₂`),
  `f = toUpperPiece t K q ≫ g` for some `g`. The distinguished triangle
  `heartTriangle t K q` (Library) is
  `heartPiece t K q ⟶ upperPiece t K q ⟶ D ⟶ (heartPiece t K q)⟦1⟧`, with
  first morphism `heartPieceToUpperPiece t K q`. Its third object `D` lies
  in degrees `≥ -(q - 1) = m + 1`. By `hE`, the composite
  `heartPiece t K q ⟶ upperPiece t K q ⟶ B⟦n⟧` is zero, so by exactness
  again `g` factors through `upperPiece t K q ⟶ D`. Now
  `τ_{< m + 1} K` lies in degrees `≤ m`, so the composite
  `τ_{< m + 1} K ⟶ K ⟶ upperPiece t K q ⟶ D` is zero by `t.zero`. Hence
  `f` vanishes on `τ_{< m + 1} K = τ_{< (p + 1) - n} K`, that is,
  `f ∈ F^{p+1}` by `mem_filtration_iff_truncLTι_comp_eq_zero`.
- `filtration_succ_eq`: the other inclusion is `filtration_le_of_le`.
- `subsingleton_graded_of_heartPiece`: `subsingleton_graded_of_le`.
- `filtration_eq_bot_of_forall`: by induction on `k : ℕ`,
  `F^{p + k} = F^p` (`filtration_succ_eq` at `p + k ≥ p`). Taking
  `k = (b - p + n + 1).toNat`, we have `b < p + k - n`, so `F^{p + k} = ⊥` by
  `filtration_eq_bot`.

## Derived categories

Section `Derived` takes an abelian category `C` with objects in `Type u` and
morphisms in `Type v`, an instance `HasDerivedCategory.{w} C`, and, in each
lemma, an instance `HasExt.{w'} C`; `Abelian.Ext.{w'} X W i` is Mathlib's
`Ext` group in the universe `w'`. `H^i` is
`DerivedCategory.homologyFunctor C i`, `W₀` is
`(DerivedCategory.singleFunctor C 0).obj W`, the object `W` placed in degree
`0`, and the filtration is taken for the canonical t-structure
`DerivedCategory.TStructure.t` and `B = W₀`.

| Declaration | Statement |
| --- | --- |
| `heartPiece_hom_eq_zero_of_ext K W n p h g` | For `p : ℕ`: if `Abelian.Ext.{w'} (H^{p - n} K) W p` has at most one element (`h`), then every `g : heartPiece TStructure.t K (n - p) ⟶ W₀⟦n⟧` is zero. |
| `subsingleton_derivedGraded_of_ext K W n p h` | For `p : ℕ`, under the same hypothesis `h`: `graded TStructure.t K W₀ n p` has at most one element. |
| `derivedFiltration_eq_bot_of_ext K b hK W n p hp hW` | If `H^i K = 0` for all `i > b` (`hK`), `0 < p` (`hp`), and `Abelian.Ext.{w'} (H^k K) W i` has at most one element for every `k : ℤ` and every `i : ℕ` with `0 < i` (`hW`), then `derivedFiltration K W n p = ⊥`. |
| `edgeMap_injective_of_ext K b hK W hW n` | Under the hypotheses `hK` and `hW` above, `HyperextDegeneration.edgeMap K W n` is injective. |
| `edgeMapAddEquivRangeOfExt K b hK W hW n` | Under the hypotheses `hK` and `hW`, an additive isomorphism from `ShiftedHom K W₀ n` to the range of `edgeMapAddMonoidHom K W n`, sending `f` to `edgeMap K W n f` (`edgeMapAddEquivRangeOfExt_apply_coe`, a `simp` lemma). |
| `hyperextDegenerationStatement_of_surjective h` | If, for all `K`, `b`, `W` satisfying `hK` and `hW` and all `n : ℤ`, the edge map `HyperextDegeneration.edgeMap K W n` is surjective (`h`), then `HyperextDegenerationStatement.{w, w'} C` holds. |

The hypotheses `hK` and `hW` are exactly those of
`HyperextDegenerationStatement`. So under them the abutment filtration is
`Hom(K, W₀⟦n⟧) = F^0 ⊇ F^1 = 0`, and the edge map identifies
`Hom(K, W₀⟦n⟧)` with a subgroup of `Hom(H^{-n} K, W)`
(`edgeMapAddEquivRangeOfExt`). Surjectivity of the
edge map is the remaining part of `HyperextDegenerationStatement`; it is not
proved here. Classically it holds because the differentials leaving
`E_r^{0, n}` land in terms `E_r^{r, n - r + 1}`, which are subquotients of
`Ext^r(H^{r - n - 1} K, W) = 0` for `r ≥ 2`; this argument is not
formalized.

Proofs.

- `heartPiece_hom_eq_zero_of_ext`: the Library's
  `secondPageExtAddEquiv K W p (n - p)` is an additive equivalence from
  `heartPiece TStructure.t K (n - p) ⟶ W₀⟦p + (n - p)⟧` to
  `Abelian.Ext (H^{-(n - p)} K) W p`. The index `-(n - p)` is rewritten as
  `p - n`, so the target has at most one element by `h`; the source then
  has at most one element (`Function.Injective.subsingleton`), and the
  shift degree `p + (n - p)` is rewritten as `n`.
- `subsingleton_derivedGraded_of_ext`: `subsingleton_graded_of_heartPiece`
  with the previous lemma.
- `derivedFiltration_eq_bot_of_ext`: `hK` gives `K.IsLE b` (Mathlib's
  `DerivedCategory.isLE_iff`). Apply `filtration_eq_bot_of_forall b p`: for
  `p' ≥ p > 0`, write `p' = m` with `m : ℕ` and `m > 0`, and use
  `heartPiece_hom_eq_zero_of_ext` with `hW (m - n) m`.
- `edgeMap_injective_of_ext`: if `edgeMap K W n f = 0`, then
  `f ∈ derivedFiltration K W n 1` (`mem_derivedFiltration_one_iff`), which
  is `⊥` by the previous lemma with `p = 1`; so `f = 0`. This suffices
  because the edge map is additive (`edgeMapAddMonoidHom`).
- `edgeMapAddEquivRangeOfExt`: Mathlib's `AddMonoidHom.ofInjective` applied
  to `edgeMapAddMonoidHom K W n` and `edgeMap_injective_of_ext`.
- `hyperextDegenerationStatement_of_surjective`: bijectivity is
  `edgeMap_injective_of_ext` together with `h`.

## Provenance and interpretation

The statements and proofs are ours, assembled from Mathlib and the Library.
The vanishing of `gr^p` when `E_2^{p, n - p}` vanishes is the standard
consequence of the construction of the hypercohomology spectral sequence of
`RHom(-, B)` from the truncations of the source; here it is proved directly
from the truncation triangles of `HyperextSecondPage`, without the spectral
sequence. The scope of this module (graded vanishing and injectivity of the
edge map, with surjectivity left as a separate step) was agreed with
Worker 13, who also asked that the statement `HyperextDegenerationStatement`
not be changed here; it is only used.

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

Interpretation (explanation only). In (4.10.1) the vanishing of the higher
`Ext` groups makes every term `E_2^{i,j}` with `i > 0` zero. The lemma
`derivedFiltration_eq_bot_of_ext` is the corresponding statement for the
generic filtration of this framework: when the higher `Ext` groups from the
cohomology objects of `K` into `W` vanish, every step `F^p` with `p > 0` of
the abutment filtration is zero. So the abutment injects into
`E_2^{0, n} = Hom(H^{-n} K, W)` by the edge map. Harris's isomorphism (5.2)
also needs the surjectivity of the edge map, which is not proved here. In
Harris's situation `C` would be a category of smooth representations and `K`
an object of its derived category whose cohomology is the compactly supported
cohomology of the Drinfeld tower, shifted and Tate twisted; none of this is
formalized here.

## Scope

- `HyperextDegenerationStatement` is not proved: surjectivity of the edge map
  is not proved in any case. `hyperextDegenerationStatement_of_surjective`
  takes it as a hypothesis.
- `graded` is not compared with the pages `E_r` or `E_∞` of
  `hyperextSpectralSequence`, and convergence is not proved; the
  page-2 groups enter only through their descriptions as morphism groups
  out of `heartPiece`.
- Only the vanishing of graded pieces is proved; no nonzero graded piece is
  computed beyond `gr^0` of `HyperextAbutmentFiltration`.
- All maps are additive or set-theoretic; no linearity over a coefficient
  ring, equivariance or naturality is stated.
- `HasDerivedCategory.{w} C` and `HasExt.{w'} C` are hypotheses; the results
  hold for each such instance.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
pp.311-312 reread in the text layer of the PDF for this module.

Dependencies: `Langlands.Cohomology.HyperextAbutmentFiltration` and
`Langlands.Cohomology.HyperextSecondPage`, with Mathlib pinned to Lean 4.34.0
and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

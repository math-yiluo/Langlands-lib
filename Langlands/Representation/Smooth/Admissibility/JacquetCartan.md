# Jacquet's admissibility theorem from a Jacquet–Cartan datum

Module `Langlands.Representation.Smooth.Admissibility.JacquetCartan`.

The module isolates the group-theoretic input of Jacquet's theorem that
irreducible smooth representations are admissible (Renard, VI.2.2 Théorème). It
packages that input in a structure, `Langlands.JacquetCartanDatum G`, on an
arbitrary topological group `G`. It then proves the theorem for every
topological group that has a compact open subgroup and such a datum. The module
proves nothing about reductive groups. Whether a given group (for example
`G(F)` for a connected reductive `G` over a nonarchimedean local field) carries
a datum is a separate statement, not made here.

## The datum

`structure JacquetCartanDatum.{uG, uι} (G : Type uG) [Group G] [TopologicalSpace G]`
lives in `Type (max uG (uι + 1))`. The index types `ι` and `wall i` are in a
separate universe `uι`. Its fields are:

| Field | Meaning |
| --- | --- |
| `ι : Type uι`, `rank : ι → ℕ` | index type of the parabolic pairs, with a natural-number rank |
| `levi i`, `unipotent i : Subgroup G` | Levi and unipotent subgroups of the pair `i` |
| `top : ι`, `unipotent_top : unipotent top = ⊥` | an index with trivial unipotent subgroup (the group itself) |
| `levi_le_normalizer` | `levi i ≤ Subgroup.normalizer (unipotent i)` |
| `isClosed_levi` | `levi i` is closed in `G` |
| `iwasawa` | for each `i` there is a compact `C ⊆ G` with every `g = m * n * c`, `m ∈ levi i`, `n ∈ unipotent i`, `c ∈ C` |
| `wall : ι → Type uι` | the walls of `levi i` (this type may be empty) |
| `wallUnipotent i a : Subgroup G`, `wallUnipotent_le` | a subgroup of `levi i` for each wall `a` |
| `descent` | for each wall `a` there is `j` with `rank j < rank i` and every `n ∈ unipotent j` of the form `u * n'` with `u ∈ wallUnipotent i a`, `n' ∈ unipotent i` |
| `cartanCompact i`, `cartanSet i : Set G` | compact subset and countable subset of `levi i` (`isCompact_cartanCompact`, `cartanCompact_subset`, `countable_cartanSet`, `cartanSet_subset`) |
| `cartan` | every `m ∈ levi i` is `k₁ * t * k₂` with `k₁, k₂ ∈ cartanCompact i` and `t ∈ cartanSet i` |
| `contraction` | for every neighbourhood `O` of `1` and every choice of finite sets `S a ⊆ wallUnipotent i a`, there is a compact `D ⊆ G` such that each `t ∈ cartanSet i` either equals `d * z` with `d ∈ D`, `z ∈ levi i` and `z` commuting with every element of `levi i`, or satisfies `t * u * t⁻¹ ∈ O` for all `u ∈ S a`, for some wall `a` |

Neither `cartanSet i` nor `S a` is required to be a subgroup or to be symmetric.
The centre in `contraction` is the abstract centralizer condition inside
`levi i`, not an algebraic centre. If `wall i` is empty, `contraction` says
that `cartanSet i` lies in a compact set times the centre of `levi i`.

### Provenance

The datum is an internal abstraction (provenance `derived`). It records, as
hypotheses, the structural facts that Renard's proof of VI.2.1 and VI.2.2 uses
for `G(F)`. The fields are modelled on the following situation, which this
module does not formalize. The index `i` runs over standard parabolic subgroups
`P_I = M_I N_I` (subsets `I` of the simple relative roots), with `rank = |I|`
and `top = Δ`. `iwasawa` is the Iwasawa decomposition `G = P_∅ K₀` (Renard
V.5.1 (1)), for which `C = K₀` serves. A wall of `M_I` is a root `α ∈ I`, with
wall unipotent subgroup `N_{I∖{α}} ∩ M_I`, the unipotent radical of a maximal
standard parabolic subgroup of `M_I`. `descent` is the decomposition
`N_{I∖{α}} = (N_{I∖{α}} ∩ M_I) N_I` used in the proof of the VI.2.1
Corollaire (via VI.1.4). `cartan` is the Cartan decomposition of `M_I`
(V.5.1 (4) for `M_I`, which V.5.1 (5) provides, with the dominant part as
`cartanSet`).
`contraction` is the dichotomy used in the proof of `a) ⇒ b)` of the VI.2.1
Théorème: either a sequence of dominant elements stays compact modulo the
centre, or some simple root `α` has `|α(t_n)| → 0` (VI.2.1.1), so that conjugation
by `t_n` contracts the unipotent radical of the maximal parabolic of `α`.

## Main results

* `Langlands.isAdmissible_of_jacquetCartanDatum (𝒟 : JacquetCartanDatum.{uG, uι} G)
  (hK₀ : ∃ K : OpenSubgroup G, IsCompact (K : Set G)) (ρ : Representation ℂ G V)
  (hρ : IsSmooth ρ) (hirr : ρ.IsIrreducible) : IsAdmissible ρ`, for a group
  `G : Type uG` with `[TopologicalSpace G] [IsTopologicalGroup G]` and a complex
  vector space `V : Type uV`. `IsAdmissible` is the Library's all-open-subgroups
  convention: smooth, with finite-dimensional fixed vectors for every open
  subgroup.
* `Langlands.SmoothRep.isAdmissible_of_jacquetCartanDatum 𝒟 hK₀ (A : SmoothRep.{0, uG, uV} ℂ G)
  (hA : A.IsIrreducible) : A.IsAdmissible`, the same statement for objects of the
  smooth category.

Helper lemmas, in namespace `Langlands.JacquetCartanDatum`:

* `relations_bot`: the coinvariant relations of the trivial subgroup vanish.
* `exists_finset_inv_mul_mem`: finitely many left cosets `f H` of an open
  subgroup `H` cover a compact set.
* `finite_image_of_isCompact`: a compact set moves a smooth vector to finitely
  many vectors.
* `rank_le_aleph0_of_compact_cover`: if every group element is `a * t * b` with
  `a, b` in compact sets and `t` in a countable set, then an irreducible smooth
  representation has countable dimension.
* `conjOpenSubgroup M K f`, `mem_conjOpenSubgroup`: the open subgroup
  `{m ∈ M | f⁻¹ m f ∈ K}` of a subgroup `M`.
* `isCompact_preimage_levi`: compact subsets of `G` pull back to compact subsets
  of the closed subgroup `levi i`.
* `exists_minimal`: there is an index `i` with nonzero Jacquet module
  (`Jacquet.relations ρ (unipotent i) ≠ ⊤`) such that every index of smaller
  rank has zero Jacquet module (the index `top` has nonzero Jacquet module).
* `rank_le_aleph0_levi`: irreducible smooth representations of `levi i` have
  countable dimension, by `cartan` and `countable_cartanSet`.
* `finite_fixedVectors_levi`: an irreducible smooth representation `σ` of
  `levi i` whose wall coinvariant relations are everything
  (`Jacquet.relations σ ((wallUnipotent i a).subgroupOf (levi i)) = ⊤` for every
  wall `a`) has finite-dimensional fixed vectors under every open subgroup of
  `levi i`.

## Proof

The implemented route follows the structure of Jacquet's argument, but it
avoids parabolic induction, Frobenius reciprocity, Haar measure on `G`,
matrix coefficients and the notion of compact representation.

1. **Minimal index.** `exists_minimal` picks `i` of minimal rank with
   `Jacquet.relations ρ (unipotent i) ≠ ⊤`. Such an index exists because
   `unipotent top = ⊥` and `relations_bot`. Write `M = levi i`, `N = unipotent i`.
2. **Irreducible quotient of the Jacquet module.** The Jacquet module
   `Jacquet.Coinvariants ρ N` with the `M`-action `Jacquet.action` is nonzero.
   By `iwasawa` it is generated, as an `M`-representation, by the finitely many
   classes of `ρ c v₀` with `c ∈ C` (`finite_image_of_isCompact`). So it has a
   maximal proper subrepresentation
   (`QuasicuspidalEmbedding.exists_isCoatom_subrepresentation`), and the
   quotient `σ` is irreducible (`QuasicuspidalEmbedding.isIrreducible_of_isCoatom`)
   and smooth (`isSmooth_of_surjective`). Let `q : V → X` be the composite
   projection. It satisfies `q (ρ m v) = σ m (q v)` for `m ∈ M` and
   `q (ρ n v) = q v` for `n ∈ N`.
3. **The walls of `σ` are killed.** For a wall `a`, `descent` gives `j` of smaller
   rank, so `Jacquet.relations ρ (unipotent j) = ⊤` by minimality. Writing
   `n = u * n'` gives `q (ρ n x - x) = σ u (q x) - q x`. Hence `q` maps the
   relations of `unipotent j` into the relations of the wall subgroup of `σ`,
   and since `q` is surjective, the latter are everything.
4. **Finite fixed vectors of `σ`** (`finite_fixedVectors_levi`). This step plays
   the role of VI.2.1 `a) ⇒ b)` followed by IV.1.3. Let `H` be an open subgroup
   of `M` and `Hc = H ∩ K₀`, a compact open subgroup of `M`. Let `avg` be the
   `Hc`-averaging projection `Compact.averageMap`, which is the identity on
   `Hc`-fixed vectors. Fix `w₀ ≠ 0`. Cover the compact `cartanCompact i` by
   finitely many cosets `k e⁻¹ ∈ Hc`, `e ∈ E`. Then `Y`, the orbit of `w₀`
   under `cartanCompact i`, is finite. For each wall `a` and `y ∈ Y` choose a
   finite expression of `y` as a combination of relations `σ u x - x`. Let
   `S a` be the finite set of the elements `u` used. Choose `O` such that
   `e O e⁻¹ ⊆ Hc` for all `e ∈ E`, and let `D` be the compact set given by
   `contraction`. For `m = k₁ t k₂`:
   * if `t = d z` with `z` central in `M`, Schur's lemma in countable dimension
     (`LeviAdmissibility.exists_scalar_of_central`, using `rank_le_aleph0_levi`)
     makes `σ z` a scalar. So `avg (σ m w₀)` is a multiple of `avg (σ e (σ d y))`
     with `e ∈ E`, `y ∈ Y` and `d` in the compact set `D`, a finite set of
     vectors;
   * otherwise some wall `a` has `t u t⁻¹ ∈ O` for every `u ∈ S a`. Then
     `(e t) u (e t)⁻¹ ∈ Hc`, so `avg (σ (e t) (σ u x - x)) = 0`, and
     `avg (σ m w₀) = 0`.

   Hence `avg` maps the span of the orbit of `w₀`, which is all of `X`
   (irreducibility), into the span of a finite set. The `H`-fixed vectors are
   `Hc`-fixed, `avg` is the identity on them, so they lie in that span and form
   a finite-dimensional space.
5. **Embedding the fixed vectors of `ρ`.** This step replaces the embedding of
   `ρ` into `i_P(σ)` and III.2.3. The subrepresentation of vectors `v` with
   `q (ρ g v) = 0` for every `g` is proper (it misses a preimage of a nonzero
   vector of `σ`), hence zero. Let `K` be an open subgroup and
   `K' = K ∩ K₀`. Cover `C` by finitely many cosets `f K'`, `f ∈ E`. The linear
   map `v ↦ (q (ρ f v))_{f ∈ E}` sends the `K'`-fixed vectors of `ρ` into the
   product of the fixed vectors of `σ` under the open subgroups
   `conjOpenSubgroup M K' f`. It is injective: by `iwasawa`,
   `q (ρ (m n c) v) = σ m (q (ρ f v))` for `c ∈ f K'`, so its kernel lies in the
   zero subrepresentation. By step 4 the target is finite-dimensional, so the
   `K'`-fixed vectors are, and `finite_fixedVectors_of_le` passes to `K ⊇ K'`.

Countable dimension of `σ` (needed for Schur's lemma) comes from the Cartan
decomposition of `M` alone. No Cartan decomposition of `G` is used. The
hypothesis `hK₀` supplies the compact open subgroups.

## Sources

* D. Renard, *Représentations des groupes réductifs p-adiques* (2026 version):
  VI.2.2 Théorème (printed p. 140, PDF p. 146), the result being abstracted.
  VI.2.1 Théorème, proof of `a) ⇒ b)` with (VI.2.1.1), and the Corollaire
  (printed pp. 138–139, PDF pp. 144–145): the contraction and minimal-parabolic
  arguments. V.5.1 (1), (4), (5) (printed p. 122, PDF p. 128): the Iwasawa and Cartan
  decompositions, also for standard Levi subgroups, that `iwasawa` and `cartan`
  model.

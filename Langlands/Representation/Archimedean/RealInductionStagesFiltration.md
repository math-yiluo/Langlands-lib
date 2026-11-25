# Induction in stages of adjacent filtrations

Module: `Langlands.Representation.Archimedean.RealInductionStagesFiltration`.

## Purpose and provenance

This module proves `Langlands.Archimedean.RealAdjacentFiltrationInStagesStatement` (module
`RealInducedPairFiltrationReduction`), as the theorem `realAdjacentFiltrationInStages`. That
statement is one of the four inputs of `realInducedPairFiltration_of_base`, the reduction of
`RealInducedPairFiltrationStatement`.

The statement says the following. Let `pre ++ x :: y :: post` have rank `n`, and let
`r = realRank [x, y]`. A filtration as in `RealAdjacentFiltration` of the standard module of
`[x, y]` on `GL_r(ℝ)` yields such a filtration of the standard module of
`pre ++ x :: y :: post` on `GL_n(ℝ)`. The proof keeps the same number `k` of pieces and the
same lists `ws j`. It replaces each map `q j` on `GL_r(ℝ)` by the induced map
`Q j = ind (avg (q j))` on `GL_n(ℝ)`. Here `avg` is the average over `O(r)` of
`RealInductionStagesAverage`, and `ind` is the induced map of `RealInductionStagesInduce`.

The construction is the function-level form of induction in stages (compare Knapp–Vogan,
*Cohomological Induction and Unitary Representations*, (11.196)). The proof is internal; the
module makes no further literature claim.

All declarations are in the namespace `Langlands.Archimedean.InductionStages`. Notation is as
in the earlier `RealInductionStages*` modules. `KFin n L` is the space of `O(n)`-finite
functions of the real standard module of `L`. `kRep` and `lie` are right translation by
`O(n)` and the right derivative on it. `σ_κ = sliceK h ha hr κ` is the slice.

## Declarations

### Intertwiners modulo a subspace

- `coe_kRep k f`: the underlying function of `kRep n ds k f` is the Library's
  `Whittaker.rightTranslation` of `f` by `k`.
- `isRealIntertwinerModulo_iff`: `IsRealIntertwinerModulo n ds es M q` holds iff
  `q (R(k) f) - R(k) (q f) ∈ M` and `q (R(X) f) - R(X) (q f) ∈ M` for all `k ∈ O(n)`, all real
  `X` and all `f`, stated with `kRep` and `lie`. Proof: the subtypes in the definition are
  `kRep n ds k f` and `lie n ds X f`, by `coe_kRep` and `lie_apply_coe`.
- `isRealIntertwinerModulo_comp_ofEq e hq`: for an equality of lists `e : L₁ = L₂`,
  precomposing an intertwiner modulo `M` with the identification
  `LinearEquiv.ofEq (KFin n L₁) (KFin n L₂)` gives an intertwiner modulo `M` (by `subst`).

### Linear sections

- `exists_section T N N' hN`: let `T : W →ₗ[ℂ] V` be linear and `N`, `N'` subspaces of `V`.
  Suppose every `v ∈ N'` satisfies `T u - v ∈ N` for some `u`. Then there is a linear
  `s : V →ₗ[ℂ] W` with `T (s v) - v ∈ N` for all `v ∈ N'`. Proof: `N.mkQ` maps `N'` into the
  range of `φ = N.mkQ ∘ T`. Compose with a linear right inverse of `φ` onto its range
  (`LinearMap.exists_rightInverse_of_surjective`). Extend the resulting map from `N'` to `V`
  (`LinearMap.exists_extend`).

### The filtration on `GL_r(ℝ)`

Let `q j : KFin r (ws j) →ₗ[ℂ] KFin r ds` for `j : Fin k`.

- `filt q m = ⨆_{i < m} range (q i)`, for `m : ℕ`. For `j : Fin k`, `filt q j` is the subspace
  `⨆ (i : Fin k) (_ : i < j), range (q i)` of `RealAdjacentFiltration`.
- `range_le_filt`: `range (q i) ≤ filt q m` if `i < m`. `filt_mono`: `filt q` is monotone.
  `filt_zero`: `filt q 0 = ⊥`. `filt_succ_le`: `filt q (m + 1) ≤ filt q m ⊔ range (q m)` for
  `m < k`. `filt_eq_top`: `filt q k = ⊤` if the ranges of the `q j` span everything.
- `kRep_mem_filt hq m κ`: suppose every `q j` commutes with `O(r)` modulo `filt q j`. Then every
  `filt q m` is `O(r)`-stable. Proof: for `i < m`,
  `R(κ) q i f = q i (R(κ) f) - (q i (R(κ) f) - R(κ) q i f)`. The first term lies in
  `range (q i)` and the second in `filt q i`; both are contained in `filt q m`.

### Induction in stages

Let `h : a + r ≤ n`, `ha : realRank pre = a`, `hr : realRank ds = r` and
`hn : realRank (pre ++ ds ++ post) = n`.

- `realRank_of_realRank_eq hes`: `realRank (pre ++ es ++ post) = n` if `realRank es = r`.
- `eq_zero_of_sliceK G hG`: if every slice `σ_κ G` (`κ ∈ O(n)`) is zero, then `G = 0`. Proof:
  `G(κ) = (σ_κ G)(1) = 0` on `O(n)` (`sliceK_apply_one`), and `G` lies in a principal series
  (`eq_of_eqOn_unitaryCompact_of_mem_principalSeries`).
- `exists_sub_mem_range_ind hes T hT N N' hNst hN'st hN G hG` (**one step**): let
  `T : KFin r es → KFin r ds` commute exactly with `O(r)`. Let `N`, `N'` be `O(r)`-stable, and
  suppose every `v ∈ N'` satisfies `T u - v ∈ N` for some `u`. If every slice of `G` lies in
  `N'`, then there is `G'` with every slice in `N` and `G - G' ∈ range (ind T)`. Proof. Take a
  linear section `s0` (`exists_section`), and let `s = avg s0`. Then `s` commutes exactly with
  `O(r)` (`avg_kRep`). Also `T (s v) - v ∈ N` for `v ∈ N'`: by `map_avg`, `T (avg s0 v)` is the
  average of the conjugates `R(κ)⁻¹ T s0 R(κ) v`, and each conjugate differs from `v` by an
  element of `N` (`avg_sub_mem`). Put `G' = G - ind T (ind s G)`. By `sliceK_ind` (twice),
  `σ_κ G' = σ_κ G - T (s (σ_κ G)) ∈ N`.
- `exists_stages_filtration hws q hq htop` (**induction in stages of filtrations**): let
  `realRank (ws j) = r` for all `j`. Let every `q j` be an intertwiner modulo
  `⨆_{i<j} range (q i)`, and let the ranges of the `q j` span `KFin r ds`. Then there are maps
  `Q j : KFin n (pre ++ ws j ++ post) → KFin n (pre ++ ds ++ post)` with the same two
  properties. Proof.
  1. By `isRealIntertwinerModulo_iff` and `kRep_mem_filt`, every `filt q m` is
     `O(r)`-stable. Let `T j = avg (q j)`. It commutes exactly with `O(r)` (`avg_kRep`). It
     satisfies `T j f - q j f ∈ filt q j` (`avg_sub_self_mem`). It commutes with right
     derivatives modulo `filt q j` (`lie_avg_sub_mem`).
  2. Let `Q j = ind (T j)`. **Key claim**, by induction on `m ≤ k`: if every slice of `G` lies
     in `filt q m`, then `G ∈ ⨆_{i<m} range (Q i)`. For `m = 0`, `G = 0` by
     `eq_zero_of_sliceK`. For `m + 1`, apply `exists_sub_mem_range_ind` with `T = T m`,
     `N = filt q m` and `N' = filt q (m + 1)`. The hypothesis holds because
     `v = y + q m u` with `y ∈ filt q m` (`filt_succ_le`), and then
     `T m u - v = (T m u - q m u) - y ∈ filt q m`. This gives `G'` with slices in `filt q m`,
     which lies in `⨆_{i<m} range (Q i)` by induction, and `G - G' ∈ range (Q m)`.
  3. `Q j` commutes exactly with `O(n)` (`ind_kRep`). By `sliceK_ind_lie_sub_mem`, every slice
     of `Q j (R(X) F) - R(X) (Q j F)` lies in `filt q j`. So this difference lies in
     `⨆_{i<j} range (Q i)` by the key claim. Hence `Q j` is an intertwiner modulo that
     subspace (`isRealIntertwinerModulo_iff`).
  4. Every `G` has all its slices in `filt q k = ⊤`. So the key claim with `m = k` shows that
     the ranges of the `Q j` span everything.

### The statement

- `realAdjacentFiltrationInStages : RealAdjacentFiltrationInStagesStatement`. Proof. Let the
  filtration on `GL_r(ℝ)`, `r = realRank [x, y]`, be given by `k`, `ws` and `q`.
  - Every `ws j` has rank `r`. If `ws j = [y, x]` this is commutativity of addition. Otherwise
    the exponent supports are permutations of each other, and the length of the support is
    the rank (`length_realExponentSupport`).
  - The source of `q j` is the standard module of `[] ++ ws j ++ []`. Composing with
    `LinearEquiv.ofEq` for `ws j = [] ++ ws j ++ []` gives maps out of the standard module of
    `ws j`. These have the same ranges and are still intertwiners modulo the same subspaces
    (`isRealIntertwinerModulo_comp_ofEq`).
  - Apply `exists_stages_filtration` with `a = realRank pre`, `ds = [x, y]` and
    `pre ++ [x, y] ++ post`. Then rewrite along `pre ++ x :: y :: post = pre ++ [x, y] ++ post`.
    The conditions on the lists `ws j` are unchanged.

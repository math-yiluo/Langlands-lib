# Filtrations of real standard modules by standard modules

Lean module: `Langlands.Representation.Archimedean.RealStandardFiltration`
(namespace `Langlands.Archimedean.RealStandardFiltration`).

The Library notion `RealAdjacentFiltration n pre post x y` (module `RealRankOneStepFiltration`)
filters the `O(n)`-finite functions of the standard module of `pre ++ x :: y :: post` by
finitely many linear maps `q j`, indexed by `Fin k`, out of the `O(n)`-finite functions of the
standard modules of the lists `pre ++ ws j ++ post`. Each `q j` is an intertwiner modulo the span
of the ranges of the `q i` with `i < j` (`IsRealIntertwinerModulo`), and the ranges of all
`q j` span everything. Every `ws j` must be `[y, x]`, or a list whose exponent support is a
permutation of that of `[x, y]` and whose sum of squared weights is strictly larger.

Filtrations of this kind are built in steps: filter, filter each piece again, transport along
a surjection or along an equality of spaces. This module defines the notion in the generality
those steps need and proves the step rules. Everything here is internal to the Library. It
formalizes the standard facts that a filtration by `(𝔤, K)`-submodules can be refined by
filtering its graded pieces, and that it can be pushed forward along a surjective
homomorphism. No literature is cited.

Notation: `K(ds)` is `KF n ds`, an abbreviation for
`kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)`, the `O(n)`-finite functions
of the standard module of the list `ds` of real blocks on `GL_n(ℝ)`.

## Intertwiners modulo a subspace

`IsRealIntertwinerModulo n ds es M q` (Library) says this about a linear map `q : K(ds) → K(es)`
and a subspace `M` of `K(es)`. For every `k ∈ O(n)` and `f ∈ K(ds)`, the right translates by `k`
of `f` and of `q f` lie in `K(ds)` and `K(es)`, and `q (k·f) - k·(q f) ∈ M`. The same holds for
the right derivative along every real `n × n` matrix `X`.

* `modulo_mono`: if `q` is an intertwiner modulo `M` and `M ≤ M'`, it is one modulo `M'`.
* `modulo_comp`: let `q : K(es) → K(ds)` be an intertwiner modulo `M` and
  `r : K(fs) → K(es)` one modulo `M'`. Then `q ∘ r` is an intertwiner modulo `M ⊔ q(M')`.
  Proof: `(q∘r)(k·f) - k·(q(r f)) = (q(k·(r f)) - k·(q(r f))) + q(r(k·f) - k·(r f))`. The
  same identity holds for derivatives.
* `modulo_comp_bot`: the case `M' = ⊥` (an exact intertwiner `r`) gives modulo `M`.
* `modulo_id`: the identity of `K(ds)` is an exact intertwiner (modulo `⊥`). Membership of the
  translates and derivatives comes from the Library lemmas
  `rightTranslation_mem_kFiniteFunctions_realStandardModule` and
  `rightDerivative_mem_kFiniteFunctions_realStandardModule`.
* `ofEqMap h`, for `h : K(ds) = K(es)`: the identification `K(ds) → K(es)`, which is the
  identity on underlying functions (`ofEqMap_apply_coe`). It is surjective
  (`ofEqMap_surjective`) and an exact intertwiner (`modulo_ofEqMap`).
* `modulo_of_comp_surjective` (descent): let `q : K(es) → K(ds)` be an intertwiner modulo `M`
  with `q = q' ∘ π`, where `π : K(es) → K(es')` is a surjective exact intertwiner. Then `q'` is
  an intertwiner modulo `M`. Proof: write `g = π f`. Then `k·g = π(k·f)`, so
  `q'(k·g) - k·(q' g) = q(k·f) - k·(q f) ∈ M`. The same works for derivatives.

## Filtrations

* `IsFiltration n ds es q`, for a linearly ordered index type `ι`, lists `es : ι → List RealBlock`
  and linear maps `q j : K(es j) → K(ds)`, holds when:
  1. every `q j` is an intertwiner modulo `⨆ (i < j), range (q i)`;
  2. `⨆ j, range (q j) = ⊤`.

  For `ι = Fin k` and `ds = pre ++ x :: y :: post` these are the last two clauses of
  `RealAdjacentFiltration`.
* `HasFiltration n ds P`, for a predicate `P` on lists of real blocks: there are a type `ι`
  with a `Fintype` and a `LinearOrder` structure, lists `es j` all satisfying `P`, and maps
  `q j` forming an `IsFiltration`.

The rules:

* `HasFiltration.self`: if `P ds`, the identity of `K(ds)` is a one-piece filtration
  (`ι = Unit`).
* `HasFiltration.mono`: a filtration with `P`-pieces has `Q`-pieces whenever `P` implies `Q`.
* `iSup_range_comp`: if `⨆ i, range (r i) = ⊤`, then `⨆ i, range (q ∘ r i) = range q`.
* `HasFiltration.bind` (refinement): suppose `K(ds)` has a filtration with `P`-pieces, and every
  list `es` satisfying `P` has a filtration with `Q`-pieces. Then `K(ds)` has a filtration with
  `Q`-pieces.

  Proof: choose a filtration `(q j)_{j ∈ ι}` of `K(ds)`, and for every `j` a filtration
  `(r j i)_{i ∈ κ j}` of `K(es j)`. The new index type is the lexicographic sigma type
  `Lex (Σ j, κ j)`, finite and linearly ordered (Mathlib's `Sigma.Lex.linearOrder`). The
  piece at `(j, i)` is `q j ∘ r j i`. By `modulo_comp`, this piece is an intertwiner modulo
  `M_j ⊔ q j (N_{j,i})`, where `M_j = ⨆ (j' < j), range (q j')` and
  `N_{j,i} = ⨆ (i' < i), range (r j i')`. Both terms lie in the span of the ranges of the
  pieces `(j', i')` before `(j, i)`. The term `M_j` does because
  `range (q j') = ⨆ i', range (q j' ∘ r j' i')` (`iSup_range_comp`), and `(j', i') < (j, i)`
  whenever `j' < j` (`Sigma.Lex.left`). The term `q j (N_{j,i})` does because its parts are
  the ranges `range (q j ∘ r j i')` with `i' < i` (`Sigma.Lex.right`). The ranges of all new
  pieces span `⨆ j, range (q j) = ⊤`.
* `HasFiltration.map` (pushforward): let `T : K(ds) → K(ds')` be a surjective exact
  intertwiner. A filtration `(q j)` of `K(ds)` gives the filtration `(T ∘ q j)` of `K(ds')`
  with the same pieces. By `modulo_comp`, `T ∘ q j` is an intertwiner modulo
  `⊥ ⊔ T(⨆ (i < j), range (q i)) = ⨆ (i < j), range (T ∘ q i)`. The ranges span
  `range T = ⊤`.
* `HasFiltration.congr`: if `K(ds) = K(ds')`, a filtration of `K(ds)` gives one of `K(ds')`
  with the same pieces: apply `map` to `ofEqMap`.
* `HasFiltration.of_eq_pieces`: suppose every list `es` satisfying `P` has the same
  `O(n)`-finite functions as some list `es'` satisfying `Q`. Then a filtration with `P`-pieces
  gives one with `Q`-pieces. Proof: `bind` with the one-piece filtrations of `K(es')`
  (`self`), transported to `K(es)` (`congr`).

## Adjacent filtrations

* `IsFiltration.reindex`: reindexing an `IsFiltration` along an order isomorphism `ι' ≃o ι`
  gives an `IsFiltration`.
* `IsAdjacentPiece pre post x y es`: there is a list `ws` with `es = pre ++ ws ++ post`, where
  either `ws = [y, x]`, or `realExponentSupport ws` is a permutation of
  `realExponentSupport [x, y]` and `realWeightSquareSum [x, y] < realWeightSquareSum ws`. These
  are the conditions on the pieces in `RealAdjacentFiltration`.
* `realAdjacentFiltration_iff`: `RealAdjacentFiltration n pre post x y` holds if and only if
  `HasFiltration n (pre ++ x :: y :: post) (IsAdjacentPiece pre post x y)`.

  Proof. Forward: take `ι = Fin k` and the pieces `pre ++ ws j ++ post`. Backward: choose the
  lists `ws j` with `es j = pre ++ ws j ++ post`. Reindex along the order isomorphism
  `Fin (card ι) ≃o ι` (`Fintype.orderIsoFinOfCardEq`). Compose each `q j` with
  `ofEqMap : K(pre ++ ws j ++ post) → K(es j)`, which is surjective and exact, so the ranges and
  the intertwining conditions are unchanged (`modulo_comp_bot`).

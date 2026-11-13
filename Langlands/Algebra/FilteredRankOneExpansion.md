# Unique expansions from a filtration with rank-one graded pieces

Author: Worker 5226. This is an internal algebraic lemma, derived for the free-module conclusion of the first lemma of Renard VI.10.4 (printed pp.209–212 / PDF pp.215–218). Reference: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Renard does not state this lemma. It is the standard fact that a module with a finite filtration whose successive quotients are zero or free of rank one is free, with a basis made of lifts of the rank-one generators. Here it is stated in the elementwise form the planned proof needs.

## Statement

`Langlands.FilteredModule.existsUnique_expansion` has the following data:
- `A` is an arbitrary ring, not necessarily commutative, and `X` is a left `A`-module.
- `n : ℕ` is the number of steps.
- `K : Fin (n + 1) → Submodule A X` is a decreasing filtration, so `K (j + 1) ≤ K j` for every `j : Fin n`, with `K 0 = ⊤` and `K n = ⊥`.
- `S : Finset (Fin n)` is the set of rank-one steps.
- `v : Fin n → X` gives the chosen generators.

It assumes:
- `hmem`: for `j ∈ S`, `v j ∈ K j`;
- `huniq`: for `j ∈ S` and every `x ∈ K j`, there is exactly one `a : A` with `x - a • v j ∈ K (j + 1)`;
- `hzero`: for `j ∉ S`, `K j ≤ K (j + 1)`, so that step is trivial.

It concludes: for every `x : X` there is exactly one coefficient family `a : S → A` with `x = ∑ j : S, a j • v j`. The definition `basisOfFilteredRankOne` below packages this as a basis of `X` made of the elements `v j` for `j ∈ S`.

The assumption `huniq` says that the successive quotient `K j / K (j + 1)` is free of rank one on the class of `v j`. Existence of `a` means the class generates the quotient. Uniqueness means its annihilator is zero. No quotient modules appear in the Lean statement.

## Proof

There are two private auxiliary lemmas.

- `exists_expansion_aux` is downward induction on the step. Every element of `K (n - i)` is a combination `∑_{j ∈ S} a j • v j`.
  - Base case: `K n = ⊥` contains only `0`.
  - Inductive step at `j = n - i - 1`, with `j ∈ S`: `huniq` gives `c` with `x - c • v j ∈ K (j + 1)`. The induction hypothesis expands this difference, and adding `Pi.single j c` to its coefficients expands `x`.
  - Inductive step with `j ∉ S`: `hzero` puts `x` into `K (j + 1)` directly.
- `eq_zero_aux` is upward induction on `i`. If `∑_{j ∈ S} a j • v j ∈ K i`, then `a j = 0` for every `j ∈ S` with `j < i`. For the new index `j₀ = i`:
  - terms with `j < i` vanish by the induction hypothesis (applied after `K (i + 1) ≤ K i`);
  - terms with `j > i` lie in `K (i + 1)`, by `hmem` and the antitonicity of `K` (`Fin.antitone_iff_succ_le`).

  So `a j₀ • v j₀ ∈ K (j₀ + 1)`. Both `a j₀` and `0` then satisfy the defining condition of `huniq` for `x = a j₀ • v j₀`, so `a j₀ = 0`.

For the main theorem, existence applies `exists_expansion_aux` at `i = n`, where `K 0 = ⊤`, and reindexes the `Finset` sum as a sum over the subtype `S`. For uniqueness, extend a second family `b : S → A` by zero to `Fin n → A`. The difference of the two expansions is `0 ∈ K n`, so `eq_zero_aux` at `i = n` shows every coefficient of the difference vanishes.

## The basis

`Langlands.FilteredModule.basisOfFilteredRankOne` takes the same data and hypotheses as `existsUnique_expansion` (the filtration conditions `hanti`, `h0`, `hn` and the hypotheses `hmem`, `huniq`, `hzero`) and defines a basis `Module.Basis S A X`, indexed by the subtype of `S`. Its vectors are `fun j : S => v j`. This is the main definition of the file. The lemma `basisOfFilteredRankOne_apply` records that the basis vector at `j : S` is `v j`.

The definition uses `Module.Basis.mk`, which needs two proofs.
- Linear independence uses `Fintype.linearIndependent_iff`. Suppose `∑_{j : S} g j • v j = 0`. The uniqueness part of `existsUnique_expansion` at `x = 0` says `g` and the zero family are both equal to the unique coefficient family, so `g = 0`.
- Spanning uses the existence part. Every `x` is a sum `∑_{j : S} a j • v j`, and each term lies in the span of the vectors, by `Submodule.sum_mem`, `Submodule.smul_mem` and `Submodule.subset_span`.

## Intended use

`Langlands.RepFunctorFiltration.homVanishing` (`Langlands/Representation/Filtration/HomVanishingFiltration.lean`) is the decreasing filtration of a Hom space by maps vanishing on a natural filtration. The planned application takes `K` to be that filtration and `A` the opposite endomorphism ring of the cuspidal progenerator, acting by precomposition. This file does not prove that application.

# Index comparisons for an aligned spin cover from the weight statements

Authors: Worker 146.

This internal helper module proves `Langlands.GroupScheme.AlignedSpinCoverTitsIndexStatement`
(Task 6282) from three prerequisite statements. It follows the assembly route recorded by
Worker 73 in the context of Task 6282, with one change in step 4, described below. No
outside source is cited beyond those behind the three prerequisites.

## Main result

`Langlands.GroupScheme.alignedSpinCoverTitsIndex_of_weights` has hypotheses

- `h1 : Quaternionic.ConnectedIsometrySplitRankStatement.{u}`: the split rank of
  `O(q)⁰` is the Witt index of `q`;
- `h2 : Quaternionic.IsometryMaximalSplitTorusWeightsStatement.{u}`: every maximal split
  torus `S'` of `O(q)⁰` has linearly independent characters `χ_1, …, χ_r`, with `r` the
  Witt index, such that for every cocharacter `ν` of `S'` and `c ≠ 0` the weight-`c` space
  of `ν` on `D^m` has `D`-dimension `#{(k, s) ∈ Fin r × ℤˣ : s ⟨χ_k, ν⟩ = c}`;
- `h3 : SpinCoverVectorWeightsStatement.{u}`: the vector characters `ε_0, …, ε_{n-1}` of
  the pinning torus over `K^s`, with the simple roots `ε_i − ε_{i+1}` and
  `ε_{n-2} + ε_{n-1}`, and with
  `#{(i, s) : s ⟨ε_i|_S, ν⟩ = c} = degree · finrank_D (weight-c space of ν)` for every
  cocharacter `ν` of `d.splitTorus`.

Its conclusion is `AlignedSpinCoverTitsIndexStatement.{u}`. The star-action hypothesis of
the target is not used. The only axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Imports

The module imports the three prerequisite statements, the published Library results
named below, and `Langlands.Combinatorics.MultiplicityJumps`. The statement
`IsometryMaximalSplitTorusWeightsStatement` is in
`Langlands.GroupScheme.Quaternionic.MaximalSplitTorusWeightsStatement`.

## Helper lemmas

In namespace `Langlands.GroupScheme.AlignedSpinCoverTitsIndex`:

- `comp_injective_of_epi`: if the underlying scheme morphism of a homomorphism
  `f : T ⟶ T'` of commutative group schemes is an epimorphism, then `χ ↦ f ≫ χ` is
  injective on homomorphisms `T' ⟶ H`. Cancel `f` on underlying morphisms, then use
  `CommGroupScheme.hom_ext_points`.
- `add_zsmul_ne_zero`: in a `ℤ`-linearly independent family, `χ k + t • χ l ≠ 0` for
  `k ≠ l`. Apply `linearIndependent_iff'` to the pair `{k, l}` with coefficients `1, t`.

## The proof

Let `r = σ.quadraticWittIndex q` and `S = d.splitTorus`.

1. **Rank.** The spin cover gives a central isogeny `p : G ⟶ O(q)⁰` with
   `p ≫ ι = π` (the field `exists_centralIsogeny` of `IsSpinCover`). By `IsCentralIsogeny.splitRank_eq`
   and `h1`, `splitRank G = r`. This is the first conjunct.
2. **Image torus.** `G` is semisimple, hence connected reductive, and
   `isConnectedReductive_of_isCentralIsogeny` makes `O(q)⁰` connected reductive.
   `exists_maximalSplitTorus_image` gives a maximal split torus `i' : S' ⟶ O(q)⁰` and a
   flat surjective `fS : S ⟶ S'` with `d.splitInclusion ≫ p = fS ≫ i'`. Flatness and
   surjectivity make the underlying morphism of `fS` an epimorphism
   (`Flat.epi_of_flat_of_surjective`).
3. **Characters.** `h2` applied to `S'` gives `χ_1, …, χ_r`. Put `y k = fS ≫ χ_k`, a
   character of `S`, and let `x i = ε_i|_S` be the restriction appearing in `h3`. Then
   `⟨χ_k, ν ≫ fS⟩ = ⟨y k, ν⟩`. By `comp_injective_of_epi` and `add_zsmul_ne_zero`,
   `y k ≠ 0` and `y k + t • y l ≠ 0` for `k ≠ l` and all `t ∈ ℤ`.
4. **Restricted simple roots.** By the first two properties in `h3`, the restriction of
   the simple root of `a` is `x (e a) − x (e a + 1)` when `(e a).val + 1 < n`, and
   `x (n − 2) + x (n − 1)` when `(e a).val + 1 = n`.
5. **A perturbed positive cocharacter.** Let `λ = d.positiveCocharacter`. Instead of the
   genericity argument of the planned route, perturb `λ`. Let `F` be the finite set of
   characters `y k`, `y k + y l` and `y k − y l` for `k ≠ l`, all nonzero by step 3.
   `IsSplitTorus.exists_regular_on_finite` gives a cocharacter `η` pairing nonzero with
   every element of `F`. Let `N` be the bound `IntegralPerturbation.bound` for the finite
   set `F ∪ {restrictions of simple roots}` and `η`, and put `ν = N • λ + η`. By
   `IntegralPerturbation.signs`, for each `α` in this set `⟨α, ν⟩ > 0` exactly when
   `⟨α, λ⟩ > 0`, or `⟨α, λ⟩ = 0` and `⟨α, η⟩ > 0`; and `⟨α, ν⟩ = 0` exactly when both
   pairings vanish. Consequently:
   - `⟨α, ν⟩ ≠ 0` for every `α ∈ F`. So the integers `b k = ⟨y k, ν⟩` are nonzero and
     satisfy `b k ≠ b l` and `b k ≠ −b l` for `k ≠ l`.
   - A simple root with nonzero restriction `α` has `⟨α, λ⟩ > 0` by `d.compatible`,
     since simple roots are positive. Hence `⟨α, ν⟩ > 0`, and `⟨α, ν⟩ ≥ 0` for every
     restricted simple root.
6. **Numerical data.** Put `c i = ⟨x i, ν⟩`. Step 4 and the nonnegativity in step 5
   give `c (j + 1) ≤ c j` for `j + 1 < n` and `0 ≤ c (n − 2) + c (n − 1)`. For `v > 0`
   the two multiplicity statements combine:
   `ν ≫ d.splitInclusion ≫ π = (ν ≫ fS) ≫ i' ≫ ι` by step 2 and `p ≫ ι = π`. So `h3`
   and `h2` (whose correction term vanishes for `v ≠ 0`) give
   `Nat.card {(i, s) : s · c i = v} = degree · Nat.card {(k, s) : s · b k = v}`.
7. **Conclusion.** Let `a` be a vertex with `(e a).val + 2 < n`. It is distinguished
   exactly when its restricted root `x (e a) − x (e a + 1)` is nonzero. By step 5 this
   holds exactly when `c (e a) ≠ c (e a + 1)`: a nonzero restriction pairs positively
   with `ν`, and a zero restriction pairs to zero. The counting lemma
   `Combinatorics.MultiplicityJumps.chain_ne_succ_iff` turns the data of step 6 into the
   criterion `(e a).val + 1 = j · degree` for some `0 < j ≤ r`. This is the second
   conjunct.

The perturbation in step 5 replaces the planned argument that the values
`|⟨χ_k ∘ fS, λ⟩|` are distinct and nonzero. That argument needed the roots
`±ε_i ± ε_j` and had an edge case for `degree = 1`, `r = n`. The cocharacter `ν` pairs
nonzero with `y k` and `y k ± y l` by construction. On the restricted simple roots it
behaves like `λ`: a zero restriction pairs to zero with every cocharacter, and a nonzero
one pairs positively with `ν` because it pairs positively with `λ`.

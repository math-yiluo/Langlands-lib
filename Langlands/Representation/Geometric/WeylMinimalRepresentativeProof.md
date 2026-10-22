# Existence and bijectivity of minimal block Weyl representatives

Author: Worker 243.

This module proves the published proposition
`Langlands.Geometric.WeylMinimalRepresentativeTheorem` from
`Langlands.Representation.Geometric.WeylStatement`. The closed theorem is
`weylMinimalRepresentativeTheorem`. It shows that the actual map
`weylDoubleCoset B C` from `MinimalRepresentatives B C` to
`W_C \ S_n / W_B` is bijective. Here `W_B` and `W_C` are the published
`blockWeyl` subgroups. The map sends a minimal permutation `w` to its double
coset `DoubleCoset.mk (blockWeyl C) (blockWeyl B) w`.

Minimality keeps both conditions from `WeylDefinitions`: `w` is strictly
increasing on each source block of `B`, and `w⁻¹` is strictly increasing on
each target block of `C`. The published statement assumes `0 < n`. The proof
does not use this hypothesis: `weylDoubleCoset_bijective` holds for every
natural rank.

Injectivity is not proved here. It is Worker 175's published theorem
`weylDoubleCoset_injective` from
`Langlands.Representation.Geometric.WeylUniquenessProof`, imported by Lean
name. This module proves existence, that is surjectivity, and then combines
the two.

## Reusable interface

- `index_strictMono B i`: the coordinates `B.index i` of one block are
  strictly increasing.
- `blockPermOf B σ`: the permutation of `Fin n` that applies `σ i` inside
  block `i`. `blockPermOf_index` evaluates it on block coordinates, and
  `blockPermOf_mem_blockWeyl` shows that it lies in `blockWeyl B`.
- `exists_blockWeyl_monotone_labels B C w`: some `b ∈ blockWeyl B` makes the
  target-block labels `blockIndex C (w (b x))` monotone on every source
  block.
- `exists_blockWeyl_strictMono C u`: some `c ∈ blockWeyl C` makes
  `u ∘ c` strictly increasing on every target block.
- `lt_of_blockIndex_le C hv`: suppose `v⁻¹` is strictly increasing on every
  target block, and `a < a'` satisfy
  `blockIndex C (v a) ≤ blockIndex C (v a')`. Then `v a < v a'`.
- `exists_minimal_mem_doubleCoset B C w`: some minimal `v` has the form
  `c * w * b` with `c ∈ blockWeyl C` and `b ∈ blockWeyl B`.
- `weylDoubleCoset_surjective B C` and `weylDoubleCoset_bijective B C`.

## Implemented proof

The proof uses only finite permutations of block coordinates. It does not
use the Coxeter-group argument cited in BZ77, section 6.3.

**Block permutations.** `blockPermOf B σ` conjugates
`Equiv.sigmaCongrRight σ` by the published coordinate equivalence
`B.indexEquiv`. It maps `B.index i a` to `B.index i (σ i a)`. The lemma
`blockIndex_index` from `WeylDefinitions` then shows that it preserves every
block label, so it lies in `blockWeyl B`. Strict monotonicity of `B.index i` comes from
unfolding `B.indexEquiv` into its partial-sum formula `finSigmaFinEquiv`.

**First sorting step.** Fix `w`. On source block `i`, consider the tuple
`x ↦ blockIndex C (w (B.index i x))`. Mathlib's `Tuple.sort` gives a
permutation of `Fin (B.size i)` that sorts this tuple
(`Tuple.monotone_sort`). Doing this in each block gives
`b = blockPermOf B (fun i => Tuple.sort _)` in `blockWeyl B`. After `b`, the
target-block labels of `w * b` are monotone on every source block.

**Second sorting step.** Now apply the same construction to `u = (w * b)⁻¹`
on the target blocks of `C`. On target block `j`, sort the tuple
`y ↦ u (C.index j y)`. The resulting `c ∈ blockWeyl C` makes `u ∘ c`
monotone on each target block. Since `u ∘ c` is injective, this is strict
monotonicity.

**The representative.** Let `v = c⁻¹ * w * b`. The group identity
`v⁻¹ = (w * b)⁻¹ * c` shows that `v⁻¹` restricted to each target block is
exactly the strictly increasing map from the second step. This is the
target-block condition.

Because `c⁻¹` lies in `blockWeyl C`, it preserves target-block labels. Hence
`blockIndex C (v a) = blockIndex C (w (b a))` for every `a`. Take
`x < x'` in source block `i` and set `a = B.index i x`, `a' = B.index i x'`.
Then `a < a'` by `index_strictMono`. The first step gives
`blockIndex C (v a) ≤ blockIndex C (v a')`.

Lemma `lt_of_blockIndex_le` now gives `v a < v a'`. Suppose instead that
`v a' ≤ v a`. The lemma `blockIndex_monotone` from `WeylUniquenessProof`
makes the two target labels equal, say both equal to `j`. Then
`exists_index_of_blockIndex_eq`, from the same module, writes
`v a = C.index j y` and `v a' = C.index j y'`. Here `y' ≤ y`, since
`C.index j` is strictly monotone. The target-block condition makes `v⁻¹`
monotone on block `j`, so `a' ≤ a`, a contradiction. Thus `v` is strictly
increasing on every source block, and `v` is minimal.

**Surjectivity and bijectivity.** Let `q` be a double coset and `w` the
representative `q.out`. The construction gives a minimal
`v = c * w * b` with `c ∈ blockWeyl C` and `b ∈ blockWeyl B`. Mathlib's
`DoubleCoset.eq` applied to `c⁻¹` and `b⁻¹` shows that `v` and `w` have the
same double coset. `DoubleCoset.out_eq'` identifies the latter with `q`. So
`weylDoubleCoset B C` is surjective. Together with the published
`weylDoubleCoset_injective`, it is bijective. Discarding the unused
hypothesis `0 < n` gives `weylMinimalRepresentativeTheorem`.

## Source and provenance

Bernstein and Zelevinsky, *Induced representations of reductive p-adic
groups I* (1977), Lemma 2.11(a), printed page 448 (PDF page 9). It states
that each double coset `W_N \ W / W_M` contains a unique element of
`W^{M,N} = { w | w(M ∩ P₀) ⊂ P₀, w⁻¹(N ∩ P₀) ⊂ P₀ }`, where `P₀` is the
standard minimal parabolic. Here `M` is the source Levi of `B` and `N` the
target Levi of `C`. For `GL_n` the two inclusions are the two within-block
monotonicity conditions in `IsMinimalRepresentative`, as the published
`WeylStatement` Markdown explains. The proof in section 6.3, printed page 468 (PDF page 29), cites
Bourbaki's Coxeter-group exercise. The two-sorting argument above is an
internal replacement for that citation in type A. Literature ID:
`bernstein-zelevinsky-1977-induced-i`.

The published `WeylDefinitions` and `WeylStatement` pairs are used without
modification.

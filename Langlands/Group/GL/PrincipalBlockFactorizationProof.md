# Positive principal congruence block factorization

Author: Worker 204.

The theorem `Langlands.GeneralLinear.BlockShape.principalBlockFactorization.{u}`
in the module `Langlands.Group.GL.PrincipalBlockFactorizationProof` proves
exactly the published proposition
`Langlands.GeneralLinear.BlockShape.PrincipalBlockFactorizationStatement.{u}`
from `Langlands.Group.GL.PrincipalBlockFactorizationStatement`. It has no
additional premises, and the field universe `u` remains arbitrary. The field
`k` with its supplied `Field`, `ValuativeRel`, `TopologicalSpace` and
`IsNonarchimedeanLocalField` instances, the rank `n`, the ordered block shape
`B : GeneralLinear.BlockShape (n + 1)`, the level `a` and the proof of `0 < a`
are all quantified by that proposition. One-block shapes and rank one
(`n = 0`) are covered by the same argument, with no case split. The module
imports the statement module and two Mathlib modules:
`Mathlib.LinearAlgebra.Matrix.SchurComplement`, for the block-matrix and
invertible-matrix API, and `Mathlib.Tactic.Group`, for the `group` tactic.
No imported Library Lean/Markdown pair is changed.

## Public API

All declarations are in the namespace `Langlands.GeneralLinear.BlockShape`.

* `iwahoriProduct_injective (B : GeneralLinear.BlockShape n) (R : Type v)
  [CommRing R] (K : Subgroup (GeneralLinear n R))`, with `n` implicit, has
  type `Function.Injective (B.iwahoriProduct R K)`. Uniqueness holds for every
  commutative ring, every rank and every subgroup `K`.
* `principalLevelSubgroup_iwahoriProduct_surjective (k : Type u) [Field k]
  [ValuativeRel k] (n : ℕ) (B : GeneralLinear.BlockShape (n + 1)) (a : ℕ)
  (ha : 0 < a)` has type
  `Function.Surjective (B.iwahoriProduct k (Langlands.Conductor.principalLevelSubgroup k n a))`.
* `principalLevelSubgroup_iwahoriProduct_bijective`, with the same arguments,
  gives the corresponding `Function.Bijective`. It is the directly usable
  specialization `principalLevelSubgroup_iwahoriProduct_bijective k n B a ha`.
* `principalBlockFactorization : PrincipalBlockFactorizationStatement.{u}`
  introduces the quantified data and applies the bijectivity theorem.

The last theorem does not use the supplied topology or the
`IsNonarchimedeanLocalField` instance. The bijectivity theorem holds for
every field with a valuative relation. Its type uses the same
`ValuativeRel.valuation k`, integer ring and maximal ideal as the published
`principalLevelSubgroup`; no other valuation or topology is introduced.

## Units from congruence

Throughout, `R` is a commutative local ring and `J` is an ideal contained in
its maximal ideal. Congruence to the identity means that
`M x y - (1 : Matrix ι ι R) x y ∈ J` for all entries.

The private theorem `isUnit_det_of_congr` shows that such a square matrix
`A` has a unit determinant. The images of `A` and `1` under reduction
modulo `J` coincide. Since the determinant commutes with this ring
homomorphism, `det A - 1 ∈ J`. If `det A` were not a unit, it would lie in
the maximal ideal. Then `1 = det A - (det A - 1)` would lie in the maximal
ideal as well, which is impossible.

## Block elimination

The private theorem `exists_blockLDU` works over a finite index type `ι` with
decidable equality, a linear order `α` and a block function `b : ι → α`. If
`M` is congruent to the identity modulo `J`, it gives matrices `L`, `D` and
`U` with `M = L * D * U` and the following entry conditions for all `x`
and `y`:

* `L x y = 0` when `b x < b y`, and `L x y = (1 : Matrix ι ι R) x y` when
  `b x = b y`;
* `D x y = 0` when `b x ≠ b y`;
* `U x y = 0` when `b y < b x`, and `U x y = (1 : Matrix ι ι R) x y` when
  `b x = b y`;
* each of `L`, `D` and `U` is congruent to the identity modulo `J`.

The proof is by strong induction on `N = Fintype.card ι`, for every index type
of that cardinality. If `ι` is empty, all three factors are `1`. Otherwise
`Finite.exists_min` gives `x₀` minimizing `b`. Let `p x` mean `b x = b x₀`:
this is the fibre of the first block present. `Equiv.sumCompl p` identifies
`{x // p x} ⊕ {x // ¬p x}` with `ι`. Reindexing `M` along it and applying
`toBlocks` gives blocks `A`, `B₁`, `C` and `D₁`. Since the two index sets are
disjoint, `A` and `D₁` are congruent to the identity, and `B₁` and `C` have
all entries in `J`.

By `isUnit_det_of_congr`, `A` is invertible over `R`; the proof uses
`invertibleOfIsUnitDet`. The products `C * ⅟A` and `⅟A * B₁` have entries in
`J`, since each entry is a sum of products with a factor in `J`. Hence
`C * ⅟A * B₁` also has entries in `J`, and the Schur complement
`S = D₁ - C * ⅟A * B₁` is congruent to the identity. The complement
`{x // ¬p x}` omits `x₀`, so its cardinality is smaller. The induction
hypothesis therefore applies to `S`, with the restricted block function, and
gives `S = L₂ * D₂ * U₂` with the listed properties. Block multiplication
(`fromBlocks_multiply` and cancellation of `⅟A`) proves

```text
fromBlocks A B₁ C D₁ =
  fromBlocks 1 0 (C * ⅟A) L₂ * fromBlocks A 0 0 D₂ * fromBlocks 1 (⅟A * B₁) 0 U₂.
```

Reindexing back along the inverse equivalence (`submatrix_mul_equiv`) gives
the three factors of `M`. The entry conditions are checked separately on the
four block positions. Inside the first fibre, `b` values are equal and the
outer factors have identity entries. In the upper-right position, `b x₀ < b y`.
Here `L` and the identity both vanish, and the entry of `U` comes from
`⅟A * B₁`, which lies in `J`. The lower-left position is symmetric, with
`b y = b x₀ < b x`; there the entry of `L` comes from `C * ⅟A`. On the
complement, the conditions are those of the induction hypothesis. The
congruence of `D` on the first fibre is the congruence of `A`.

## Uniqueness in any subgroup

Membership is read in block coordinates `B.index i r`. A private
extensionality lemma, `ext_index`, uses surjectivity of `B.indexEquiv`. The
published `mem_parabolic_iff`, `mem_oppositeParabolic_iff`,
`mem_unipotentSubgroup_iff` and `mem_oppositeUnipotentSubgroup_iff` describe
the subgroups entrywise. `leviEmbedding_apply_ne` gives the zero
off-diagonal blocks of the embedded Levi.

* `eq_one_of_mem_opposite_of_mem_parabolic`: an element of the opposite radical
  lying in the upper parabolic is `1`. Blocks with `i < j` vanish by the
  opposite parabolic condition. Diagonal blocks are identity blocks by the
  opposite radical condition. Blocks with `j < i` vanish by the parabolic
  condition.
* `eq_one_of_mem_levi_of_mem_unipotent`: an element of the common Levi lying in
  the upper radical is `1`. Its diagonal blocks are identity blocks, and its
  off-diagonal blocks vanish.
* The Levi and the upper radical are contained in the parabolic.

For `iwahoriProduct_injective`, suppose `l₁ * m₁ * u₁ = l₂ * m₂ * u₂`. A
`group` computation gives `l₂⁻¹ * l₁ = m₂ * u₂ * u₁⁻¹ * m₁⁻¹`. The left side
lies in the opposite radical, and the right side lies in the parabolic. Hence
`l₁ = l₂`. Cancelling gives `m₁ * u₁ = m₂ * u₂`. Then
`m₂⁻¹ * m₁ = u₂ * u₁⁻¹` lies in both the Levi and the upper radical, so
`m₁ = m₂`, and finally `u₁ = u₂`. Only these subgroup intersections are used;
no property of `K` beyond its being a subgroup is needed.

## Existence in the principal subgroup

The proof of `principalLevelSubgroup_iwahoriProduct_surjective` sets
`O = (ValuativeRel.valuation k).integer`, a local ring, and
`I = (IsLocalRing.maximalIdeal O) ^ a`. Since `a ≠ 0`, `Ideal.pow_le_self`
gives `I ≤ IsLocalRing.maximalIdeal O`; this is the only use of positivity.

An element `x` of `principalLevelSubgroup k n a` is, by the published
definition, the image under `GeneralLinearGroup.map O.subtype` of some
`g ∈ integralPrincipalCongruence n I`. The published
`mem_integralPrincipalCongruence` gives entrywise congruence of `g` to the
identity modulo `I`. The elimination theorem is applied with `ι = Fin (n + 1)`
and the block function `x ↦ (B.indexEquiv.symm x).1`, the block index of a
standard coordinate. No reindexing of `GL_(n+1)` is needed. The three
resulting matrices are congruent to the identity, so `isUnit_det_of_congr`
makes them invertible integral matrices `l`, `d` and `u`.
`GeneralLinearGroup.mk''` constructs them, and `g = l * d * u` holds in
`GL (Fin (n + 1)) O`.

By `map_mem_principalCongruenceSubgroup` and
`mem_integralPrincipalCongruence`, the images of `l`, `d` and `u` lie in the
same principal subgroup at level `a`. The ring homomorphism `O → k` preserves
zero entries (`map_zero`) and identity entries (the private
`ringHom_one_apply`). Three private lemmas then translate the entry conditions
into the subgroups, after converting block coordinates with
`B.indexEquiv.symm (B.index i r) = ⟨i, r⟩`:

* `mem_oppositeUnipotentSubgroup_of_entries` handles lower block-triangular
  matrices with identity diagonal blocks.
* `mem_leviSubgroup_of_entries` handles block-diagonal matrices. Such a matrix
  lies in the parabolic and equals the Levi embedding of its
  `leviProjection`.
* `mem_unipotentSubgroup_of_entries` handles upper block-triangular matrices
  with identity diagonal blocks.

Thus the images of `l`, `d` and `u` lie in the published `iwahoriLower`,
`iwahoriLevi` and `iwahoriUpper` of the principal subgroup.
`GeneralLinearGroup.map` is a monoid homomorphism. Hence their ordered product
is the image of `g`, that is, `x`. This is the existence part. It produces the
actual opposite-radical, common-Levi and upper-radical factors, in that order,
inside the same positive principal subgroup.

## Provenance and validation boundary

This is a derived proof for the concrete `GL_(n+1)` principal subgroups of the
Library; the literature does not contain it in this form. Its motivating
source is Bill Casselman, *Introduction to admissible representations of
p-adic groups*, Chapter III, *Induced representations and the Jacquet module*,
revision April 29, 2019, section 4, PDF and printed page 5. The registered
source is `casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`, retained at
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.
I read that page for this proof. It defines Iwahori factorization, with
condition (a) requiring bijectivity of the product map in the
opposite-radical, Levi, upper-radical order. The PDF text extraction omits
the overbar on the opposite radical; the order used here is that of the
published statement. In the split case, the proof of Lemma III.4.1 asserts
that the congruence subgroups `G(p^n)`, `n ≥ 1`, satisfy the lemma. It cites
Iwahori–Matsumoto and gives no elimination argument. No source-specific
project errata file was found. The local-ring Schur-complement elimination
and the intersection argument above are the implemented Lean proof; they are
not taken from the source. Casselman's contraction conditions and
neighbourhood-basis assertion are not part of this theorem.

The complete module passes Lean-service compilation with zero errors and
zero warnings. Inspection of `principalBlockFactorization` reports a theorem
with universe parameter `u`, depending only on `propext`, `Classical.choice`
and `Quot.sound`. Independent semantic review, Lake build, the official
exact-target check and publication are separate submission requirements.

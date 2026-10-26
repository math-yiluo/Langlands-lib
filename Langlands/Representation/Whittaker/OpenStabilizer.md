# The block-reversal stabilizer and its product character

Author: Worker 176.

## Scope and conventions

For a field `K : Type u`, a natural number `n`, and an ordered positive block shape `B : BlockShape n`, put `P = B.parabolic K`, `U = upperUnipotent n K`, and `w = (B.reverseMatrix K)⁻¹`. The construction works at every natural rank, including the positive ranks required by the application. It uses the existing permutation that reverses whole blocks and preserves each position inside a block.

`openStabilizer B K` is the actual subgroup carrier `Geometric.orbitStabilizer P U w`. Thus an element `q` is an upper unipotent matrix with `w⁻¹ * q * w ∈ P`. This is the convention for the orbit `P * w⁻¹ * U`. The name records the intended representative; the file proves neither openness of this orbit nor any induction or representation-theoretic theorem.

## The explicit group equivalence

`openStabilizerEquiv B K` constructs the multiplicative equivalence

```lean
openStabilizer B K ≃* (∀ i, upperUnipotent (B.size i) K)
```

Its forward map is the family of actual diagonal blocks of `B.leviProjection K (Geometric.stabilizerToInducing P U w q)`. To prove that these blocks are upper unipotent, the code transports entries through `reverseMatrix_conjugate_entry`, uses strict monotonicity of the consecutive coordinates within each block, and retains the diagonal entries equal to one.

Conjugation carries `q` to a block diagonal matrix in the original block order. Entries strictly below its block diagonal vanish by parabolic membership. Entries strictly above its block diagonal correspond to entries strictly below the diagonal of `q`, since the block order was reversed, so they also vanish. Consequently the Levi embedding of its Levi projection is exactly the conjugated matrix.

The inverse sends a family `m` of upper unipotent block matrices to

```lean
(B.reverseMatrix K)⁻¹ * B.leviEmbedding K (fun i => (m i).val) * B.reverseMatrix K
```

The proof checks upper unipotence entry by entry in the reversed block coordinates. Different blocks give zero entries; within one block the required triangularity and diagonal conditions come from `m`. Conjugating back gives the actual block diagonal matrix in `P`, proving stabilizer membership. The two inverse laws follow respectively from the block diagonal reconstruction and the existing Levi projection/section identity. No inverse map or bijectivity is assumed.

The exported laws `openStabilizerEquiv_apply_val`, `openStabilizerEquiv_symm_apply_val`, and `openStabilizerEquiv_leviProjection` state the forward formula, inverse matrix formula, and equality of the complete Levi family. They use the existing subgroup carriers and original block indexing.

## Exact character formula

For every raw additive character `ψ : AddChar K ℂ`, `openStabilizerEquiv_character` proves an equality in `ℂˣ`:

```lean
entrywiseCharacter ψ n q.val =
  ∏ i, entrywiseCharacter ψ (B.size i) (openStabilizerEquiv B K q i)
```

The proof first uses the published all-ranks double-product evaluation of `entrywiseCharacter`. A private finite-product lemma reindexes the two matrix indices by the sigma type of block coordinates. Off-block entries are zero, so the corresponding factors are `ψ 0 = 1`. In a single consecutive block, two global indices are adjacent exactly when their internal indices are adjacent. The surviving factors therefore give the character of each diagonal block. Finally, reindexing the outer product by `Fin.revPerm` restores the original order of the blocks. Equality of complex values gives equality of units. This proof introduces no inverse character, transformed additive character, or reversal within a block, and imposes no continuity or unitarity on `ψ`.

## Minimality and topology

`reversePermutation_isMinimalRepresentative` proves

```lean
Geometric.IsMinimalRepresentative B (BlockShape.singletons n) B.reversePermutation.symm
```

The first clause follows from `reversePermutation_symm_index` and strict monotonicity of each reversed-shape block inclusion. The second clause is vacuous because every singleton block has only one coordinate. This is an intrinsic permutation statement, not a geometric openness assertion.

With `[TopologicalSpace K] [IsTopologicalRing K]`, `openStabilizerContinuousEquiv` constructs the corresponding continuous multiplicative equivalence for the actual subgroup and product topologies. Forward continuity is conjugation followed by the continuous Levi projection, coordinate evaluation, and subtype construction. Inverse continuity is the continuous family of underlying block matrices followed by the continuous Levi embedding, multiplication by the two fixed permutation matrices, and the subgroup inclusions. `openStabilizerContinuousEquiv_toMulEquiv` identifies its underlying multiplicative equivalence with `openStabilizerEquiv`. No local compactness, Haar measure, topological-field inversion hypothesis, or representation carrier is used.

## Derived provenance

The source context is F. Rodier, *Modèles de Whittaker des représentations admissibles des groupes réductifs p-adiques quasi-déployés*, the author manuscript described as a modified 1975 form, Chapter V.2, Lemma 6 and the proof of Theorem 4, PDF pages 36–42. These pages were read visually. The registered source is `rodier-whittaker-author-manuscript`, content SHA256 `8c110b6b626108ec67421f288baa4b761a8073df2c68db6be8360b654f569812`. No source-specific erratum was found in the current Library, project notes, or literature files.

Rodier uses the longest Weyl element and a transformed Levi character in the open-cell argument. The representative here reverses only whole blocks and preserves their internal positions. Its exact character formula is proved directly from these coordinates. The arbitrary-field scope, all-ranks convention, named subgroup equivalence, and topological interface are derived internal constructions from the published `ReverseBlocks`, `Blocks`, `SingletonBlocks`, `EntrywiseCharacter`, and geometric stabilizer definitions; they are not asserted to be literal formulations in Rodier. No conclusion about heredity, admissibility, irreducibility, or Whittaker functional spaces is deduced in this file.

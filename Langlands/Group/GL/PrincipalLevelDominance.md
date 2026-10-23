# Principal levels in every rank and dominant torus sandwiches

This module supplies the group-theoretic facts about `GL_m` over a valued field
that the proof of Bernstein--Zelevinsky (1976), Lemma 4.9, page 39, uses for
each block of `G°`. They concern the principal congruence subgroups
("principal levels") and the dominant part of the diagonal torus. BZ76 uses
these facts there without separate statements. Throughout, `k` is a field with
a valuative relation, `O` is its valuation ring
`(ValuativeRel.valuation k).integer`, and `Iwasawa.torus ϖ lam` is the diagonal
matrix with entries `ϖ ^ lam i`.

## Conjugation lemmas (copied)

The private declarations `EntryIdeal`, `entryIdeal_upper_conj`,
`entryIdeal_lower_inv_conj`, `principal_upper_conj` and
`principal_lower_inv_conj` are copied verbatim from the private section of the
published module `Langlands.Group.GL.BlockIwahoriBasis`. They are private
there and cannot be imported. They state the following. Let `a` be block
scalars with `a i / a j ∈ O` for `i < j`. Conjugating a block-upper unipotent
element of a principal congruence subgroup by `diag(a)` stays in that
subgroup, and so does conjugating a block-lower unipotent element by
`diag(a)⁻¹`. The proofs compare entries, using the published
`BlockShape.blockScalar_conj_apply`, `BlockShape.blockScalar_inv_conj_apply`
and `Conductor.mem_principalCongruenceSubgroup_iff`.

## Principal levels in every rank

- `eq_one_of_rank_zero`: `GL_0(k)` is trivial.
- `rankPrincipalLevel k m a`: the image in `GL_m(k)` of the kernel of reduction
  modulo `𝔪 ^ a` on `GL_m(O)`. It is defined uniformly in `m`, because the
  block sizes of a block shape are not syntactically successors.
  - `rankPrincipalLevel_succ`: for `m = n + 1` it is, by definition, the
    published `Conductor.principalLevelSubgroup k n a`.
  - `rankPrincipalLevel_le_integralRange`: it consists of integral matrices,
    that is, it lies in `Iwasawa.integralRange`.
  - `rankPrincipalLevel_antitone`: it decreases as `a` grows. Rank zero is
    trivial; positive rank is `principalLevelSubgroup_antitone`.
- `conj_mem_rankPrincipalLevel`, `conj_mem_rankPrincipalLevel_iff`: integral
  matrices normalize every principal level, because it is the image of a
  kernel, which is normal in `GL_m(O)`.

## Torus elements

- `torus_add`, `torus_zero`, `torus_commute`: the torus is a homomorphism in
  the exponent, so torus elements commute.
- `torus_eq_blockScalar`: `Iwasawa.torus ϖ lam` is the block scalar
  `(BlockShape.singletons (n + 1)).blockScalar k (fun i => ϖ ^ lam i)`, using
  `BlockShape.leviEmbedding_singletonLevi_val`.
- `ratio_mem_integer`: if `v(ϖ) ≤ 1` and `lam` is antitone, then
  `ϖ ^ lam i / ϖ ^ lam j ∈ O` for `i < j`.

## Dominant sandwich

`exists_dominant_sandwich ha hϖ h₁ h₂ hg`: assume `0 < a`, `v(ϖ) ≤ 1`, `lam₁`
and `lam₂` antitone, and `g` in the principal level `P` of level `a`. Then
`ϖ^lam₁ g ϖ^lam₂ = x (ϖ^lam₁ ϖ^lam₂) y` for some `x, y ∈ P`.

Proof. Rank zero is trivial. In rank `n + 1`, write `δᵢ = ϖ^lamᵢ`.

1. Factor `g⁻¹ = l d u` by the published principal-level Iwahori
   factorization `BlockShape.principalLevelSubgroup_iwahoriProduct_surjective`
   for the singleton block shape. This needs `0 < a`. Here `l` is lower
   unipotent, `d` is diagonal and `u` is upper unipotent, all in `P`.
2. Then `g = u⁻¹ d⁻¹ l⁻¹`, and `d⁻¹` commutes with `δ₁`, since both are block
   scalars of the singleton shape (`blockScalarLevi_commute`).
3. Hence `δ₁ g δ₂ = (δ₁ u⁻¹ δ₁⁻¹ d⁻¹) (δ₁ δ₂) (δ₂⁻¹ l⁻¹ δ₂)`.
4. `δ₁ u⁻¹ δ₁⁻¹ ∈ P` by `principal_upper_conj`, and `δ₂⁻¹ l⁻¹ δ₂ ∈ P` by
   `principal_lower_inv_conj`. The ratio hypotheses come from
   `ratio_mem_integer`.

## Topology over a nonarchimedean local field

Here `k` is a nonarchimedean local field.

- `isOpen_rankPrincipalLevel`, `isCompact_rankPrincipalLevel`: principal levels
  are open and compact. Positive rank uses the published
  `Conductor.principalLevelOpenSubgroup` and
  `isCompact_principalLevelOpenSubgroup`.
- `isCompact_integralRange`: `GL_m(O)` is compact. It is the principal level of
  level `0` (`principalLevelSubgroup_zero`).
- `exists_pos_rankPrincipalLevel_subset`: every identity neighborhood contains
  a principal level of positive level. Positive rank uses the published
  `exists_pos_principalLevelOpenSubgroup_subset`.

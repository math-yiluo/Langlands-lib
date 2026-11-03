# Proof of the finite-index restriction of rational characters to a split component

Authors: Worker 1236 and Worker 934. Worker 934 wrote and checked the proof
term in the task context of task `7876f742-af37-4881-beed-1f05b008c82f`;
Worker 1236 wrote this module and its Markdown.

This file proves the published proposition
`Langlands.GroupScheme.CharacterRestrictionFiniteIndexStatement`
(in [`CharacterRestrictionFiniteIndexStatement`](CharacterRestrictionFiniteIndexStatement.md))
as the theorem

```lean
theorem Langlands.GroupScheme.characterRestrictionFiniteIndexStatement :
    CharacterRestrictionFiniteIndexStatement.{u}
```

for every universe `u`. The statement is used unchanged. It says: over every
field `k : Type u`, for every `G : GroupScheme (Spec (CommRingCat.of k))` with
`IsConnectedReductive G`, every commutative group scheme `A` over `k` and every
`i : A.toGrp ⟶ G` with `IsSplitComponent i`, the range of
`characterRestrict i : X^*(G)_k → X^*(A)` has finite index
(`AddSubgroup.FiniteIndex`). The proof adds no perfectness, characteristic,
splitness, local-field or algebraic-closedness hypothesis. It does not use
`CharacterRestrictionStatement`, injectivity of `characterRestrict i`, or any
consumer target.

## The proof

The proof is the term

```lean
fun _ _ _ hG _ _ hi => hi.finiteIndex_range_characterRestrict hG
```

It introduces the field `k`, its `Field` instance, the group `G`, the
hypothesis `hG : IsConnectedReductive G`, the group `A`, the homomorphism `i`
and the hypothesis `hi : IsSplitComponent i`. It then applies the published
theorem

```lean
theorem Langlands.GroupScheme.IsSplitComponent.finiteIndex_range_characterRestrict
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) {A : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : A.toGrp ⟶ G} (hi : IsSplitComponent i) :
    (characterRestrict i).range.FiniteIndex
```

from [`CharacterRestrictionFiniteIndex`](CharacterRestrictionFiniteIndex.md)
(author Worker 1001). Its conclusion is the conclusion of the statement
verbatim, so no conversion is needed.

## The finite-index argument used

The applied theorem, as recorded in its own Markdown, works as follows.

- It takes the field `IsConnectedReductive.isAffineHom` of `hG`, and gets
  `LocallyOfFiniteType G.X.hom` from the field `IsConnectedReductive.smooth`.
  It takes `IsCentralSplitTorus i` from `IsSplitComponent.isCentralSplitTorus`
  (in [`Characters`](Characters.md)). Then it calls the more general
  `CharacterRestrictionFiniteIndex.finiteIndex_range_characterRestrict`. That
  theorem needs only that `G` is affine and locally of finite type over `k` and
  that `i` is a central split torus. It does not use reductivity,
  connectedness, smoothness itself, or the maximality in `IsSplitComponent`.
- The general theorem embeds `G` in some `GL_N` by the Library's
  `affineLinearEmbeddingStatement` (Milne, *Algebraic Groups*, Theorem 4.9).
  The split torus `𝔾_m^J ≅ A` then acts through `GL_N`, and this action
  decomposes `k^N` into weight blocks. Because `i` is central, each block
  projector commutes with `G`. So the determinant of `G` acting on the block of
  weight `m` and dimension `d_m > 0` is a rational character of `G`. Its
  restriction to `𝔾_m^J` is `d_m • m` under `X^*(𝔾_m^J) ≃ ℤ^J`.
- The weights `m` that occur generate `ℤ^J`, because the composite
  `𝔾_m^J ⟶ G ⟶ GL_N` is a monomorphism. Let `D` be the product of the block
  dimensions. Then `D • X^*(A)` lies in the range of `characterRestrict i`,
  after transport along `A ≅ 𝔾_m^J`. Since `X^*(A)` is finitely generated, the
  quotient by the range is finite.

## Dependencies

- Statement: `CharacterRestrictionFiniteIndexStatement`
  (`Rational/CharacterRestrictionFiniteIndexStatement`), with its imports
  `Rational/Characters` (`characterRestrict`, `IsSplitComponent`) and
  `Reductive/Basic` (`IsConnectedReductive`).
- Proof: `IsSplitComponent.finiteIndex_range_characterRestrict`
  (`Rational/CharacterRestrictionFiniteIndex`) and the declarations it uses;
  that module's Markdown lists them.

The theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Source

The statement is the finite-index part of the Lemme in Renard,
*Représentations des groupes réductifs p-adiques* (French version of
9 July 2026), source `renard-2026-representations-groupes-reductifs-padiques`,
SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
V.2.6, printed p.108 (PDF p.114). Renard works over a nonarchimedean local
field. His proof compares `X^*(G)` with the character group of the torus
`G/𝒟G`. The Lean proof does not follow that route; it uses the
representation-theoretic argument above. That argument needs no local-field
hypothesis, which is why the statement holds over every field, as its
Markdown records.

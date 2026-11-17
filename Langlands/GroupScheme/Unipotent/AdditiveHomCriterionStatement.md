# Unipotence through homomorphisms to the additive group

`Langlands.GroupScheme.UnipotentAdditiveHomCriterionStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy
`[LocallyOfFiniteType G.X.hom]` and `[IsAffineHom G.X.hom]`. The proposition
says

```text
IsUnipotent G ↔
  ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G), IsClosedSubgroup i →
    SubgroupFunctor.range i ≠ ⊥ →
      Nontrivial (H ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)
```

In words, an affine algebraic group over `k` is unipotent exactly when every
nontrivial closed subgroup of it has a nontrivial homomorphism to the
additive group `𝔾ₐ`.

The ingredients are existing declarations, used without change.

- `IsUnipotent G` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that every nonzero finite-dimensional matrix representation of `G` has a
  nonzero fixed vector.
- `IsClosedSubgroup i` (from [`Reductive.Basic`](../Reductive/Basic.md))
  says that the underlying morphism of schemes of the homomorphism `i` is a
  closed immersion.
- `SubgroupFunctor.range i` (from
  [`SubgroupFunctor`](../SubgroupFunctor.md)) assigns to each scheme `T` over
  `Spec k` the subgroup of `G(T)` of points that factor through `i`. The
  bottom element `⊥` assigns the trivial subgroup to every `T`.
- `VectorGroup.groupScheme (CommRingCat.of k) 1` (from
  [`VectorGroupQuotient`](../VectorGroupQuotient.md)) is the vector group
  `𝔾ₐ¹ = Spec k[T]` over `Spec k`, with the additive group law.
- `Nontrivial (H ⟶ 𝔾ₐ)` (Mathlib) says that there are two different
  homomorphisms `H ⟶ 𝔾ₐ` of group schemes.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Proposition 14.22, p.285: "An algebraic group G is unipotent if and only
  if every nontrivial algebraic subgroup of it admits a nontrivial
  homomorphism to Ga."
- Chapter 14 opening, p.279: "Recall that all algebraic groups are affine
  over a base field k."
- 6.45, p.135: "An algebraic group G is said to be unipotent if every nonzero
  representation of G has a nonzero fixed vector."
- p.7, before Definition 1.3: "An algebraic group G is trivial if e: ∗ → G is
  an isomorphism, and a homomorphism G → G′ is trivial if it factors through
  e′: ∗ → G′."
- Definition 1.3, p.7: "An algebraic subgroup of an algebraic group (G, m_G)
  over k is an algebraic group (H, m_H) over k such that H is a k-subscheme
  of G and the inclusion map is a homomorphism of algebraic groups."
- Proposition 1.41, p.18: "Algebraic subgroups of algebraic groups are closed
  (in the Zariski topology)."
- p.8: "The functor R ⇝ (R, +) is represented by Spm(k[T]), and hence is an
  algebraic group Ga."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Proposition 14.22 on
printed p.285 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for printed pp.274–316. The 2017
errata have no entry for pp.7, 8 or 135. Their p.18 entry concerns the proof
of 1.40, not Proposition 1.41. The 2022 errata add a sentence after
Definition 1.3: the identity section `e → G` factors through `H` and gives
`H` a neutral element. This does not change the definition.

Milne's proof: every algebraic subgroup of a unipotent group is unipotent
(14.7), and a nontrivial unipotent group has a nontrivial homomorphism to
`Ga` by its central series (14.21). Conversely, take a nontrivial
homomorphism `G → Ga` with kernel `G₁`, then one on `G₁` if `G₁ ≠ e`, and so
on. The descending chain condition on algebraic subgroups (1.42) ends the
series at `e`. Its quotients are algebraic subgroups of `Ga`, so `G` is
unipotent by 14.7. This is explanation only. The statement does not depend
on that route.

## Derivation from the source

- **Algebraic group.** Milne's algebraic group is a group scheme of finite
  type over `k`, and by the Chapter 14 convention it is affine. The
  instances `LocallyOfFiniteType G.X.hom` and `IsAffineHom G.X.hom` say this.
  An affine morphism is quasi-compact, so `G` is of finite type over `k`.
- **Algebraic subgroups.** By Definition 1.3 and Proposition 1.41, an
  algebraic subgroup of `G` is a closed subscheme that is a subgroup. The
  statement quantifies over all homomorphisms `i : H ⟶ G` whose underlying
  morphism is a closed immersion. Each algebraic subgroup is presented by its
  inclusion, and each such `i` identifies `H` with an algebraic subgroup of
  `G`, its image. `H` need not be assumed of finite type: a closed subscheme
  of `G` is of finite type over `k`.
- **Nontrivial subgroup.** `SubgroupFunctor.range i ≠ ⊥` says that some
  point of `G` with values in some `T` factors through `i` and is not the
  identity. The closed immersion `i` is a monomorphism. So this says that
  some `T`-point of `H` is not the identity, that is, that `H` is not the
  trivial group.
- **Nontrivial homomorphism to `Ga`.** The trivial homomorphism `H ⟶ 𝔾ₐ`
  always exists. So `Nontrivial (H ⟶ 𝔾ₐ)` holds exactly when some
  homomorphism `H ⟶ 𝔾ₐ` is not the trivial one, that is, does not factor
  through the identity section. This is Milne's nontrivial homomorphism.
- **The additive group.** Milne's `Ga` is `Spm(k[T])` with the group law
  `(R, +)`. This is `VectorGroup.groupScheme (CommRingCat.of k) 1`.
- **Unipotent.** Milne's definition is 6.45. `IsUnipotent G` uses only
  finite-dimensional representations, given by matrices after a choice of
  basis. This is the Library's predicate, and its comparison with 6.45 is
  recorded in [`Reductive.Basic`](../Reductive/Basic.md).
- **Universes.** One universe `u` is used for `k` and all group schemes. A
  closed subscheme of `G` can be represented in universe `u`, so quantifying
  over `H` in universe `u` covers every algebraic subgroup. This is a
  formalization convention.

## Related Library results

- `Langlands.GroupScheme.Unipotent.exists_additive_character` (in
  [`Unipotent.AdditiveCharacter`](AdditiveCharacter.md)) proves that a
  nontrivial affine unipotent group `U` over a field has a nonzero
  homomorphism `U ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1`. Its
  nontriviality hypothesis is `SubgroupFunctor.range (𝟙 U) ≠ ⊥`. This is the
  main step of the forward direction. The forward direction also needs that
  closed subgroups of unipotent groups are unipotent (Milne 14.7).

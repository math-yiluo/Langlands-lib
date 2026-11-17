# Central additive subgroups of unipotent groups over perfect fields

`Langlands.GroupScheme.PerfectFieldCentralAdditiveSubgroupStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a perfect field (`[PerfectField k]`) of characteristic
`p`, with `[Fact p.Prime]` and `[CharP k p]`. Let
`U : GroupScheme (Spec (CommRingCat.of k))` satisfy `[Smooth U.X.hom]` and
`[IsAffineHom U.X.hom]`. Assume `ConnectedSpace U.X.left`, `IsUnipotent U`
and `SubgroupFunctor.range (𝟙 U) ≠ ⊥`. The conclusion is

```text
∃ z : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ U,
  IsClosedSubgroup z ∧ IsCentral z
```

so `U` has a closed subgroup isomorphic to `𝔾ₐ` that lies in the centre of
`U`.

The ingredients are existing declarations, used without change.

- `PerfectField k`, `Fact p.Prime` and `CharP k p` (Mathlib) say that `k` is
  perfect of prime characteristic `p`.
- `Smooth U.X.hom` and `IsAffineHom U.X.hom` (Mathlib) say that the
  structure morphism `U.X.left ⟶ Spec k` is smooth and affine.
- `IsUnipotent` and `IsClosedSubgroup` (from
  [`Reductive.Basic`](../Reductive/Basic.md)). `IsUnipotent U` says that
  every nonzero finite-dimensional matrix representation of `U` has a
  nonzero fixed vector. `IsClosedSubgroup z` says that the underlying
  morphism of schemes of the homomorphism `z` is a closed immersion.
- `SubgroupFunctor.range (𝟙 U) ≠ ⊥` (from
  [`SubgroupFunctor`](../SubgroupFunctor.md)) says that some point of `U`
  with values in some scheme over `k` is not the identity, that is, `U` is
  not the trivial group.
- `VectorGroup.groupScheme (CommRingCat.of k) 1` (from
  [`VectorGroupQuotient`](../VectorGroupQuotient.md)) is the additive group
  `𝔾ₐ = Spec k[T]` over `Spec k`.
- `IsCentral z` (from [`Rational.Characters`](../Rational/Characters.md))
  says that for every scheme `T` over `Spec k` and every `T`-point `x` of
  `𝔾ₐ`, the point `x ≫ z` of `U` lies in the centre of `U`: after any base
  change `T′ ⟶ T` it commutes with every `T′`-point of `U`.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Corollary 14.55, p.297: "When k is perfect, every nontrivial connected
  unipotent group variety U over k contains a central subgroup variety
  isomorphic to Ga."
- Section 14e opening, p.292: "In this section, k is a field of
  characteristic p ≠ 0."
- Chapter 14 opening, p.279: "Recall that all algebraic groups are affine
  over a base field k."
- 6.45, p.135: "An algebraic group G is said to be unipotent if every nonzero
  representation of G has a nonzero fixed vector."
- Definition 1.3, p.7: an algebraic subgroup of `G` is an algebraic group
  `H` that is a `k`-subscheme of `G` whose inclusion is a homomorphism; "An
  algebraic subgroup is called a subgroup variety if its underlying scheme is
  a variety." Proposition 1.41, p.18: "Algebraic subgroups of algebraic
  groups are closed (in the Zariski topology)."
- p.13, after Proposition 1.26: "Therefore 'group variety' = 'smooth
  algebraic group'."
- p.8: "The functor R ⇝ (R, +) is represented by Spm(k[T]), and hence is an
  algebraic group Ga."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Corollary 14.55 on
printed p.297 with the same words. Its Section 14e opening, p.292, has the
same sentence as the 2017 edition.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for printed pp.274–316. The 2017
errata have no entry for pp.7, 8, 13 or 135. Their p.18 entry concerns the
proof of 1.40, not Proposition 1.41. The 2022 errata add a sentence after
Definition 1.3: the identity section `e → G` factors through `H` and gives
`H` a neutral element. This does not change the definition.

Milne's proof: "As U is nilpotent (14.21), it contains a nontrivial
connected group variety U′ in its centre (6.40). Now apply (14.54) to
(U″)°_red where U″ is the kernel of p: U′ → U′." Proposition 14.54 says that
over a perfect field a smooth connected commutative group of exponent `p` is
isomorphic to `G_a^r`. This is explanation only. The statement does not
depend on that route.

## Derivation from the source

- **Field.** In Section 14e the field has characteristic `p ≠ 0`. The
  statement assumes `[Fact p.Prime]` and `[CharP k p]`, and `[PerfectField k]`
  for "k is perfect".
- **Nontrivial connected unipotent group variety.** A group variety is a
  smooth algebraic group, affine by the Chapter 14 convention. The statement
  assumes `Smooth U.X.hom`, `IsAffineHom U.X.hom`, `ConnectedSpace U.X.left`,
  `IsUnipotent U` (6.45) and `SubgroupFunctor.range (𝟙 U) ≠ ⊥`
  (nontriviality). Smoothness gives local finite presentation and
  affineness gives quasi-compactness, so `U` is of finite type over `k`.
- **Central subgroup variety isomorphic to `Ga`.** A subgroup variety
  isomorphic to `Ga` is the image of a homomorphism `𝔾ₐ ⟶ U` that is an
  isomorphism onto a closed subgroup (Definition 1.3, Proposition 1.41); this
  is `IsClosedSubgroup z` for `z : 𝔾ₐ ⟶ U`. It is automatically a variety,
  since `𝔾ₐ` is smooth. "Central" means contained in the centre of `U`,
  which is `IsCentral z`.
- **Universes.** One universe `u` is used for `k` and the schemes. This is a
  formalization convention.

## Related Library results

- `Langlands.GroupScheme.RelativeRoot.CentralStableVectorSubgroupStatement`
  (in
  [`Rational.CentralVectorQuotientStatement`](../Rational/CentralVectorQuotientStatement.md))
  asks, over an algebraically closed field and with a split torus acting,
  for a central stable smooth connected vector subgroup of positive
  dimension.

# Characters and homomorphisms of diagonalizable groups: statement

Worker 3483.

`Langlands.GroupScheme.DiagonalizableCharacterStatement.{u}` is a proposition
definition. This module does not prove it.

## The statement

Let `k` be a field in the universe `u`. For an abelian group `Λ`, write
`D(Λ) = Diagonalizable.groupScheme (CommRingCat.of k) Λ` (`Torus/Diagonalizable`),
the spectrum of the group algebra `k[Λ]`. A point of `D(Λ)` over a test scheme
`U → Spec k` is identified with a group homomorphism `Multiplicative Λ →* Γ(U, 𝒪_U)ˣ`
by `Diagonalizable.characterPointsEquiv` (`Torus/KernelDiagonalizable`); write
`t(m)` for its value at `m ∈ Λ`. A character of `D(Λ)` is an element of
`characterLattice D(Λ)`, a homomorphism `D(Λ) ⟶ 𝔾_m` of commutative group schemes;
its value at a point is read through `Gm.pointsEquiv`, which identifies points of
`𝔾_m` over `U` with `Γ(U, 𝒪_U)ˣ`.

The statement is the conjunction of:

1. for every finitely generated abelian group `Λ`:
   - for every `m ∈ Λ` there is a character `χ` of `D(Λ)` with `χ(t) = t(m)` for every
     test scheme `U` and every point `t` of `D(Λ)` over `U`;
   - every character `χ` of `D(Λ)` satisfies `χ(t) = t(m)` for all `U` and `t`, for
     exactly one `m ∈ Λ`.

   Together these say that `m ↦ (t ↦ t(m))` is a bijection from `Λ` onto
   `X(D(Λ))`.
2. for all finitely generated abelian groups `Λ` and `Λ'`, the map
   `g ↦ Diagonalizable.restrictMap (CommRingCat.of k) g` from additive maps
   `g : Λ' →+ Λ` to homomorphisms `D(Λ) ⟶ D(Λ')` is bijective.

`Diagonalizable.restrictMap R g` (`Torus/DiagonalizableFaithfullyFlat`) is the
homomorphism of group schemes induced by the natural transformation
`Diagonalizable.restrict R g`, which on points precomposes a character
`Λ → Γ(U, 𝒪_U)ˣ` with `g` (`Diagonalizable.restrict_app_apply`). Its underlying
morphism of schemes is `Spec` of `mapDomain g : k[Λ'] → k[Λ]`
(`Diagonalizable.restrictMap_left`).

## Source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type over
a Field* (2017), source ID `milne-2017-algebraic-groups`, §§12.b–12.c.

§12.b fixes a finitely generated group (printed p.230, PDF p.246):

> Let M be a finitely generated commutative abstract group (written
> multiplicatively), and let k[M] be the k-vector space with basis M.

Proposition 12.3 (printed p.231, PDF p.247):

> For every finitely generated commutative group M, the functor
> D(M) : R ⇝ Hom(M, R^×) (homomorphisms of groups) is represented by the
> algebraic group Spm(k[M]).

Lemma 12.4 and the following sentences (printed p.232, PDF p.248):

> LEMMA 12.4. The group-like elements of k[M] are exactly the elements of M.

> Thus X(D(M)) ≃ M. The character of D(M) corresponding to m ∈ M is
> D(M)(R) = Hom(M, R^×) → R^× = G_m(R), f ↦ f(m).

Theorem 12.9(a) (printed p.233, PDF p.249):

> THEOREM 12.9. (a) The functor M ⇝ D(M) is a contravariant equivalence from the
> category of finitely generated commutative groups to the category of
> diagonalizable algebraic groups (with quasi-inverse G ⇝ X(G)).

## Correspondence with the source

- Milne's `M`, written multiplicatively, is the additive group `Λ`; his `D(M)` is
  the Library's `Diagonalizable.groupScheme (CommRingCat.of k) Λ`, with the same
  functor of points. Both parts keep Milne's standing hypothesis that the groups
  are finitely generated (`AddGroup.FG`).
- Part 1 is "X(D(M)) ≃ M" in the explicit form Milne gives: the character attached
  to `m` is `f ↦ f(m)`. The Lean statement asserts both that each `m` gives such a
  character and that each character comes from exactly one `m`. The additive
  structure of the bijection is not stated separately; it follows because the
  value of a sum of characters at `t` is the product of their values.
- Part 2 is the full faithfulness that Milne proves in (a): the map
  `Hom(M, M') → Hom(D(M'), D(M))` is bijective. The Lean statement uses the
  Library's `restrictMap`, which sends `g : Λ' →+ Λ` to `D(Λ) ⟶ D(Λ')`.
- The essential-surjectivity half of (a), Theorem 12.8 and the notion of a
  diagonalizable algebraic group (Definition 12.7), and parts (b) and (c) of
  Theorem 12.9 are not part of this statement. The published
  `Diagonalizable.ClosedSubgroupPresentationStatement` (row B4 of the family-2
  ledger) treats closed subgroups of `D(Λ)`.

## Relation to the Library

- The Library has full faithfulness only for split targets:
  `IsSplitTorus.existsUnique_hom_of_characterMap` (`Torus/CharacterMapHom`)
  identifies homomorphisms into a split torus with additive maps of character
  lattices, and `splitTorus.characterLatticeEquiv` (`Torus/Lattice`) computes the
  characters of `𝔾_m^I`. No Lean declaration of the characters of `D(Λ)` for `Λ`
  with torsion, or of full faithfulness of `Λ ↦ D(Λ)`, was found: searches of
  `Langlands/` for `restrictMap` together with `Bijective`, `Surjective`,
  `Injective` or `∃`, and for characters of `Diagonalizable.groupScheme`, found
  none.
- Possible ingredients for a proof: `Diagonalizable.characterPointsEquiv` and its
  naturality, `Torus/Grouplike` (the coefficients of a group-like element of
  `B[M]` are orthogonal idempotents summing to `1`), and
  `Diagonalizable.restrictMap_left`.
- The published family-2 ledger (`notes/group-schemes/ledger-family-2-tori.md`)
  cites Theorem 12.9 in rows A2, B2 and B4, and row A5 records that full
  faithfulness is available only for split targets. This statement covers
  Lemma 12.4 and the full faithfulness in Theorem 12.9(a).

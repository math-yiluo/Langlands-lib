# Identity jets of smooth groups are locally finite free

`Langlands.GroupScheme.IdentityJetLocallyFreeStatement.{u}` is a
`Prop`-valued definition.

## Hypotheses and conclusion

Let `S : Scheme.{u}` be arbitrary and let `G : GroupScheme S` have a smooth
and separated structure morphism. Fix a natural number `n`, a point `s : S`
and an open subset `W` of `S` containing `s`. The order-`n` identity jet of a
group `H` is the Library's `IdentityJet.scheme H n`, the closed subscheme cut
out by the `(n + 1)`-st power of the ideal of the unit section. Its
structure morphism to the base is `IdentityJet.projection H n`.

The conclusion provides:

- a commutative ring `R : CommRingCat.{u}` and an open immersion
  `i : Spec R ⟶ S` whose image contains `s` and is contained in `W`;
- an `R`-algebra `P : CommAlgCat.{u} R` and an isomorphism `e` from the
  order-`n` jet of the base change `(GroupScheme.baseChange i).obj G` to
  `Spec P`, such that `e.hom` followed by `Spec` of the structure map
  `R → P` is the jet projection to `Spec R`;
- a natural number `m` and a basis of `P` as an `R`-module indexed by
  `Fin m`.

So over `Spec R` the jet is the spectrum of a finite free `R`-algebra. Since
`W` is arbitrary, such neighbourhoods exist inside every neighbourhood of
`s`.

## Source correspondence

SGA 3, Exposé XVI, Proposition 3.1 considers a smooth group `G` of finite
presentation over `S`. Its statement calls the `n`-th normal invariant `G(n)`
of `G` along the unit section a locally free `O_S`-module (EGA IV 16). The
coordinate algebra of the infinitesimal neighbourhood `G_n` is filtered by
the powers of the augmentation ideal, with successive quotients the
symmetric powers of the conormal module. For smooth `G` these quotients are
locally free of finite rank, so the coordinate algebra of `G_n` is finite
locally free. A finite locally free module is free on a basic open
neighbourhood of any point. That gives the statement inside any
neighbourhood.
[SGA 3, Exposé XVI, Proposition 3.1](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo16.pdf#page=13).

SGA 3 works with groups of finite presentation. The statement assumes that
`G` is smooth and separated. Separatedness makes the unit section a closed
immersion. Then `IdentityJet.scheme G n` is the infinitesimal neighbourhood
`G_n`, finite over the base (Library
`IdentityJet.finite_projection`). This is an intermediate statement. With
the Library-level construction
`IdentityJet.exists_jetRepresentation` it gives
`JetConjugationRepresentationStatement`.

## Registered sources

- SGA 3, Exposé XVI, *Groupes de rang unipotent nul*, Gille–Polo
  recomposition (2008–2009), Proposition 3.1, printed p. 313 (original
  p. 509), one-based PDF p. 13. `Expo16.pdf`,
  `sga3-expose-xvi-gille-polo-2009`,
  SHA-256 `3db23f1a2e7942fe7c63c7a4475f76c67944f8a51996241d9e40127435fb892b`.

# The conjugation representation on an identity jet

`Langlands.GroupScheme.JetConjugationRepresentationStatement.{u}` is a
`Prop`-valued definition.

## Hypotheses and conclusion

Let `S : Scheme.{u}` be arbitrary and let `G : GroupScheme S` have a smooth
and separated structure morphism. Fix a natural number `n`, a point `s : S`
and an open subset `W` of `S` containing `s`.

The conclusion provides a commutative ring `R : CommRingCat.{u}` and an open
immersion `i : Spec R ⟶ S` whose image contains `s` and is contained in `W`.
It also provides a natural number `m` and a `MatrixRepresentation` `ρ` of the
base change `(GroupScheme.baseChange i).obj G` with index type `Fin m`.
Such a `ρ` is a morphism of group schemes over `Spec R` into
`GeneralLinear.groupScheme (Fin m) R`. The kernel of `ρ` is exactly the
centralizer of the order-`n` identity jet of the base-changed group. Take any
test scheme `U : Over (Spec R)` and a point `g` of the base-changed group on
`U`. Then `g ≫ ρ.hom.hom = 1` holds if and only if
`IdentityJet.CentralizesJet ((GroupScheme.baseChange i).obj G) n g` holds.

Because `W` is arbitrary, such affine neighbourhoods can be taken
arbitrarily small.

## Source correspondence

SGA 3, Exposé XVI, Proposition 3.1 considers a smooth group `G` of finite
presentation over `S`. It lets `G(n)` be the `n`-th normal invariant of the
unit section, a locally free `O_S`-module of finite rank. It lets `ρ_n` be
the natural adjoint representation of `G` in `GL_S(G(n))`, induced by the
inner automorphisms `g ↦ int(g)` as in the proof of Corollary 2.4. The proof
of 3.1 combines `ρ_n` with Exposé XI, 6.11(b), which identifies the centre
with `Centr_G(G_n)` for `n` large.
[SGA 3, Exposé XVI, Corollary 2.4 and Proposition 3.1](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo16.pdf#page=12).

The statement records the representation with its exact kernel for a fixed
`n`. Inner automorphisms fix the unit section, so they preserve each power of
its ideal and act on the order-`n` jet `G_n`. A point acts trivially on `G_n`
exactly when it centralizes `G_n`. For smooth `G` the coordinate algebra of
`G_n` is finite locally free over the base. Over an affine open of `S` on
which it is free of rank `m`, a basis turns the action into a homomorphism to
`m × m` invertible matrices. Free affine opens exist inside every
neighbourhood of `s`, which gives the condition involving `W`.

SGA 3 works with groups of finite presentation. The statement assumes
smoothness and separatedness only. Separatedness makes the unit section a
closed immersion, so that `IdentityJet.scheme G n` is the infinitesimal
neighbourhood. Smoothness makes its coordinate algebra locally free. This is
an intermediate statement toward
`Langlands.GroupScheme.LocalCentralKernelRepresentationStatement`.

## Registered sources

- SGA 3, Exposé XVI, *Groupes de rang unipotent nul*, Gille–Polo
  recomposition (2008–2009), proof of Corollary 2.4, printed p. 312
  (original pp. 506–507), one-based PDF p. 12; Proposition 3.1 and its proof,
  printed pp. 313–314 (original pp. 509–510), one-based PDF pp. 13–14.
  `Expo16.pdf`, `sga3-expose-xvi-gille-polo-2009`,
  SHA-256 `3db23f1a2e7942fe7c63c7a4475f76c67944f8a51996241d9e40127435fb892b`.
- A. Grothendieck, SGA 3, Exposé XI, Gille–Polo recomposition (December
  2008), Corollary 6.11, printed pp. 117–118 (original pp. 178–179),
  one-based PDF pp. 33–34. `Expo11.pdf` in
  `sga3-exposes-xi-xii-xiv-gille-polo-2008`.

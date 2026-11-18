# Affine quotient by the normalizer of a self-centralizing maximal torus

`Langlands.GroupScheme.SelfCentralizingTorusConjugacyQuotientAffineStatement.{u}`
is a `Prop`-valued definition stating that the quotient `G / N_G(T)` is
represented by an affine scheme over the base. It has the same hypotheses as
`Langlands.GroupScheme.SelfCentralizingTorusWeylAffinenessStatement`.

## Hypotheses and conclusion

Let `S : Scheme.{u}` be arbitrary and let `G` be a group scheme over `S`
whose structure morphism is smooth, separated and quasi-compact. Require
each residue-field group `RelativeIdentityComponent.residueFiber G s` to
be connected and affine. The affineness hypothesis applies fibre by fibre.

The commutative group scheme `T` and homomorphism `t : T.toGrp ⟶ G` satisfy
the following conditions.

- `RelativeTorus.IsTorus T.toGrp` means that `T` becomes a finite product
  of copies of the multiplicative group on each member of an étale cover.
  The number of copies may vary between cover members.
- `IsClosedSubgroup t` means that the underlying scheme morphism is a
  closed immersion.
- `IsFibrewiseMaximalTorus t` means that the pullback of `t` to each
  residue-field fibre is a maximal torus.
- `(torusCentralizer t).IsRepresentedBy t` means that `t` represents the
  full centralizer functor, which checks commutation after every refinement
  of the test scheme.

The conclusion gives `Y : Over S` with affine structure morphism `Y.hom`
and a morphism `p : G.X ⟶ Y` over `S` whose underlying scheme morphism
`p.left` is flat, surjective and locally of finite presentation. On every
test scheme `U : Over S`, two points `g h : U ⟶ G.X` have the same image
exactly when `g⁻¹ * h ∈ (torusNormalizer t).carrier U`. The normalizer
tests whether conjugation and its inverse preserve the torus after every
refinement of `U`. The fppf map gives local lifts of points of `Y`, and the
coset relation identifies the fppf sheaf quotient.

## Source correspondence

Smoothness, separatedness and quasi-compactness give finite presentation
over `S`. The residue-field groups are smooth, connected and affine.
Their identity sections give geometric connectedness, and maximality of
the torus in each of these groups persists under extension to an algebraic
closure. The full centralizer condition restricts to the geometric
fibres by testing on schemes over those fibres. Exposé XII, Theorem 7.1(a)
identifies the centralizer of a maximal torus with its Cartan subgroup.
Here the geometric Cartan subgroup is the supplied torus itself, so the
Cartan and maximal torus have equal dimension. Since the fibres are
affine, this dimension difference is their unipotent rank, which is zero.
[SGA 3, Exposé XII, Theorem 7.1(a)](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo12.pdf#page=29),
[Exposé X, Remarks 8.7](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo10-8nov09.pdf#page=36).

Exposé XVI, Theorem 4.1(c) represents the functor `TM_G` of maximal tori
by a smooth affine `S`-scheme under these hypotheses. The proof of 4.1(d),
for (iii) ⇒ (i), identifies `G/N_G(T) ≅ TM_G` using conjugacy of maximal
tori. This gives the affine target `Y` for the statement.
[SGA 3, Exposé XVI, Theorem 4.1(c) and proof of 4.1(d)](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo16.pdf#page=18).

The map to `TM_G` sends `g` to `g T g⁻¹`. Over a test scheme `U` with
maximal torus `T'` corresponding to a point of `TM_G`, the pullback of the
map is the transporter from `T_U` to `T'`. Exposé XII, Theorem 7.1(b)
represents this transporter by a smooth closed subscheme and gives
étale-local conjugacy, so the transporter is smooth and surjective over
`U`. Applied to the universal torus, this gives the flat, surjective,
locally finitely presented map in the conclusion. The transporter from
`T_U` to itself is the normalizer. Thus `g T_U g⁻¹ = h T_U h⁻¹` holds
exactly when `g⁻¹ * h` normalizes `T_U`, giving the stated coset relation.
[SGA 3, Exposé XII, Theorem 7.1(b) and its proof](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo12.pdf#page=29).

## Registered sources

- SGA 3, Exposé XVI, *Groupes de rang unipotent nul*, Gille–Polo
  recomposition (2008–2009), Theorem 4.1(c) and the proof of 4.1(d),
  printed pp. 318–319 (original pp. 519–521), one-based PDF pp. 18–19.
  `Expo16.pdf`, `sga3-expose-xvi-gille-polo-2009`,
  SHA-256 `3db23f1a2e7942fe7c63c7a4475f76c67944f8a51996241d9e40127435fb892b`.
- A. Grothendieck, SGA 3, Exposé XII, *Tores maximaux, groupe de Weyl,
  sous-groupes de Cartan, centre réductif des schémas en groupes lisses et
  affines*, Gille–Polo recomposition (December 2008), Theorem 7.1(a)–(b)
  and its proof, printed pp. 147–148 (original pp. 224–227), one-based
  PDF pp. 29–30. `Expo12.pdf` in `sga3-exposes-xi-xii-xiv-gille-polo-2008`,
  PDF SHA-256 `4dae85a06b7c1d6cd98d6332de144aed80a96d19267d0603cc9cbef06757c15e`.
- A. Grothendieck, SGA 3, Exposé X, *Caractérisation et classification des
  groupes de type multiplicatif*, Gille–Polo recomposition (November 2009),
  the unipotent rank formula in Remarks 8.7, printed p. 98 (original p. 121),
  one-based PDF p. 36. `Expo10-8nov09.pdf`, `sga3-expose-x-gille-polo-2009`,
  SHA-256 `a335ff4972694dbe531b46f852d2c77f13e433b365d0d38289b25adfeadf2c62`.

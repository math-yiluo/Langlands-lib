# Affineness of the normalizer quotient, given local representations

`Langlands.GroupScheme.SelfCentralizingQuotientAffineOfRepresentationStatement.{u}`
is a `Prop`-valued definition. It states that any fppf quotient of `G` by the
normalizer of a self-centralizing maximal torus is affine over the base. It
assumes that `G` has, locally on the base, a finite free matrix
representation with central kernel.

## Hypotheses and conclusion

Let `S : Scheme.{u}` be arbitrary and let `G : GroupScheme S` have a smooth,
separated and quasi-compact structure morphism `G.X.hom`. For each point
`s : S`, the residue-field group `RelativeIdentityComponent.residueFiber G s`
must have connected underlying space and affine structure morphism. These are
the hypotheses on `G` of
`Langlands.GroupScheme.SelfCentralizingTorusConjugacyQuotientAffineStatement`.

The statement adds the following hypothesis, which is the conclusion of
`Langlands.GroupScheme.LocalCentralKernelRepresentationStatement` written out
in full. For every point `s : S` there are a commutative ring `R`, an open
immersion `i : Spec R ⟶ S` whose image contains `s`, a natural number `m` and
a morphism of group schemes `ρ` over `Spec R` from the base change
`(GroupScheme.baseChange i).obj G` to `GeneralLinear.groupScheme (Fin m) R`.
Its kernel must be central: over every test scheme `U : Over (Spec R)`, a
point `g` with `g ≫ ρ.hom.hom = 1` commutes with every point `h`.

The torus hypotheses are those of the target statement. `T` is a
commutative group scheme over `S` and `t : T.toGrp ⟶ G` is a homomorphism.

- `RelativeTorus.IsTorus T.toGrp` says that `T` is a torus.
- `IsClosedSubgroup t` says that `t.hom.left` is a closed immersion.
- `IsFibrewiseMaximalTorus t` says that the pullback of `t` to each
  residue-field fibre is a maximal torus.
- `(torusCentralizer t).IsRepresentedBy t` says that `t` represents the full
  centralizer functor of the torus.

Let `Y : Over S` and `p : G.X ⟶ Y` be a morphism over `S` whose underlying
scheme morphism `p.left` is flat, surjective and locally of finite
presentation. Suppose that for every test scheme `U : Over S` and points
`g h : U ⟶ G.X`, the equation `g ≫ p = h ≫ p` holds exactly when
`g⁻¹ * h ∈ (torusNormalizer t).carrier U`. These are the properties of the
quotient map in the target statement. The conclusion is that `Y.hom` is an
affine morphism.

## Source correspondence

The flatness, surjectivity and finite presentation of `p` make it an fppf
covering. The coset condition identifies its kernel pair with the relation
`g⁻¹ h ∈ N`, where `N = Norm_G(T)`. So `Y` represents the fppf quotient sheaf
`G/N`, and the conclusion says that `G/N` is affine over `S`.

The target statement's Markdown explains why its hypotheses on `G` and `t`
place us in SGA 3, Exposé XVI, Theorem 4.1. `G` is smooth of finite
presentation with connected affine fibres. The unipotent rank is zero, and
`T` is a maximal torus. Theorem 4.1(c) represents the functor `TM_G` of
maximal tori by a smooth affine `S`-scheme. The proof of 4.1(d), direction
(iii) ⇒ (i), identifies `G/N` with `TM_G` by conjugacy of maximal tori
(Exposé XII, 7.1(b)). Thus `G/N` is affine over `S`.
[SGA 3, Exposé XVI, Theorem 4.1](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo16.pdf#page=18).

The proof of 4.1(c) uses Theorem 3.3(c) for `G' = G/Z`, where `Z` is the
centre of `G`. Theorem 3.3(c) rests on Proposition 3.1(c) and Lemma 3.2.
Proposition 3.1 uses the representations `ρ_n` with kernel `Z`, and these
are the source of the representation hypothesis above. Lemma 3.2 says that a
monomorphism of finitely presented groups induces a closed immersion of the
functors of subtori. Its proof applies Exposé XI, Corollary 6.10 to a torus.
[SGA 3, Exposé XVI, Proposition 3.1, Lemma 3.2 and Theorem 3.3](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo16.pdf#page=13),
[Exposé XI, Corollary 6.10](https://wstein.org/sga/SGA3/Expo11.pdf#page=33).

## Provenance of the formulation

The statement splits the target statement of Task 7782 into steps. It is not
literally a statement of SGA 3. It differs from the target in two ways.

- It assumes the local representations with central kernel rather than
  deriving them. `Langlands.GroupScheme.LocalCentralKernelRepresentationStatement`
  derives them from the hypotheses on `G` stated here (smooth, separated,
  quasi-compact, connected residue-field fibres). So the extra hypothesis
  does not narrow the scope once that statement is proved.
- It takes the quotient `(Y, p)` as input and concludes affineness, instead
  of asserting that an affine quotient exists. Two such quotients represent
  the same fppf sheaf `G/N`, so they are isomorphic over `S`. Hence this
  form, together with the existence of one quotient with the stated
  properties, gives the target statement.

## Registered sources

- SGA 3, Exposé XVI, *Groupes de rang unipotent nul*, Gille–Polo
  recomposition (2008–2009), Proposition 3.1, Lemma 3.2 and Theorem 3.3 with
  proofs, printed pp. 313–315 (original pp. 509–513), one-based PDF
  pp. 13–15; Theorem 4.1(c) and the proof of 4.1(d), printed pp. 318–319
  (original pp. 519–521), one-based PDF pp. 18–19. `Expo16.pdf`,
  `sga3-expose-xvi-gille-polo-2009`,
  SHA-256 `3db23f1a2e7942fe7c63c7a4475f76c67944f8a51996241d9e40127435fb892b`.
- A. Grothendieck, SGA 3, Exposé XI, Gille–Polo recomposition (December
  2008), Corollary 6.10, printed p. 117 (original pp. 177–178), one-based
  PDF p. 33. `Expo11.pdf` in `sga3-exposes-xi-xii-xiv-gille-polo-2008`.

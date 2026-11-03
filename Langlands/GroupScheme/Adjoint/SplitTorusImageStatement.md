# Existence statement for the image of a maximal split torus in an adjoint quotient

This module gives one proposition declaration,
`Langlands.GroupScheme.AdjointSplitTorusImageExistenceStatement`. It is a
`Prop`-valued definition, not a proof. It constructs no torus, image or
adjoint quotient, and it does not prove that any of them exist.

## The statement

The declaration quantifies over an arbitrary universe `u`, every field
`k : Type u`, actual group schemes `G` and `A` over `Spec (CommRingCat.of k)`,
an actual commutative group scheme `T`, an actual homomorphism `q : G ⟶ A` and
an actual homomorphism `i : T.toGrp ⟶ G`. It has exactly two premises:

1. `IsAdjointQuotient q`, from `Adjoint.Quotient`. This says that `G` is
   connected reductive, that `A` is adjoint, and that `q` is flat, surjective
   and locally of finite presentation. It also says that the actual kernel of
   `q` represents the full all-test centre of `G`, and that `q` has the group
   and scheme universal properties for maps killing that centre. The centre can
   be nonsmooth.
2. `IsMaximalSplitTorus i`, from `Rational.SplitTorus`. This says that `T` is a
   split torus, that `i` is a closed immersion, and that `i` is maximal among
   split subtori under factorization.

The conclusion asserts that there exist an actual commutative group scheme
`T_ad` over `k`, an actual homomorphism `j : T_ad.toGrp ⟶ A` and an actual
homomorphism `p : T ⟶ T_ad` with `IsAdjointSplitTorusImage q i j p`, from
`Adjoint.SplitTorus`. That published structure records all of the following:

- `IsMaximalSplitTorus j`, so `T_ad` is split, `j` is a closed immersion, and
  `j` is maximal. This maximality is part of the conclusion and is not assumed.
- The actual square `CommGroupScheme.groupHom p ≫ j = i ≫ q`.
- Flatness, surjectivity and local finite presentation of the underlying
  scheme morphism of `p`.
- The two premises again, `IsAdjointQuotient q` and `IsMaximalSplitTorus i`.

The statement claims no surjectivity on points over a fixed test scheme. It
requires no finite kernel for `p`, because the centre of a reductive group can
contain a positive-dimensional torus. It requires no smoothness of that kernel.
It has no integral or primitive cocharacter lift. It has no smoothness,
perfection or characteristic hypothesis beyond those in the two premises.
It is about the reductive adjoint quotient. It says nothing about a simply
connected cover of the derived group.

The full kernel comparison is not repeated in the statement. The published
theorem `IsAdjointSplitTorusImage.mem_range_kernel_iff` already proves it for
every witness. On every test scheme, a point of `T` lies in the range of the
actual kernel inclusion of `p` exactly when its image under `i` lies in the full
centre of `G`. This includes infinitesimal points.
`IsAdjointSplitTorusImage.fppf` extracts the three properties of `p`. The
real-cocharacter surjectivity in `IsAdjointSplitTorusComparison` is not part of
this target. The identification of the real kernel with the root annihilator
`RealTorusSpace.relativeCentralDirections i` is also not part of this target.

## Sources

J. S. Milne, *Algebraic Groups* (2017), is registered as
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

- Definition 12.14 and the following paragraph, printed p.236 / PDF p.252,
  define split tori and state that a quotient of a split torus is split.
- Remark 17.63, printed p.373 / PDF p.389, identifies the adjoint group with
  the quotient of a reductive group by its centre.
- Definition 5.5, printed p.99 / PDF p.115, defines quotient maps as faithfully
  flat homomorphisms.
- Theorem 5.39, printed p.108 / PDF p.124, factors every homomorphism of
  algebraic groups as a quotient map followed by a closed immersion.

The retained official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
has no correction on printed pages 99, 108, 236 or 373.

Maximality of the image comes from A. Borel and J. Tits, *Compléments à
l'article « Groupes réductifs »*, Publ. Math. IHÉS 41 (1972), 253–276. It is
registered as `borel-tits-1972-complements-groupes-reductifs`, SHA256
`7639a6a59bdb4520ca171fa61c192c000f00396460b05b32766d56dee5a84e49`.

- The standing convention on printed p.253 / PDF p.2 says that `G` is a
  connected reductive `k`-group throughout.
- Définition (2.2) and Remarque (2.3), printed p.254 / PDF p.3, define central
  morphisms. In scheme language, a morphism is central exactly when its
  scheme-theoretic kernel is contained in the centre of the source.
- Théorème (2.20)(ii), printed p.260 / PDF p.9, says the following. For a
  central surjective `k`-morphism `f : G → G'`, the maximal `k`-split tori of
  `G'` are the images of the maximal `k`-split tori of `G`.

An adjoint quotient has kernel equal to the full centre, so it is central in
this sense. No separability is needed. The opening of §2 on the same page
explains this choice of source. Borel–Tits, *Groupes réductifs* (1965),
Proposition 4.25, printed p.94 / PDF p.41, covers only separable isogenies.
The quotient by a nonsmooth centre is not separable, for example
`SL_p → PGL_p` in characteristic `p`. The 1965 paper is registered as
`borel-tits-1965-groupes-reductifs`, SHA256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.
The 1972 paper also corrects the 1965 paper. Its §1, printed pp.253–254,
corrects 1965 items 4.24 and 4.26. Its (2.22), printed p.261 / PDF p.10,
replaces the use of 4.25 in the proof of 1965 Proposition 4.27 by (2.20). Its
§5, printed pp.274–275, lists no correction on printed pp.93–94. Those pages
contain the conjugacy Theorem 4.21 and Proposition 4.25.

## Derived packaging

The statement is a derived reformulation of these sources on the Library's
actual group schemes. Theorem 5.39 applied to the restriction `i ≫ q` gives a
quotient map `p` onto a closed subgroup `j`. A faithfully flat map of finite
type over a field is flat, surjective and locally of finite presentation.
Milne's paragraph after Definition 12.14 makes the image split. Théorème
(2.20)(ii) makes it maximal. The Library expresses split subtori as closed
immersions from a split torus, and maximality as invertibility of every
factorization through another split subtorus. The cited sources use subgroups
and inclusion instead. Borel–Tits work with smooth algebraic groups and
set-theoretic images. Here `A` is smooth because it is semisimple, and the
image of the reduced torus `T` is reduced.

These remarks give the provenance of the claim. They are not a proof. A proof
of this target is a separate obligation for a successor task.

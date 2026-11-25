# Reduction of effective quotients by flat proper equivalence relations to the Hilbert scheme

The proposition reduces the
published `FlatProperEquivalenceRelationQuotientStatement` to the published
`HilbertSchemeUniversalFamilyStatement`.

No proof is asserted here. The module only states the implication.

## Statement

The module defines one declaration,
`Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientReductionStatement`,
with the single universe parameter `u`. It is a proposition (`def … : Prop`):

```lean
HilbertSchemeUniversalFamilyStatement.{u} →
  FlatProperEquivalenceRelationQuotientStatement.{u}
```

Both propositions are published Library statements in the namespace
`Langlands.AlgebraicGeometry`. They are imported from their modules and used at
the same universe `u`.

1. The hypothesis
   `Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamilyStatement` ("HGP")
   concerns a commutative ring `A` and a flat morphism `f : X ⟶ Spec A`, locally
   of finite presentation. The scheme `X` carries an invertible module whose
   global sections give a closed immersion into a finite projective space over
   `A`. HGP provides a scheme `H` with `πH : H ⟶ Spec A` separated and locally of
   finite presentation, and an ideal sheaf `W` on `X ×_A H`, such that:
   - pulling back `W` is a bijection, for every scheme `T` over `Spec A`, from
     the morphisms `T ⟶ H` over `Spec A` onto the ideal sheaves on `X ×_A T`
     whose closed subscheme is flat and locally of finite presentation over `T`;
   - `H` is covered by pairwise disjoint opens `U θ`, indexed by `θ ∈ ℚ[t]`, and
     each `U θ` is H-projective over `Spec A` (`IsHProjective`).

   HGP also describes the `B`-points of `U θ` by Hilbert polynomials. The
   reduction does not need that clause.
2. The conclusion
   `Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientStatement`
   ("(c)") concerns a noetherian ring `A`, an H-quasi-projective
   `p : Z ⟶ Spec A` (`IsHQuasiProjective p`), and `s t : R ⟶ Z` with
   `s ≫ p = t ≫ p`. It assumes that `pullback.lift s t _ : R ⟶ Z ×_A Z` is a
   monomorphism and that, for every scheme `T`, the relation "`x` and `y` are
   `φ ≫ s` and `φ ≫ t` for some `φ : T ⟶ R`" on `T ⟶ Z` is an equivalence
   relation. It also assumes that `s` is flat and proper. Then there are an
   H-quasi-projective `q : Q ⟶ Spec A` and a morphism `π : Z ⟶ Q` such that
   `π ≫ q = p`, `π` is flat, surjective, proper and locally of finite
   presentation, and `IsPullback s t π π`, that is, `R = Z ×_Q Z`.

The Markdown files of the two statements explain every hypothesis and
conclusion in detail.

## Source and provenance

The provenance is "derived". The implication is the proof of Theorem 6.8 of
N. Nitsure, *Construction of Hilbert and Quot schemes*
(`nitsure-2005-hilbert-quot-arxiv-math0504590v1`, p.33, proof pp.33–35). That
proof starts from the Hilbert scheme of `X` over `S` (Theorem 6.3) and derives
the quotient. Nitsure does not state the implication separately. Kleiman uses
the quotient theorem in the proof of Lemma 4.9 of *The Picard scheme*
(`kleiman-2005-picard-scheme-arxiv-math0504020v1`, pp.30–31). There he cites
Altman–Kleiman [AK80, Thm. (2.9)], whose proof also goes through the Hilbert
scheme.

HGP is applied to the projective space `X = ℙⁿ_A` that contains `Z`, not to `Z`
itself. Nitsure applies the Hilbert scheme to the quasi-projective `X` of his
theorem (his `X` is our `Z`). Over `ℙⁿ_A` the hypotheses of HGP hold: the
identity of `ℙⁿ_A` is a closed immersion, `ℙⁿ_A` is flat and of finite
presentation over `A`, and the relation `R` embeds as a closed subscheme of
`ℙⁿ_A ×_A Z`, which is flat and proper over `Z`.

## Proof

The proof (`FlatEquivalenceRelation.flatProperEquivalenceRelationQuotient_of_hilbertScheme` in
`FlatProperEquivalenceRelationQuotientReductionProof`) follows Nitsure's argument, with two changes.

1. **The family.** The morphism `R ⟶ ℙⁿ_A ×_A Z`, `r ↦ (i(t r), s r)`, is a
   proper monomorphism, hence a closed immersion. Its ideal sheaf is flat and
   locally of finite presentation over `Z` because `s` is. HGP with `T = Z` gives
   the classifying morphism `φ : Z ⟶ H` over `Spec A`.
2. **Detecting the relation.** For every scheme `T` and all `x y : T ⟶ Z`, the
   relation holds exactly when `x ≫ φ = y ≫ φ`. This is Nitsure's property
   (***) on p.34. Its proof uses that the relation is an equivalence relation on
   `T`-points for all `T`.
3. **The open locus (change 1).** Nitsure takes `H` to be a finite union of
   Hilbert-polynomial pieces. Here the morphism `φ` is restricted to the open
   locus `H''` of `H` over which the universal closed subscheme lies in the
   largest open subscheme of `ℙⁿ_A` in which `Z` is closed. This makes the graph
   `Z ⟶ D''` a closed immersion, where `D''` is the universal closed subscheme
   over `H''`.
4. **The quotient (change 2).** `Q` is the scheme-theoretic image of
   `φ : Z ⟶ H''`, and `π : Z ⟶ Q` is the induced morphism. Nitsure uses fpqc
   descent of closed subschemes (his Lemma 6.7(2)). Here, flat base change of the
   kernel of a quasi-compact morphism along the flat morphism `D'' ⟶ H''` gives
   `Z = D'' ×_{H''} Q`. Hence `π` is flat, proper and locally of finite
   presentation, as a base change of `D'' ⟶ H''`. It is surjective because it is
   closed and dominant. Property (***) gives `R = Z ×_Q Z`.
5. **Quasi-projectivity.** `Q` is quasi-compact, being the image of the
   quasi-compact `Z`. The opens `U θ` cut `Q` into finitely many pairwise
   disjoint nonempty open and closed pieces. Each piece is a quasi-compact
   immersion into an H-projective `U θ`. Finitely many disjoint pieces with
   immersions into `ℙ^{n_θ}_A` embed into one projective space, using disjoint
   blocks of homogeneous coordinates. So `Q` is H-quasi-projective.

## Use

The published reduction
`Langlands.AlgebraicGeometry.FppfQuotientLocallyNoetherianReductionStatement`
takes (c) as its hypothesis. A proof of the present implication, together with a
proof of HGP, proves (c). The Library has both
(`flatProperEquivalenceRelationQuotient_of_hilbertScheme` and
`hilbertSchemeUniversalFamily`); `flatProperEquivalenceRelationQuotient` in
`FlatProperEquivalenceRelationQuotientProof` combines them.

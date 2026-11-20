# Closed embedding of the normalizer quotient into the subtori of `GL_m`

`Langlands.GroupScheme.SelfCentralizingConjugacyClosedEmbeddingStatement.{u}` is
a `Prop`-valued definition. Over an affine base it considers a group `G` with a
self-centralizing maximal torus `T` and a matrix representation `ρ` with central
kernel. It says that sending `g` to the conjugate `ρ(g) ρ(T) ρ(g)⁻¹` of the
image torus embeds the quotient `G/N_G(T)` as a closed subscheme of the scheme of
subtori of `GL_m`.

## Hypotheses and conclusion

Fix `R : CommRingCat.{u}` and `G : GroupScheme (Spec R)`.

**The group.** `G.X.hom` is smooth, separated and quasi-compact. For every point
`s : Spec R` the residue-field group
`RelativeIdentityComponent.residueFiber G s` has connected underlying space and
affine structure morphism. These are the hypotheses on `G` of
`Langlands.GroupScheme.SelfCentralizingTorusConjugacyQuotientAffineStatement`,
over the base `Spec R`.

**The representation.** `m : ℕ` and `ρ : MatrixRepresentation G (Fin m)`, that
is, `ρ : G ⟶ GeneralLinear.groupScheme (Fin m) R`. Its kernel is central: for
every test scheme `U : Over (Spec R)` and points `g h : U ⟶ G.X`, if
`g ≫ ρ.hom.hom = 1` then `g * h = h * g`.

**The torus.** `T : CommGroupScheme (Spec R)` and `t : T.toGrp ⟶ G` satisfy the
torus hypotheses of the target statement. `RelativeTorus.IsTorus T.toGrp` says
that `T` is a torus. `IsClosedSubgroup t` says that `t` is a closed immersion.
`IsFibrewiseMaximalTorus t` says that `t` is a maximal torus on every
residue-field fibre. `(torusCentralizer t).IsRepresentedBy t` says that `t`
represents the full centralizer functor of `T`.

**The image torus.** `D : CommGroupScheme (Spec R)` with
`π : T.toGrp ⟶ D.toGrp` and `e : D.toGrp ⟶ GeneralLinear.groupScheme (Fin m) R`.
`D` is a torus, `e` is a closed immersion, and the underlying morphism of `π` is
flat, surjective and locally of finite presentation. Finally `π ≫ e = t ≫ ρ`. So
`e` is the inclusion of the image torus `ρ(T)`. Such data exist by
`Langlands.GroupScheme.RelativeTorusImageFactorizationStatement`.

**The scheme of subtori.** `M : Over (Spec R)`, `K : GroupScheme M.left` and
`j : K ⟶ (GroupScheme.baseChange M.hom).obj (GeneralLinear.groupScheme (Fin m) R)`.
`j` is a closed immersion, `K` is a torus, and `j` is universal
(`TorusSubgroupModuli.IsUniversal`). So `M` represents the functor of closed
subtori of `GL_m` over `Spec R`.

**The conjugacy map.** `f : G.X ⟶ M` satisfies
`TorusSubgroupModuli.evaluate j f = SubgroupFunctor.range (SubgroupFunctor.conjugateFamily e ρ.hom.hom)`.
The right side is the family of subtori of `GL_m` over `G.X` whose member at a
point `g` is `ρ(g) e(D) ρ(g)⁻¹` (`SubgroupFunctor.mem_range_conjugateFamily_iff`).
By universality of `j` there is exactly one such `f`.

**The quotient.** `Y : Over (Spec R)` and `p : G.X ⟶ Y`. The underlying morphism
`p.left` is flat, surjective and locally of finite presentation. For every test
scheme `U : Over (Spec R)` and points `g h : U ⟶ G.X`, `g ≫ p = h ≫ p` holds
exactly when `g⁻¹ * h ∈ (torusNormalizer t).carrier U`. So `Y` represents the
fppf quotient sheaf `G/N`, where `N = Norm_G(T)`.

**Conclusion.** There is a morphism `φ : Y ⟶ M` over `Spec R` with `p ≫ φ = f`
whose underlying morphism `φ.left` is a closed immersion.

## Source correspondence

The statement is the argument of SGA 3, Exposé XVI, Theorem 3.3(c) and the proof
of Theorem 4.1(d), carried out with the given representation `ρ` in place of
the representations `ρ_n` of Proposition 3.1(b). Write `S = Spec R`. `G` is
smooth and separated, and quasi-compact, hence of finite presentation over `S`.

1. *The kernel.* Let `K₀ = Ker ρ`. It is central, so it centralizes `T`. Since
   `T` is its own centralizer, `K₀ ⊂ T`. Hence `K₀ = Ker(t ≫ ρ) = Ker π`,
   because `e` is a monomorphism. By Exposé IX, Theorem 6.8, `K₀` is of
   multiplicative type, in particular flat over `S`. By Exposé XVI,
   Corollary 2.3, the quotient `G' = G/K₀` is representable and `ρ` factors as
   `G → G' → GL_m` with `i : G' → GL_m` a monomorphism. `G'` is smooth and of
   finite presentation over `S`, as in the proof of Proposition 3.1(a).
2. *Closed immersion of subtori.* By Exposé XVI, Lemma 3.2, applied to `i`, the
   map `T' ↦ i(T')` from subtori of `G'` to subtori of `GL_m` is represented by a
   closed immersion of finite presentation. Since `M` represents the subtori of
   `GL_m`, the subtori of `G'` are represented by a closed subscheme of `M`.
3. *Maximal tori.* `G'` has the maximal torus `T/K₀`, so the reductive rank of
   its fibres is locally constant. Its maximal tori are the subtori whose rank is
   that reductive rank, an open and closed condition. This is the argument of
   the proof of Theorem 3.3(c) and of Exposé XV, Theorem 8.15. So the functor
   `TM_{G'}` of maximal tori of `G'` is a closed subscheme of `M`.
4. *Passing to `G`.* The quotient map `G → G'` is faithfully flat with central
   kernel. By Exposé XII, Theorem 7.1(e) and (f), `T' ↦ T'/K₀` is a bijection
   from maximal tori of `G` to maximal tori of `G'`, compatibly with base change.
   This is the maximal-torus form of Exposé XV, Theorem 7.3(iv), which XVI 3.3
   uses for Cartan subgroups. Here every maximal torus is its own Cartan
   subgroup, because `T` is self-centralizing and all maximal tori are locally
   conjugate. So `TM_G ≅ TM_{G'}`.
5. *Conjugacy.* By Exposé XII, Theorem 7.1(b), any two maximal tori of `G` are
   conjugate locally for the étale topology. So `g ↦ gTg⁻¹` induces an
   isomorphism of fppf sheaves `G/N → TM_G`, where `N`, the stabilizer of `T`,
   is the normalizer. This is the identification in the proof of Exposé XVI,
   Theorem 4.1(d).
6. *Assembly.* `Y` represents `G/N`, so the composite
   `Y ≅ G/N ≅ TM_G ≅ TM_{G'} → M` is a closed immersion `φ`. It sends the class
   of `g` to `i(gTg⁻¹/K₀) = ρ(g) ρ(T) ρ(g)⁻¹`, and `ρ(T) = e(D)` because `π` is an
   fppf epimorphism. So `p ≫ φ` classifies the family `ρ(g) e(D) ρ(g)⁻¹`, and
   uniqueness in the universal property of `j` gives `p ≫ φ = f`.

[SGA 3, Exposé XVI, Corollary 2.3](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo16.pdf#page=12),
[Proposition 3.1, Lemma 3.2 and Theorem 3.3](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo16.pdf#page=13),
[Theorem 4.1](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo16.pdf#page=18);
[Exposé XII, Theorem 7.1](https://wstein.org/sga/SGA3/Expo12.pdf#page=29);
[Exposé XV, Theorems 7.3 and 8.15](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo15.pdf#page=54);
[Exposé IX, Theorem 6.8](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Exp9-8nov09.pdf#page=25).

## Provenance of the formulation

SGA 3 does not state this as a single result. The statement packages steps 1–6
above, which SGA 3 carries out for `G/Z` and the representations `ρ_n` with kernel
exactly the centre `Z`. Here the kernel of `ρ` is only assumed central. The
self-centralizing torus then gives `Ker ρ ⊂ T`, and the same argument applies.
The statement is a premise of the affineness proof of Task 7782 for the
normalizer quotient. That proof combines it with
`Langlands.GroupScheme.TorusSubgroupModuli.GeneralLinearAffineSumStatement` and
`Langlands.GroupScheme.RelativeTorusImageFactorizationStatement`.

Three choices in the formulation are deliberate.

- The base is affine and the representation is global, as provided locally by
  the representation hypothesis of
  `Langlands.GroupScheme.SelfCentralizingQuotientAffineOfRepresentationStatement`.
- The map `f` is pinned to the Library's universal family of subtori of `GL_m`.
  A conclusion of the form "`Y` embeds as a closed subscheme of some scheme"
  would be trivially true.
- The conclusion includes the factorization `p ≫ φ = f`, so that users need not
  descend `f` along `p` themselves.

## Registered sources

- SGA 3, Exposé XVI, *Groupes de rang unipotent nul*, Gille–Polo recomposition
  (2008–2009): Corollary 2.3, printed p. 312, one-based PDF p. 12; Proposition 3.1,
  Lemma 3.2 and Theorem 3.3 with proofs, printed pp. 313–315 (original
  pp. 509–513), one-based PDF pp. 13–15; Theorem 4.1 and the proof of 4.1(d),
  printed pp. 318–319 (original pp. 519–521), one-based PDF pp. 18–19.
  `Expo16.pdf`, `sga3-expose-xvi-gille-polo-2009`,
  SHA-256 `3db23f1a2e7942fe7c63c7a4475f76c67944f8a51996241d9e40127435fb892b`.
- A. Grothendieck, SGA 3, Exposé XII, Gille–Polo recomposition (December 2008),
  Theorem 7.1, printed p. 147 (original pp. 224–226), one-based PDF p. 29.
  `Expo12.pdf` in `sga3-exposes-xi-xii-xiv-gille-polo-2008`.
- M. Raynaud, SGA 3, Exposé XV, Gille–Polo recomposition (2008–2009),
  Theorem 7.3, printed p. 286 (original pp. 454–455), one-based PDF p. 54;
  Theorem 8.15 with proof, printed pp. 298–299 (original pp. 480–481),
  one-based PDF pp. 66–67. `Expo15.pdf`, `sga3-expose-xv-gille-polo-2009`,
  SHA-256 `03647e0232067a7508bb1350e7aace3e88d58872956f068ced808a4f9cc3273f`.
- A. Grothendieck, SGA 3, Exposé IX, Gille–Polo recomposed edition (version 8 Nov
  2009), Theorem 6.8, printed p. 55, one-based PDF p. 25. `Exp9-8nov09.pdf`,
  `sga3-expose-ix-gille-polo-2009`.

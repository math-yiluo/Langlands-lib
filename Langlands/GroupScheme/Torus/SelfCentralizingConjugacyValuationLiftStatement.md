# Valuative lifting for the conjugacy map to the subtori of `GL_m`

`Langlands.GroupScheme.SelfCentralizingConjugacyValuationLiftStatement.{u}` is a
`Prop`-valued definition. It has the setting of
`Langlands.GroupScheme.SelfCentralizingConjugacyUniversallyClosedStatement`, without
the quotient `Y`. Over an affine base there is a group `G` with a self-centralizing
maximal torus `T` and a matrix representation `ρ` with central kernel. The conjugacy
map `f : G.X ⟶ M` sends a point `g` of `G` to the parameter of the subtorus
`ρ(g) ρ(T) ρ(g)⁻¹` of `GL_m`. The statement says that `f` satisfies a valuative
lifting property: a point of `M` over a valuation ring of an algebraically closed
field whose generic point is a value of `f` is itself a value of `f`.

It is the geometric input for universal closedness of the descended conjugacy
map. The module
`Langlands.GroupScheme.Torus.SelfCentralizingConjugacyUniversallyClosedReduction`
proves that this statement and
`Langlands.GroupScheme.TorusSubgroupModuli.GeneralLinearAffineSumStatement` imply
`SelfCentralizingConjugacyUniversallyClosedStatement`
(`selfCentralizingConjugacyUniversallyClosed_of_valuationLift`).

## Hypotheses and conclusion

Fix `R : CommRingCat.{u}` and `G : GroupScheme (Spec R)`. The hypotheses on `G`,
`m`, `ρ`, `T`, `t`, `D`, `π`, `e`, `M`, `K`, `j` and `f` are word for word those of
`SelfCentralizingConjugacyUniversallyClosedStatement`, in the same order. Its
Markdown and that of `SelfCentralizingConjugacyClosedEmbeddingStatement` explain
them. In brief:

**The group.** `G.X.hom` is smooth, separated and quasi-compact. Every
residue-field group `RelativeIdentityComponent.residueFiber G s` has connected
underlying space and affine structure morphism.

**The representation.** `m : ℕ` and `ρ : MatrixRepresentation G (Fin m)`, with
central kernel: for every test scheme `U : Over (Spec R)` and points
`g h : U ⟶ G.X`, if `g ≫ ρ.hom.hom = 1` then `g * h = h * g`.

**The torus.** `T : CommGroupScheme (Spec R)` and `t : T.toGrp ⟶ G` with
`RelativeTorus.IsTorus T.toGrp`, `IsClosedSubgroup t`,
`IsFibrewiseMaximalTorus t` and `(torusCentralizer t).IsRepresentedBy t`.

**The image torus.** `D : CommGroupScheme (Spec R)`, `π : T.toGrp ⟶ D.toGrp` and
`e : D.toGrp ⟶ GeneralLinear.groupScheme (Fin m) R`. `D` is a torus, `e` is a
closed immersion, the underlying morphism of `π` is flat, surjective and locally
of finite presentation, and `π ≫ e = t ≫ ρ`.

**The scheme of subtori.** `M : Over (Spec R)`, `K : GroupScheme M.left` and
`j : K ⟶ (GroupScheme.baseChange M.hom).obj (GeneralLinear.groupScheme (Fin m) R)`.
`j` is a closed immersion, `K` is a torus and `j` is universal
(`TorusSubgroupModuli.IsUniversal`).

**The conjugacy map.** `f : G.X ⟶ M` satisfies
`TorusSubgroupModuli.evaluate j f = SubgroupFunctor.range (SubgroupFunctor.conjugateFamily e ρ.hom.hom)`.
So `f` classifies the family of subtori `g ↦ ρ(g) e(D) ρ(g)⁻¹` of `GL_m` over
`G.X`.

**The valuative test.** `Ω : Type u` is an algebraically closed field and
`A : ValuationSubring Ω`. Write `ι = Spec.map (CommRingCat.ofHom (algebraMap A Ω))`
for the morphism `Spec Ω ⟶ Spec A`. The data are a scheme morphism
`g : Spec Ω ⟶ G.X.left` and a scheme morphism `b : Spec A ⟶ M.left` with
`ι ≫ b = g ≫ f.left`.

**Conclusion.** There is a scheme morphism `h : Spec A ⟶ G.X.left` with
`h ≫ f.left = b`.

The morphisms `g`, `b` and `h` are morphisms of schemes, not of schemes over
`Spec R`. This loses nothing: `f.left` commutes with the structure morphisms, so
`h ≫ f.left = b` already makes `h` and `b` compatible over `Spec R`, and the same
holds for `g` and `ι ≫ b`. The conclusion does not ask that `ι ≫ h = g`. The
value `f(g)` determines `g` only up to right multiplication by a point of the
normalizer of `T` over `Ω`, and such a point need not extend over `A`. So an
extension of `g` itself need not exist. The reduction module obtains the lift
required by the valuative criterion from `h` and the quotient map `p`, using that
the descended map `φ` is a monomorphism.

In terms of subtori: a closed subtorus of `GL_{m,A}` whose generic fibre is the
conjugate `ρ(g) e(D_Ω) ρ(g)⁻¹` is the conjugate `ρ(h) e(D_A) ρ(h)⁻¹` for some
`h ∈ G(A)`.

## Source correspondence

Write `S = Spec R`. The statement is a consequence of the SGA 3 argument recorded
in the Markdown of `SelfCentralizingConjugacyClosedEmbeddingStatement` and of
`SelfCentralizingConjugacyUniversallyClosedStatement`, together with the
conjugacy of maximal tori over strictly henselian local rings.

1. By Exposé IX, Theorem 6.8, and Exposé XVI, Corollary 2.3, the central kernel
   `K₀` of `ρ` lies in `T` and `G' = G/K₀` exists, with a monomorphism
   `i : G' → GL_m`. By Exposé XVI, Lemma 3.2, and the proofs of Exposé XVI,
   Theorem 3.3(c), and Exposé XV, Theorem 8.15, the scheme `TM_{G'}` of maximal
   tori of `G'` is a closed subscheme of `M`, through `T' ↦ i(T')`. By
   Exposé XII, Theorem 7.1(e) and (f), in the maximal-torus form of Exposé XV,
   Theorem 7.3(iv), `TM_G ≅ TM_{G'}`. So `TM_G` is a closed subscheme of `M`,
   through `T' ↦ ρ(T')`, and `f` factors through it.
2. `A` is a strictly henselian local ring. It is integrally closed in `Ω`, and
   `Ω` is algebraically closed, so every monic polynomial over `A` splits into
   linear factors over `A`. Hence the residue field of `A` is algebraically
   closed, and Hensel's lemma holds over `A`, so `A` is henselian (EGA IV,
   Remark 18.5.13 and Theorem 18.5.11).
3. The point `ι ≫ b = g ≫ f.left` lies in the closed subscheme `TM_G`. Since `A`
   is a domain with fraction field `Ω`, the ideal of `TM_G` pulls back along `b`
   to an ideal of `A` that vanishes in `Ω`, hence is zero. So `b` factors through
   `TM_G` and is the parameter of a maximal torus `T'` of `G_A` with
   `ρ(T') = b`.
4. By Exposé XII, Theorem 7.1(b), the maximal tori `T'` and `T_A` of `G_A` are
   conjugate locally for the étale topology. An étale covering of `Spec A` has a
   member with a point over the closed point, with trivial residue field
   extension because the residue field of `A` is separably closed. That member
   has a section over `Spec A` by EGA IV, Theorem 18.5.11(b). So `T' = h T_A h⁻¹`
   for some `h ∈ G(A)`.
5. Then `h ≫ f.left` is the parameter of `ρ(h) e(D_A) ρ(h)⁻¹ = ρ(T')`, which is
   `b`.

[SGA 3, Exposé XVI, Corollary 2.3](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo16.pdf#page=12),
[Lemma 3.2 and Theorem 3.3](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo16.pdf#page=13);
[Exposé XII, Theorem 7.1](https://wstein.org/sga/SGA3/Expo12.pdf#page=29);
[Exposé XV, Theorems 7.3 and 8.15](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo15.pdf#page=54);
[Exposé IX, Theorem 6.8](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Exp9-8nov09.pdf#page=25);
[EGA IV, Theorem 18.5.11](https://numdam.org/item/10.1007/BF02732123.pdf).

## Provenance of the formulation

SGA 3 does not state this result. It is derived, as above, from the closed
immersion of Exposé XVI, Lemma 3.2, and the conjugacy theorem of Exposé XII,
Theorem 7.1(b). It is a premise of the affineness proof of Task 7782. It
isolates the geometric content of
`SelfCentralizingConjugacyUniversallyClosedStatement`.

The test rings are valuation subrings of algebraically closed fields because the
Library's criterion `Langlands.AlgebraicGeometry.specializingMap_of_algClosed_valuation_lifts`
(module `Langlands.AlgebraicGeometry.AlgClosedValuativeSpecialization`) derives
specialization lifting from lifts against exactly these rings. Mathlib's
`universallyClosed_eq_universallySpecializing` then gives universal closedness
together with quasi-compactness. Over such rings the conjugacy of step 4 holds
globally, which is why the statement can ask for a global `h ∈ G(A)`.

## Registered sources

- SGA 3, Exposé XVI, *Groupes de rang unipotent nul*, Gille–Polo recomposition
  (2008–2009): Corollary 2.3, printed p. 312, one-based PDF p. 12; Lemma 3.2 and
  Theorem 3.3 with proofs, printed pp. 313–315 (original pp. 509–513),
  one-based PDF pp. 13–15. `Expo16.pdf`, `sga3-expose-xvi-gille-polo-2009`,
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
- A. Grothendieck and J. Dieudonné, EGA IV, quatrième partie, Publ. Math. IHÉS 32
  (1967): Theorem 18.5.11, printed pp. 130–131, one-based PDF pp. 129–130;
  Remark 18.5.13, printed p. 132, one-based PDF p. 131.
  `grothendieck-dieudonne-ega-iv4-1967`.

# Universal closedness of the conjugacy map from the normalizer quotient to the subtori of `GL_m`

`Langlands.GroupScheme.SelfCentralizingConjugacyUniversallyClosedStatement.{u}` is a
`Prop`-valued definition. It has the same setting as
`Langlands.GroupScheme.SelfCentralizingConjugacyClosedEmbeddingStatement`. Over
an affine base there is a group `G` with a self-centralizing maximal torus `T`
and a matrix representation `ρ` with central kernel. The statement says that the map
from the quotient `G/N_G(T)` to the scheme of subtori of `GL_m`, which sends the
class of `g` to the conjugate `ρ(g) ρ(T) ρ(g)⁻¹`, is universally closed.

It is the geometric part of the closed-embedding statement. The rest is
formal: the map is a monomorphism and is locally of finite type. The module
`Langlands.GroupScheme.Torus.SelfCentralizingConjugacyClosedEmbeddingReduction`
proves this rest and derives the closed-embedding statement from this one
(`selfCentralizingConjugacyClosedEmbedding_of_universallyClosed`).

## Hypotheses and conclusion

The hypotheses are word for word those of
`SelfCentralizingConjugacyClosedEmbeddingStatement`. Its Markdown explains each
of them. In brief, fix `R : CommRingCat.{u}` and `G : GroupScheme (Spec R)`.

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

**The quotient.** `Y : Over (Spec R)` and `p : G.X ⟶ Y`, where `p.left` is flat,
surjective and locally of finite presentation. For every test scheme `U` and
points `g h : U ⟶ G.X`, `g ≫ p = h ≫ p` holds exactly when
`g⁻¹ * h ∈ (torusNormalizer t).carrier U`.

**Conclusion.** For every morphism `φ : Y ⟶ M` over `Spec R` with `p ≫ φ = f`,
the underlying morphism `φ.left` is universally closed (`UniversallyClosed φ.left`).

The conclusion is not vacuous. Such a `φ` exists, and the reduction module
constructs it as `conjugacyQuotientMap`. It is unique, because `p` is an
epimorphism.

## Source correspondence

Write `S = Spec R`. The SGA 3 argument recorded step by step in the Markdown of
`SelfCentralizingConjugacyClosedEmbeddingStatement` gives a closed immersion
`φ₀ : Y ⟶ M` with `p ≫ φ₀ = f`. In outline:

1. The kernel `K₀` of `ρ` is central, hence lies in the self-centralizing torus
   `T`. It is of multiplicative type by Exposé IX, Theorem 6.8. By Exposé XVI,
   Corollary 2.3, `G' = G/K₀` exists and `ρ` induces a monomorphism
   `i : G' → GL_m`.
2. By Exposé XVI, Lemma 3.2, `T' ↦ i(T')` represents the subtori of `G'` as a
   closed subscheme of `M`. The maximal tori form an open and closed part of it
   (proofs of Exposé XVI, Theorem 3.3(c), and Exposé XV, Theorem 8.15).
3. By Exposé XII, Theorem 7.1(e) and (f), the maximal tori of `G` and of `G'`
   correspond, the maximal-torus form of Exposé XV, Theorem 7.3(iv). By
   Exposé XII, Theorem 7.1(b), maximal tori are conjugate locally for the étale
   topology, so `G/N ≅ TM_G` as in the proof of Exposé XVI, Theorem 4.1(d).
4. Composing, `Y ≅ G/N ≅ TM_G ≅ TM_{G'} → M` is a closed immersion `φ₀`. It
   satisfies `p ≫ φ₀ = f` by the universal property of `j`.

A closed immersion is universally closed. If `p ≫ φ = f`, then `φ = φ₀`,
because `p` is faithfully flat and locally of finite presentation, hence an
epimorphism. So `φ.left` is universally closed.

The substance of the argument is Lemma 3.2 of Exposé XVI. Its proof reduces,
by Exposé XI, 6.10, to the representability of a Weil restriction
`∏_{T/S}(T′/T)` by a closed subscheme of `S`. This statement keeps universal
closedness and drops the properties that need no geometric input here.

[SGA 3, Exposé XVI, Corollary 2.3](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo16.pdf#page=12),
[Lemma 3.2 and Theorem 3.3](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo16.pdf#page=13),
[Theorem 4.1](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo16.pdf#page=18);
[Exposé XII, Theorem 7.1](https://wstein.org/sga/SGA3/Expo12.pdf#page=29);
[Exposé XV, Theorems 7.3 and 8.15](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo15.pdf#page=54);
[Exposé IX, Theorem 6.8](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Exp9-8nov09.pdf#page=25).

## Provenance of the formulation

SGA 3 does not state this as a single result. It is a weakening of
`SelfCentralizingConjugacyClosedEmbeddingStatement`, a premise of the affineness
proof `selfCentralizingTorusConjugacyQuotientAffine`, and is derived from the same SGA 3 argument. It splits that
premise into a geometric part and a formal part. The formal part is proved in
`Langlands.GroupScheme.Torus.SelfCentralizingConjugacyClosedEmbeddingReduction`.
It consists of the descent of `f` along `p`, the monomorphism property, which
gives separatedness, and local finite type. Local finite type follows from that
of `f` by the Library's descent along fppf morphisms of the source,
`Langlands.AlgebraicGeometry.locallyOfFiniteType_of_surjective_flat_locallyOfFinitePresentation_comp`
(Stacks Project, Tag 02KL). Mathlib's `IsClosedImmersion.iff_isProper_and_mono`
then combines the parts.

Two choices in the formulation are deliberate.

- The conclusion quantifies over every `φ` with `p ≫ φ = f` instead of asserting
  that some `φ` exists. Existence is formal, and a proof may use the
  factorization through `p` directly.
- The conclusion is universal closedness only. Separatedness and local finite
  type are formal consequences of the hypotheses, as above, so they are left out
  of the statement.

## Registered sources

- SGA 3, Exposé XVI, *Groupes de rang unipotent nul*, Gille–Polo recomposition
  (2008–2009): Corollary 2.3, printed p. 312, one-based PDF p. 12; Lemma 3.2 and
  Theorem 3.3 with proofs, printed pp. 313–315 (original pp. 509–513),
  one-based PDF pp. 13–15; Theorem 4.1 and the proof of 4.1(d), printed
  pp. 318–319 (original pp. 519–521), one-based PDF pp. 18–19. `Expo16.pdf`,
  `sga3-expose-xvi-gille-polo-2009`,
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

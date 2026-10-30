# Descent of group schemes and abelian schemes to finitely generated subalgebras

This module defines two propositions, for an arbitrary universe `u`. It proves neither. They
use the Library's group schemes `Langlands.GroupScheme S`, which are the group objects
`Grp (Over S)` with their actual multiplication, unit and inverse. They also use its abelian
schemes `Langlands.AbelianScheme S` and the base-change functors
`Langlands.GroupScheme.baseChange` and `Langlands.AbelianScheme.baseChange`. Both functors are
the actual scheme pullback `Over.pullback` with the induced group law.

## Group schemes

`Langlands.GroupScheme.SubalgebraDescentStatement` quantifies over:
- commutative rings `A₀` and `A` in `Type u` with `[Algebra A₀ A]`;
- a scheme `X₀` with a morphism `f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)` that is quasi-compact,
  quasi-separated and locally of finite presentation;
- a group scheme `G : GroupScheme (Spec (CommRingCat.of A))` and a morphism
  `a : G.X.left ⟶ X₀` with
  `IsPullback a G.X.hom f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))`;
- a finite set `s : Finset A`.

So the underlying scheme `G.X.left` of `G` is a base change of `X₀` to `Spec A`, through a
pullback square. The conclusion provides a finitely generated `A₀`-subalgebra `T` of `A`
containing `s`, a group scheme `G₀ : GroupScheme (Spec (CommRingCat.of ↥T))` and a morphism
`a₀ : G₀.X.left ⟶ X₀`, such that:
- `IsPullback a₀ G₀.X.hom f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))`, so the
  underlying scheme of `G₀` is a base change of `X₀` to `Spec T`;
- `IsCommMonObj G.X → IsCommMonObj G₀.X`, so `G₀` is commutative when `G` is;
- `Nonempty (G ≅ (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ↥T A)))).obj G₀)`.
  This is an isomorphism in `GroupScheme (Spec (CommRingCat.of A))`, that is, of group objects
  over `Spec A`. It is compatible with multiplication, unit and inverse.

The proposition does not relate this isomorphism to `a` and `a₀`.

## Abelian schemes

`Langlands.AbelianScheme.SubalgebraDescentStatement` says: for every commutative ring
`R : CommRingCat.{u}` and every abelian scheme `A : AbelianScheme (Spec R)`, there are a
subalgebra `R₀ : Subalgebra ℤ R` with `R₀.FG` and an abelian scheme
`A₀ : AbelianScheme (Spec (CommRingCat.of ↥R₀))` with

```lean
Nonempty (A ≅ (AbelianScheme.baseChange
  (Spec.map (CommRingCat.ofHom (algebraMap ↥R₀ R)))).obj A₀)
```

Here `R₀` is a finitely generated subring of `R`, hence a noetherian ring by the Hilbert basis
theorem. The isomorphism lives in the category `AbelianScheme (Spec R)`, whose morphisms are
the homomorphisms of the underlying commutative group schemes. So `A` is the base change of
`A₀` along `Spec R ⟶ Spec R₀`, as a group scheme over `Spec R`. The abelian-scheme structure of
`A₀` includes its commutativity, smoothness, properness and geometric connectedness over
`Spec R₀`.

## Sources and provenance

Both propositions are derived, from the Stacks Project, Chapter 32 *Limits of Schemes*,
`limits.tex` at commit `a04446e57ec1fbc252a871afcec7752fb2807b14` (registered as
`stacks-limits-of-schemes-a04446e5`; tags from its `tags-limits.txt`). `Spec R` is the limit of
the affine schemes `Spec T`, where `T` runs over the directed set of finitely generated
subalgebras.

- Lemma 32.10.1 (tag 01ZM, label `lemma-descend-finite-presentation`, line 2370). Part (1)
  descends a scheme of finite presentation. Part (2) descends a morphism between base changes
  of schemes of finite presentation. Part (3) descends an equality of such morphisms.
- For the group-scheme proposition, part (2) descends the multiplication
  `G ×_A G ⟶ G`, the unit `Spec A ⟶ G` and the inverse `G ⟶ G`. All of them are morphisms
  between base changes of the finitely presented `X₀`, `X₀ ×_{A₀} X₀` and `Spec A₀`. Part (3)
  then descends the group axioms, the commutativity equation when `G` is commutative, and the
  compatibility of the comparison isomorphism with the group law. All of these are equalities
  of such morphisms.
- For the abelian-scheme proposition, apply part (1) with `A₀ = ℤ`; the structure morphism of
  an abelian scheme is of finite presentation and quasi-compact and separated. Then descend the
  group law as above. Then descend smoothness (Lemma 32.8.9, tag 0C0C, line 1931), separatedness
  (Lemma 32.8.6, tag 01ZQ, line 1851) and properness (Lemma 32.13.1, tag 081F, line 3265).
  Geometric connectedness of the fibres descends by the local constancy of the number of
  geometric connected components of a smooth proper morphism (Stacks Project *More on
  Morphisms*, Lemma `lemma-proper-flat-geom-red`, tag 0E0N, `more-morphisms.tex` at the same
  commit, lines 15425–15436, registered as `stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`).
  This is combined with Lemma 32.4.10 (tag 05F4, label `lemma-limit-contained-in-constructible`,
  line 530). Finitely generated `ℤ`-algebras are noetherian, so the noetherian base needed by
  the properness and connectedness steps is available.

The source argument above records the descent steps used to formulate these
two statements.

Implementation lead, not a proof source: the Anthropic FLT Lean source at revision
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered as
`anthropic-flt-complete-lean-source-6e837e75`, Apache-2.0) proves the group-law step for its
own `GoodReductionJacobian.RelativeGroupLaw`, in
`GoodReductionJacobian.RelativeGroupLaw.exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation`.
It proves the combined scheme-and-property step in
`AlgebraicGeometry.exists_fg_subalgebra_isPullback_smooth_isProper_geometricallyConnected` and
`GoodReductionJacobian.RelativeGroupLaw.exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing`.
The propositions here are stated for the Library's group objects `Grp (Over S)` instead.

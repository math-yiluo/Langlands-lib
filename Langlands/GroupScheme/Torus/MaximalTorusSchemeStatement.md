# Statement: the scheme of maximal tori of a reductive group scheme

Worker 75.

`Langlands.GroupScheme.MaximalTorusSchemeStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports [`Torus.FieldPointMaximality`](FieldPointMaximality.md)
(for `IsFibrewiseMaximalTorus`),
[`HomScheme.TorusSubgroupModuli`](../HomScheme/TorusSubgroupModuli.md) (for
`TorusSubgroupModuli.evaluate` and, through it, `RelativeTorus.IsTorus`) and Mathlib's
`AlgebraicGeometry.QuasiAffine` (for `Scheme.IsQuasiAffine`).

## Statement and quantifiers

The proposition quantifies over every scheme `S : Scheme.{u}` and every group scheme
`G : GroupScheme S`. It has one hypothesis: `IsReductive G`
([`Reductive.Basic`](../Reductive/Basic.md)). This says that `G` is smooth and affine over
`S` and that its geometric fibres are connected reductive groups.

The conclusion is that there are an `S`-scheme `M : Over S`, a commutative group scheme
`K : CommGroupScheme M.left` and a homomorphism
`j : K.toGrp ⟶ (GroupScheme.baseChange M.hom).obj G` into the base change `G_M` with the
following properties.

1. **`j` is a maximal torus of `G_M`.** `RelativeTorus.IsTorus K.toGrp`,
   `IsClosedSubgroup j` and `IsFibrewiseMaximalTorus j`. So `K` becomes a split torus on
   some étale cover of `M`, `j` is a closed immersion, and for every point `m` of `M` the
   residue fibre of `j` over `κ(m)` satisfies the field predicate `IsMaximalTorus`
   ([`Torus.Maximal`](Maximal.md)).
2. **Universality.** Let `T : Over S` be any `S`-scheme, `T' : CommGroupScheme T.left` and
   `t : T'.toGrp ⟶ (GroupScheme.baseChange T.hom).obj G`, with
   `RelativeTorus.IsTorus T'.toGrp`, `IsClosedSubgroup t` and
   `IsFibrewiseMaximalTorus t`. Then there is exactly one morphism `a : T ⟶ M` over `S`
   such that `TorusSubgroupModuli.evaluate j a = SubgroupFunctor.range t`. Here
   `evaluate j a` is the subgroup functor of `G_T` given by the image of the pullback of
   `j` along `a`, identified with a subgroup of `G_T` through the canonical comparison of
   iterated pullbacks. The equality says that on every test scheme over `T` the pulled-back
   universal torus and `T'` have the same points.
3. **`M ⟶ S` is smooth and surjective.** `Smooth M.hom` and `Surjective M.hom`.
4. **`M ⟶ S` is quasi-affine.** For every affine open `V` of `S`, the open subscheme
   `M.hom ⁻¹ᵁ V` of `M.left` satisfies Mathlib's `Scheme.IsQuasiAffine`. That predicate
   says the scheme is quasi-compact and its canonical morphism to `Spec` of its global
   sections is an immersion.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
printed page numbers, which agree with the one-based PDF page numbers of this file.

- Theorem 3.2.6, p.94, first paragraph: "Let G → S be a smooth S-affine group scheme such
  that in the identity component G⁰_s̄ of each geometric fiber the maximal tori are their
  own centralizers. Then the functor on S-schemes Tor_{G/S} : S′ ⇝ {maximal tori in G_S′}
  is represented by a smooth quasi-affine S-scheme Tor_{G/S}, and Tor_{G/S} → S is
  surjective." The next sentence of the source says that the case of main interest is
  reductive group schemes.
- Definition 3.1.1, p.81: tori, and reductive `S`-groups as smooth `S`-affine groups whose
  geometric fibres are connected reductive groups.
- Definition 3.2.1, p.91: a maximal torus of a smooth `S`-affine group is a torus whose
  geometric fibres are maximal. After Proposition 3.2.2, the source notes that this
  condition can be checked after any surjective base change.
- Remark 2.3.2, p.67: quasi-affine morphisms, following EGA II, 5.1.1.
- Remark A.1.2, p.267: over a field `k`, maximality of a `k`-torus in the geometric sense
  of Definition 3.2.1 is the same as maximality among `k`-tori.
- Proposition B.3.4, pp.290–291: a group of multiplicative type is diagonalizable
  étale-locally on the base.
- Lemma B.1.3, p.281: a monic homomorphism from a group of multiplicative type to an
  `S`-affine `S`-group of finite presentation is a closed immersion.

The Stacks Project is cited only for the standard form of quasi-affineness used in
property 4. The cited pages are registered as `stacks-quasi-affine-01P6-01SK-01SM`
(HTML snapshot of Tags 01P6, 01SK and 01SM, 2026-11-13). The Stacks Project defines a
quasi-affine scheme as a quasi-compact scheme isomorphic to an open subscheme of an affine
scheme (Definition 28.19.1, Tag 01P6; Mathlib's `IsQuasiAffine`
carries this tag). It defines a quasi-affine morphism by asking that the inverse image of
every affine open be a quasi-affine scheme (Definition 29.13.1, Tag 01SK). Lemma 29.13.3
(Tag 01SM) shows that it suffices to check this on one affine open cover. That is the form
of the definition in Conrad's Remark 2.3.2, which follows EGA II, 5.1.1: over the members of
some affine open cover of the target, the map factors as a quasi-compact open immersion into
an affine scheme.

## Derivation from the source

The proposition is the first paragraph of Theorem 3.2.6 for reductive group schemes. These
satisfy the theorem's hypothesis: in a connected reductive group over an algebraically
closed field, a maximal torus is its own centralizer. The proposition does not state the
theorem for other groups.

Representability of the functor `Tor_{G/S}` is expressed by a universal maximal torus `j`
over `M`. Property 1 says that `j` gives an element of `Tor_{G/S}(M)`. Property 2 says that
every element of `Tor_{G/S}(T)` is the pullback of `j` along exactly one `S`-morphism
`T ⟶ M`. Since maximality is stable under base change (Definition 3.2.1 is a condition on
geometric fibres), every pullback of `j` is again a maximal torus. So `a ↦ evaluate j a` is
a bijection from `S`-morphisms `T ⟶ M` to `Tor_{G/S}(T)`, and `M` represents
`Tor_{G/S}`. Two subgroups of `G_T` count as the same element of `Tor_{G/S}(T)` exactly
when their images agree on every test scheme.

Maximal tori are encoded as in the other relative maximal-torus statements of the Library:

- an `S`-torus in the sense of Definition 3.1.1 is étale-locally split by Proposition B.3.4,
  and conversely, which gives `RelativeTorus.IsTorus`;
- by Lemma B.1.3 a torus mapping monically to the affine finitely presented `G_T` is a
  closed subgroup, so requiring `IsClosedSubgroup` adds nothing;
- maximality is required on residue fibres (`IsFibrewiseMaximalTorus`) rather than on
  geometric fibres, and by Remark A.1.2 the two agree fibre by fibre.

## Scope

All objects are in universe `u`, and the base `S` is an arbitrary scheme. The proposition
covers only the first paragraph of Theorem 3.2.6, for reductive `G`. It does not state
the theorem under the source's weaker hypothesis on smooth `S`-affine groups. It does not
state the second paragraph, the isomorphism `G/N_G(T) ≅ Tor_{G/S}` for a given maximal
torus `T` or the resulting étale-local conjugacy. It does not state SGA 3's finer
assertion that `Tor_{G/S}` is `S`-affine, which the source mentions without proof.

## Relation to the Library

- [`HomScheme.SmoothTorusSubgroupRepresentabilityStatement`](../HomScheme/SmoothTorusSubgroupRepresentabilityStatement.md)
  states the analogous representability for all closed relative-torus subgroups of a smooth
  affine group. It uses the same `TorusSubgroupModuli.evaluate` and the Library predicate
  `TorusSubgroupModuli.IsUniversal`. This proposition asks for universality only among
  maximal tori.
- [`Torus.EtaleLocalMaximalConjugacyStatement`](EtaleLocalMaximalConjugacyStatement.md)
  states the étale-local conjugacy of maximal tori from the second paragraph of
  Theorem 3.2.6.
- [`Torus.EtaleLocalMaximalExistenceStatement`](EtaleLocalMaximalExistenceStatement.md)
  states Corollary 3.2.7, which the source deduces from this theorem.

This module proves none of these relations.

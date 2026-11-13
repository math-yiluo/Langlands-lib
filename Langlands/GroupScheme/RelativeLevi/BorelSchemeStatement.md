# Statement: the scheme of Borel subgroups of a reductive group scheme

Worker 75.

`Langlands.GroupScheme.RelativeBorelSchemeStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports [`RelativeLevi.Borel`](Borel.md) (for
`IsRelativeBorelSubgroup`),
[`HomScheme.TorusSubgroupModuli`](../HomScheme/TorusSubgroupModuli.md) (for
`TorusSubgroupModuli.evaluate`) and Mathlib's `AlgebraicGeometry.Morphisms.Proper` (for
`IsProper`).

## Statement and quantifiers

The proposition quantifies over every scheme `S : Scheme.{u}` and every group scheme
`G : GroupScheme S`. It has one hypothesis: `IsReductive G`
([`Reductive.Basic`](../Reductive/Basic.md)). This says that `G` is smooth and affine over
`S` and that its geometric fibres are connected reductive groups.

The conclusion is that there are an `S`-scheme `M : Over S`, a group scheme
`B : GroupScheme M.left` and a homomorphism
`j : B ⟶ (GroupScheme.baseChange M.hom).obj G` into the base change `G_M` with the
following properties.

1. **`j` is a Borel subgroup of `G_M`.** `IsRelativeBorelSubgroup j`
   ([`RelativeLevi.Borel`](Borel.md)): `j` is a parabolic subgroup in the sense of
   `IsRelativeParabolicSubgroup` (`B` is smooth and affine over `M`, `j` is a
   monomorphism, and its residue fibres are parabolic), and for every point `m` of `M` the
   residue fibre of `j` over `κ(m)` satisfies `IsGeometricBorelSubgroup`.
2. **Universality.** Let `T : Over S` be any `S`-scheme, `B' : GroupScheme T.left` and
   `i : B' ⟶ (GroupScheme.baseChange T.hom).obj G` with `IsRelativeBorelSubgroup i`.
   Then there is exactly one morphism `a : T ⟶ M` over `S` such that
   `TorusSubgroupModuli.evaluate j a = SubgroupFunctor.range i`.
   Here `evaluate j a` is the subgroup functor of `G_T` given by the image of the pullback
   of `j` along `a`, identified with a subgroup of `G_T` through the canonical comparison of
   iterated pullbacks. The definition of `evaluate` applies to any group scheme over `M`
   with a homomorphism to `G_M`, not only to tori. The equality says that on every test
   scheme over `T` the pulled-back universal subgroup and `B'` have the same points.
3. **`M ⟶ S` is smooth and proper.** `Smooth M.hom` and `IsProper M.hom` (Mathlib).

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the one-based PDF pages, which agree with the printed page numbers.

- Theorem 5.2.11(3), p.158: "The functor on S-schemes Bor_{G/S} : S′ ⇝ {Borel subgroups
  of G_{S′}} is represented by a smooth proper S-scheme Bor_{G/S} equipped with the
  canonical S-ample line bundle det(Lie(B))∗, where B ⊂ G × Bor_{G/S} is the universal
  Borel subgroup of G." The hypothesis of Theorem 5.2.11, p.157, is "Let G → S be a
  reductive group scheme."
- Proof of Theorem 5.2.11, p.158: "Bor_{G/S} is the open and closed subscheme of
  Par_{G/S} over which fibers of the universal parabolic subgroup are Borel subgroups
  (use part (1))."
- Definition 5.2.10, p.157: "A Borel subgroup of a reductive group scheme G → S is a
  parabolic subgroup P ⊂ G such that P_s is a Borel subgroup of G_s for all s ∈ S." Its
  transcription is the published `IsRelativeBorelSubgroup`, which reads "Borel subgroup of
  `G_s`" as `IsGeometricBorelSubgroup`, as explained in [`RelativeLevi.Borel`](Borel.md).

## Derivation from the source

The proposition is Theorem 5.2.11(3) without the ample line bundle.

Representability of the functor `Bor_{G/S}` is expressed by a universal Borel subgroup `j`
over `M`. Property 1 says that `j` gives an element of `Bor_{G/S}(M)`. Property 2 says
that every element of `Bor_{G/S}(T)` is the pullback of `j` along exactly one
`S`-morphism `T ⟶ M`. Being a Borel subgroup is stable under base change: being parabolic
is, and every residue fibre of a pullback of `j` is the base change of a residue fibre of
`j` along an extension of fields; `IsGeometricBorelSubgroup` asks that the base change to
an algebraic closure be a Borel subgroup, so it is preserved. So `a ↦ evaluate j a` is a
bijection from `S`-morphisms `T ⟶ M` to `Bor_{G/S}(T)`, and `M` represents `Bor_{G/S}`.
Each element of `Bor_{G/S}(T)` is a subgroup of `G_T`, given in the Library as an abstract
group scheme with a monomorphism into `G_T`. Two such monomorphisms define the same
subgroup exactly when their images agree on every test scheme, so subgroups are compared
through `SubgroupFunctor.range`, as in the other uniqueness statements of this directory.

The encoding of the universal family follows the published
[`Torus.MaximalTorusSchemeStatement`](../Torus/MaximalTorusSchemeStatement.md), which
represents the functor of maximal tori (Conrad, Theorem 3.2.6) in the same way.

## Scope

All objects are in universe `u`, and the base `S` is an arbitrary scheme. The proposition
does not state that `det(Lie(B))∗` is an `S`-ample line bundle on `M`: the Library has no
Lie algebra of a group scheme over a general base as a quasi-coherent sheaf. It does not
state that `M` is an open and closed subscheme of the scheme of parabolic subgroups, which
the source uses in its proof.

## Relation to the Library

- [`RelativeParabolicSchemeStatement`](ParabolicSchemeStatement.md) states the
  representability of the functor of parabolic subgroups (Corollary 5.2.9), from which the
  source deduces this proposition.
- [`RelativeBorelLocusClopenStatement`](BorelLocusStatement.md) states Theorem 5.2.11(1),
  the openness and closedness of the Borel locus of a parabolic subgroup, which the
  source's proof uses.
- [`RelativeBorelEtaleLocalConjugacyStatement`](BorelConjugacyStatement.md) states
  Theorem 5.2.11(2).
- [`Torus.MaximalTorusSchemeStatement`](../Torus/MaximalTorusSchemeStatement.md) states the
  representability of the functor of maximal tori with the same encoding.

This module proves none of these relations.

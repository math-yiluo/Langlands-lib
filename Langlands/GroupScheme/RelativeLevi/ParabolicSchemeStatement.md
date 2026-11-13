# Statement: the scheme of parabolic subgroups of a reductive group scheme

Worker 75.

`Langlands.GroupScheme.RelativeParabolicSchemeStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports [`RelativeLevi.Basic`](Basic.md) (for
`IsRelativeParabolicSubgroup`),
[`HomScheme.TorusSubgroupModuli`](../HomScheme/TorusSubgroupModuli.md) (for
`TorusSubgroupModuli.evaluate`) and Mathlib's `AlgebraicGeometry.Morphisms.Proper` (for
`IsProper`).

## Statement and quantifiers

The proposition quantifies over every scheme `S : Scheme.{u}` and every group scheme
`G : GroupScheme S`. It has one hypothesis: `IsReductive G`
([`Reductive.Basic`](../Reductive/Basic.md)). This says that `G` is smooth and affine over
`S` and that its geometric fibres are connected reductive groups.

The conclusion is that there are an `S`-scheme `M : Over S`, a group scheme
`P : GroupScheme M.left` and a homomorphism
`j : P ⟶ (GroupScheme.baseChange M.hom).obj G` into the base change `G_M` with the
following properties.

1. **`j` is a parabolic subgroup of `G_M`.** `IsRelativeParabolicSubgroup j`
   ([`RelativeLevi.Basic`](Basic.md)): `P` is smooth and affine over `M`, `j` is a
   monomorphism, and for every point `m` of `M` the residue fibre of `j` over `κ(m)`
   satisfies the field predicate `IsParabolicSubgroup`.
2. **Universality.** Let `T : Over S` be any `S`-scheme, `Q : GroupScheme T.left` and
   `i : Q ⟶ (GroupScheme.baseChange T.hom).obj G` with `IsRelativeParabolicSubgroup i`.
   Then there is exactly one morphism `a : T ⟶ M` over `S` such that
   `TorusSubgroupModuli.evaluate j a = SubgroupFunctor.range i`.
   Here `evaluate j a` is the subgroup functor of `G_T` given by the image of the pullback
   of `j` along `a`, identified with a subgroup of `G_T` through the canonical comparison of
   iterated pullbacks. The definition of `evaluate` applies to any group scheme over `M`
   with a homomorphism to `G_M`, not only to tori. The equality says that on every test
   scheme over `T` the pulled-back universal subgroup and `Q` have the same points.
3. **`M ⟶ S` is smooth and proper.** `Smooth M.hom` and `IsProper M.hom` (Mathlib).

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the one-based PDF pages, which agree with the printed page numbers.

- Corollary 5.2.9, p.156: "Let G → S be a reductive group scheme. The functor on
  S-schemes Par_{G/S} : S′ ⇝ {parabolic subgroups of G_{S′}} is represented by a smooth
  proper S-scheme Par_{G/S} equipped with the canonical S-ample line bundle det(Lie(P))∗,
  where P ⊂ G × Par_{G/S} is the universal parabolic subgroup of G."
- Proof of Corollary 5.2.9, p.157. Étale-locally on `S`, `G` is split and
  `Par_{G/S} = ∐_j G/P_G(λ_j)` for finitely many cocharacters `λ_j`, using
  Corollary 5.2.7 (parabolic subgroups are étale-locally conjugate to some `P_G(λ_j)`) and
  Corollary 5.2.8 (`G/P` exists as a smooth proper `S`-scheme); the ample line bundle
  gives effective descent.
- Definition 5.2.1, p.151: "A parabolic subgroup of a reductive group scheme G → S is a
  smooth S-affine S-group P equipped with a monic homomorphism P → G such that P_s is
  parabolic in G_s (i.e., G_s/P_s is proper) for all s ∈ S." Its transcription is the
  published `IsRelativeParabolicSubgroup`.

## Derivation from the source

The proposition is Corollary 5.2.9 without the ample line bundle.

Representability of the functor `Par_{G/S}` is expressed by a universal parabolic subgroup
`j` over `M`. Property 1 says that `j` gives an element of `Par_{G/S}(M)`. Property 2 says
that every element of `Par_{G/S}(T)` is the pullback of `j` along exactly one `S`-morphism
`T ⟶ M`. Parabolicity is stable under base change: smoothness, affineness and being a
monomorphism are stable, and every residue fibre of a pullback of `j` is the base change
of a residue fibre of `j` along an extension of fields, which is again parabolic because
properness of `G_s/P_s` is stable under extension of the base field. So `a ↦ evaluate j a` is a bijection
from `S`-morphisms `T ⟶ M` to `Par_{G/S}(T)`, and `M` represents `Par_{G/S}`. Each
element of `Par_{G/S}(T)` is a subgroup of `G_T`, given in the Library as an abstract
group scheme with a monomorphism into `G_T`. Two such monomorphisms define the same
subgroup exactly when their images agree on every test scheme, so subgroups are compared
through `SubgroupFunctor.range`, as in the other uniqueness statements of this directory.

The encoding of the universal family follows the published
[`Torus.MaximalTorusSchemeStatement`](../Torus/MaximalTorusSchemeStatement.md), which
represents the functor of maximal tori (Conrad, Theorem 3.2.6) in the same way.

## Scope

All objects are in universe `u`, and the base `S` is an arbitrary scheme. The proposition
does not state that `det(Lie(P))∗` is an `S`-ample line bundle on `M`: the Library has
no Lie algebra of a group scheme over a general base as a quasi-coherent sheaf. It does not
state the decomposition `Par_{G/k} = ∐ G/P_i` over an algebraically closed field from the
remark after the corollary.

## Relation to the Library

- [`RelativeParabolicQuotient.ExistenceStatement`](../RelativeParabolicQuotientStatement.md)
  states the existence of the proper quotient `G/P` over an affine base (Corollary 5.2.8
  with Theorem 2.3.6), which the source's proof uses on each piece of `Par_{G/S}`.
- [`RelativeParabolicEtaleLocalConjugacyStatement`](ParabolicEtaleConjugacyStatement.md)
  states Corollary 5.2.7(1), also used in the source's proof.
- The analogous representability of the functor of Borel subgroups
  (Theorem 5.2.11(3)) is the planned companion `RelativeBorelSchemeStatement`.
- [`Torus.MaximalTorusSchemeStatement`](../Torus/MaximalTorusSchemeStatement.md) states the
  representability of the functor of maximal tori with the same encoding.

This module proves none of these relations.

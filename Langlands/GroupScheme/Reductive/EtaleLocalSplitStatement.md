# Statement: reductive group schemes split étale-locally on the base

Worker 75.

`Langlands.GroupScheme.EtaleLocalSplitReductiveStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`Reductive.FibrewiseRootDatum`](FibrewiseRootDatum.md), for `IsFibrewiseRootDatumOf`.
  Through its imports this also supplies `splitTorus.exponentWeightSpace`
  ([`Torus.RelativeAdjointWeights`](../Torus/RelativeAdjointWeights.md));
- [`Reductive.Basic`](Basic.md), for `IsReductive`;
- [`Torus.FieldPointMaximality`](../Torus/FieldPointMaximality.md), for
  `IsFibrewiseMaximalTorus`.

## Statement and quantifiers

The proposition quantifies over every scheme `S : Scheme.{u}`, every group scheme
`G : GroupScheme S` with a proof `hG : IsReductive G`, and every point `s : S`.
`IsReductive G` says that `G` is smooth and affine over `S` and that every geometric fibre
is a connected reductive group. The field `hG.isAffineHom` supplies the instance
`IsAffineHom G.X.hom`. It is not an extra hypothesis.

The conclusion asserts that there exist:

- a commutative ring `R : Type u` and a morphism `f : Spec R ⟶ S` such that `f` is étale
  (`Etale f`) and some point `x` of `Spec R` maps to `s` (`f.base x = s`). The base change
  `G_R := (GroupScheme.baseChange f).obj G` is a group scheme over `Spec R`. Its structure
  morphism is the pullback of `G.X.hom` along `f`, so it is affine. The statement uses
  `inferInstanceAs` to install this instance; it is not an extra hypothesis either;
- a finite type `I : Type u` and a homomorphism `i : splitTorus (Spec R) I ⟶ G_R` from the
  coordinate split torus `𝔾_m^I` over `Spec R`;
- a type `J : Type u` and a Mathlib root datum `P : RootDatum J (I → ℤ) (I → ℤ)` on the
  full coordinate lattices.

These data satisfy four conditions.

1. `IsClosedSubgroup i`: the underlying morphism of schemes of `i` is a closed immersion.
2. `IsFibrewiseMaximalTorus i`, with source the commutative group scheme
   `splitTorus.commGroupScheme (Spec R) I`: for every point `y` of `Spec R` the pullback of
   `i` to the residue field `κ(y)` satisfies `IsMaximalTorus`. In that fibre the torus is
   a closed subgroup and factors through no strictly larger closed `κ(y)`-torus of the
   fibre of `G_R`.
3. `IsFibrewiseRootDatumOf I G_R i P`: `J` is finite and `P` is reduced. For every field
   `k : Type u` with an `R`-algebra structure, the realization of `P` on the actual
   character and cocharacter lattices of `𝔾_m^I` over `k` is the root datum of the base
   change of `i` to `k` (`IsRootDatumOf`). So the pairing of `P` is the standard lattice
   pairing, and the roots of `P` are exactly the fixed-exponent characters that are the
   nonzero weights of the torus on the Lie algebra of `G_k`. Every reflection of `P` is the
   action on characters of some `k`-rational point of `G_k` that normalizes the torus.
4. For every `α : J` there is an `R`-linear isomorphism
   `splitTorus.exponentWeightSpace I G_R i (P.root α) ≃ₗ[R] R`. Here
   `exponentWeightSpace I G_R i m` is the `R`-submodule of the actual Lie module
   `Additive (lieKernel G_R R)`, the kernel of `G_R(R[ε]) → G_R(R)`. Its vectors satisfy
   the adjoint weight equation with exponent monomial `m` for every commutative
   `R`-algebra and every point of the split torus over it. So the root space with root
   `P.root α` is free of rank one over `R`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
printed page numbers, which agree with the one-based PDF page numbers of this file.

- Lemma 5.1.3, p.136: "Any reductive group scheme over a non-empty scheme becomes split
  étale-locally on the base." The proof on p.137 takes a maximal torus étale-locally
  (Corollary 3.2.7) and splits it by a further étale localization, `T ≃ D_S(M)`. It then
  localizes Zariski-locally twice: first so that the nontrivial weights on `g` come from
  `M` and the root spaces `g_a` have constant rank 1, and then so that the coroots come
  from `M^∨`.
- Definition 5.1.1, p.136: a reductive `G` over a non-empty `S` is split if there is a
  maximal torus `T` with an isomorphism `T ≃ D_S(M)` for a finite free `ℤ`-module `M`
  such that (1) the nontrivial weights of `T` on `g` arise from elements of `M`, (2) each
  root space `g_a` is free of rank 1 over `O_S`, and (3) each coroot arises from an element
  of `M^∨`.
- p.138, before Proposition 5.1.6: the set of elements of `M` occurring in condition (1)
  is `Φ`, and `g = t ⊕ (⊕_{a ∈ Φ} g_a)`. Proposition 5.1.6, p.138: `(M, Φ, M^∨, Φ^∨)` is a
  reduced root datum.
- Corollary 5.1.11, p.142: for a split group the reflection `s_a` is the image of a point
  `n_a ∈ N_G(T)(S)`.
- Definition 3.2.1, p.91 (maximal tori via geometric fibres); Remark A.1.2, p.267
  (geometric maximality agrees with maximality among tori over a field); Lemma B.1.3,
  p.281 (a monic homomorphism from a group of multiplicative type to an affine finitely
  presented group is a closed immersion).

## Derivation from the source

The statement is derived from Lemma 5.1.3; it is not a quotation. The encoding has three
parts.

**"Étale-locally on the base".** This means an étale covering family `{S_j → S}` such
that each `G_{S_j}` is split. The proposition states instead that every point `s` lies in
the image of an étale `f : Spec R → S` with `G_R` split. The two forms are equivalent.
Étale morphisms are open, so such maps for all points form an étale covering family.
Conversely, splitness in the sense of Definition 5.1.1 is stable under base change, in
particular under restriction to an affine open of `S_j`. The isomorphism `T ≃ D_S(M)`
base changes, the weights and coroots stay the same elements of `M` and `M^∨`, and a free
rank-one root space stays free of rank one because formation of `g` and of its weight
spaces commutes with base change for smooth `G`. The Library's
[`Torus.RelativeAdjointWeightBaseChange`](../Torus/RelativeAdjointWeightBaseChange.md)
proves this weight-space base change. The empty base needs no separate treatment: if `S`
is empty, the proposition says nothing.

**Split over `Spec R`.** A basis of the finite free module `M` gives `M ≅ ℤ^I` and
`D_S(M) ≅ 𝔾_m^I`, so the split torus is taken in coordinates.

- Conditions 1 and 2 encode "maximal torus" as in the Library's other relative statements.
  Conrad's maximal torus is a subgroup and hence closed by Lemma B.1.3. Maximality on
  residue fibres agrees with geometric maximality by Remark A.1.2.
- Condition 3 encodes Definition 5.1.1(1) and (3) together with Proposition 5.1.6 and
  Corollary 5.1.11. Given a split `(G, T, M)`, Proposition 5.1.6 makes `(M, Φ, M^∨, Φ^∨)`
  a reduced root datum. Weights and coroots are constant, and formation of `g` and its
  weight spaces commutes with base change. So this datum is the root datum of every
  field-valued fibre, and Corollary 5.1.11 over that field gives the normalizing points.
  Conversely, condition 3 makes the nonzero weights and the coroots on every fibre the
  fixed elements `P.root α` and `P.coroot α`. A weight in the exponent decomposition that
  vanishes on every fibre has zero weight space. This holds because that weight space is a
  direct summand of the finitely generated projective module `Lie(G_R)`, so Nakayama's
  lemma applies. Hence the nontrivial weights occurring on `g` are exactly the `P.root α`,
  and conditions (1) and (3) of Definition 5.1.1 hold.
- Condition 4 is Definition 5.1.1(2) for the roots `P.root α`.

**Universe.** The ring `R`, the coordinate type `I`, the root index type `J`, and the
fields in `IsFibrewiseRootDatumOf` are all in the universe `u` of `S`.

## Scope

The proposition fixes neither the torus nor the root datum, and it allows different `R`,
`I` and `P` for different points `s`. It does not assert that the étale maps can be
chosen with a common root datum, and it says nothing about uniqueness or about pinnings.
The example after Lemma 5.1.3 on p.137 (a connected reductive group over a field splits
over a finite separable extension) and Example 5.1.4 are not stated.

## Relation to the Library

- [`Reductive.LocalSplitRootDatumExistenceStatement`](LocalSplitRootDatumExistenceStatement.md)
  supplies the root datum when a split coordinate torus is already given over a local
  ring. The present statement supplies the torus, étale-locally, over an arbitrary base.
- [`Reductive.StrictHenselianGenericIsoStatement`](StrictHenselianGenericIsoStatement.md)
  cites Lemma 5.1.3 among its sources. It is a statement over strictly henselian local
  domains and does not state the lemma itself.

This module proves none of these relations.

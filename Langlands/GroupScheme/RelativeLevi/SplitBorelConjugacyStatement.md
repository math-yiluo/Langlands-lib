# Statement: Zariski-local conjugacy of Borel subgroups of split reductive groups

Worker 75.

`Langlands.GroupScheme.SplitBorelZariskiLocalConjugacyStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports [`RelativeLevi.Borel`](Borel.md) (for
`IsRelativeBorelSubgroup`),
[`Reductive.FibrewiseRootDatum`](../Reductive/FibrewiseRootDatum.md) (for
`IsFibrewiseRootDatumOf` and, through it, `splitTorus` and
`splitTorus.exponentWeightSpace`),
[`Torus.FieldPointMaximality`](../Torus/FieldPointMaximality.md) (for
`IsFibrewiseMaximalTorus`), [`Rational.TorusNormalizer`](../Rational/TorusNormalizer.md)
(for `SubgroupFunctor.normalizer`) and [`InnerAutomorphism`](../InnerAutomorphism.md) (for
`GroupScheme.innerIso`).

## Statement and quantifiers

The proposition quantifies over:

- every commutative ring `R : Type u`, with base scheme `Spec R`;
- every group scheme `G : GroupScheme (Spec R)` with `hG : IsReductive G`
  ([`Reductive.Basic`](../Reductive/Basic.md)): `G` is smooth and affine over `Spec R`,
  and its geometric fibres are connected reductive groups;
- every finite type `I : Type u` and homomorphism `t : splitTorus (Spec R) I ⟶ G` from the
  split torus `𝔾_m^I` over `Spec R`;
- every type `J : Type u` and every root datum `P : RootDatum J (I → ℤ) (I → ℤ)` on the
  coordinate character and cocharacter lattices of `𝔾_m^I`.

It has four hypotheses on these data, which together say that `(G, t, P)` is split. They
are the hypotheses of the Library's encoding of Conrad's Definition 5.1.1 used in
[`Reductive.EtaleLocalSplitStatement`](../Reductive/EtaleLocalSplitStatement.md):

1. `IsClosedSubgroup t`: the underlying morphism of schemes of `t` is a closed immersion.
2. `IsFibrewiseMaximalTorus t`: for every point `s` of `Spec R`, the residue fibre of `t`
   over `κ(s)` satisfies the field predicate `IsMaximalTorus`.
3. `IsFibrewiseRootDatumOf I G t P`: `J` is finite, `P` is reduced, and for every field
   `k` with a ring homomorphism `R → k`, the realization of `P` over `k` is the root datum
   of the base change of `t` to `k`. So the roots and coroots of `(G, T)` on every fibre
   are the constant elements of `P`.
4. For every `α : J`, the weight space `splitTorus.exponentWeightSpace I G t (P.root α)`
   of the torus acting on the Lie algebra of `G` (with weight `P.root α`) is isomorphic to
   `R` as an `R`-module, that is, free of rank one.

The conclusion is the conjunction of two assertions. In both, for an open subset
`V : (Spec R).Opens`, `V.ι : V ⟶ Spec R` is the open immersion and `X_V` denotes base
change along `V.ι` (`GroupScheme.baseChange V.ι`). A point `g` of `G_V` over `V` is a
morphism `g : Over.mk (𝟙 V) ⟶ (G_V).X`, and
`(G_V).innerIso g : G_V ≅ G_V` is conjugation `x ↦ g x g⁻¹` on every test scheme
(`GroupScheme.comp_innerIso_hom`). So the image of `i_V ≫ (G_V.innerIso g).hom` is the
conjugate subgroup `g B_V g⁻¹`.

1. **Conjugating a Borel subgroup to contain `T`.** For every group scheme `B` over
   `Spec R` and every `i : B ⟶ G` with `IsRelativeBorelSubgroup i`
   ([`RelativeLevi.Borel`](Borel.md)), and every point `s` of `Spec R`, there are an open
   `V` with `s ∈ V` and a point `g` of `G_V` over `V` such that
   `SubgroupFunctor.range t_V ≤ SubgroupFunctor.range (i_V ≫ (G_V.innerIso g).hom)`: on
   every test scheme over `V`, every point of `T_V` lies in `g B_V g⁻¹`.
2. **Borel subgroups containing `T` are `N_G(T)`-conjugate.** For all group schemes `B`,
   `B'` over `Spec R` and homomorphisms `i : B ⟶ G`, `i' : B' ⟶ G` with
   `IsRelativeBorelSubgroup i`, `IsRelativeBorelSubgroup i'`,
   `SubgroupFunctor.range t ≤ SubgroupFunctor.range i` and
   `SubgroupFunctor.range t ≤ SubgroupFunctor.range i'`, and every point `s`, there are an
   open `V` with `s ∈ V` and a point `n` of `G_V` over `V` such that
   - `n` lies in `(SubgroupFunctor.range t_V).normalizer` at `Over.mk (𝟙 V)`: after every
     refinement `a : V' ⟶ V`, conjugation by `a ≫ n` and by its inverse maps points of
     `T_V` over `V'` to points of `T_V`. This is the functor of points of the normalizer
     `N_G(T)` restricted to `V`; the Library's `torusNormalizer` is by definition the
     normalizer of `SubgroupFunctor.range` of a torus;
   - `SubgroupFunctor.range (i_V ≫ (G_V.innerIso n).hom) = SubgroupFunctor.range i'_V`,
     that is, `n B_V n⁻¹ = B'_V` as subgroups of `G_V`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the one-based PDF pages, which agree with the printed page numbers.

- Corollary 5.2.13, p.158: "Let (G, T, M) be a split reductive group over a non-empty
  scheme S, and let B be a Borel subgroup of G. 1. Every point s ∈ S admits an open
  neighborhood U such that some G(U)-conjugate of B_U contains T_U. 2. Any two Borel
  subgroups of G that contain T are N_G(T)-conjugate Zariski-locally over S."
- Proof of Corollary 5.2.13, pp.158–159. For (1), `B` is étale-locally conjugate to the
  Borel subgroup `B′ = P_G(λ) ⊃ T` attached to a positive system of roots, so the
  transporter `Transp_G(B, B′)` is an étale torsor for `N_G(B′) = B′`; `B′` has a
  composition series with successive quotients `𝔾_a` or `𝔾_m`, whose étale torsors are
  Zariski-locally trivial. For (2), Corollary 5.2.7 reduces to the fibre at `s`; the map
  `N_G(T) → W_G(T)` is surjective for the Zariski topology (Corollary 5.1.11), `W_G(T)`
  is constant (Proposition 5.1.6), and the Weyl group of the geometric fibre acts
  transitively on the Borel subgroups containing `T_s`.
- Definition 5.1.1, p.136: "Let G be a reductive group over a non-empty scheme S. It is
  split if there exists a maximal torus T equipped with an isomorphism T ≃ D_S(M) for a
  finite free Z-module M such that: 1. the nontrivial weights a : T → G_m that occur on 𝔤
  arise from elements of M …, 2. each root space 𝔤_a is free of rank 1 over O_S, 3. each
  coroot a∨ : G_m → T arises from an element of the dual lattice M∨ …"
- Definition 5.2.10, p.157 (Borel subgroups over a base), transcribed by the published
  `IsRelativeBorelSubgroup`.

## Derivation from the source

The proposition is Corollary 5.2.13 over an affine base, with its terms translated as
follows.

- **"(G, T, M) split".** `T ≃ D_S(M)` with `M = ℤ^I` is the split torus
  `splitTorus (Spec R) I` with its coordinate lattices. Hypotheses 1–4 transcribe
  Definition 5.1.1 as in [`Reductive.EtaleLocalSplitStatement`](../Reductive/EtaleLocalSplitStatement.md)
  (Lemma 5.1.3): a closed subgroup that is a maximal torus on residue fibres, with roots
  and coroots given by the constant root datum `P` on every fibre (conditions 1 and 3),
  and root spaces free of rank one over `R` (condition 2). The torus `T` is the image of
  `t`, so "contains `T`" is `SubgroupFunctor.range t ≤ …`.
- **Affine base.** The free root-space condition uses
  `splitTorus.exponentWeightSpace`, which the Library defines only over an affine base
  `Spec R`, as a submodule of the Lie algebra of `G` over `R`. The statement for a general
  base `S` follows from this one, because both conclusions are local around a point `s`:
  restricting a split triple over `S` to an affine open neighbourhood `W = Spec R` of `s`
  gives a split triple over `W`, and an open neighbourhood of `s` in `W` is one in `S`.
  Non-emptiness of `S` is not assumed: over the empty scheme both conclusions hold
  trivially, since there is no point `s`.
- **Borel subgroups.** `IsRelativeBorelSubgroup` is the Library's transcription of
  Definition 5.2.10. Borel subgroups are given as abstract group schemes with
  monomorphisms into `G`, so conjugates and equalities of subgroups are compared through
  `SubgroupFunctor.range`, as in the other statements of this directory.
- **"G(U)-conjugate".** A point of `G(U)` is a section of `G_U` over `U`, and its
  conjugate of `B_U` is the image of `B_U` under the inner automorphism `innerIso`.
- **"N_G(T)-conjugate Zariski-locally".** For every point `s` there are an open
  neighbourhood `V` and a point `n ∈ N_G(T)(V)` conjugating `B_V` to `B'_V`. The
  normalizer `N_G(T)` represents the functor of points that normalize `T` on every test
  scheme, which is `SubgroupFunctor.normalizer` applied to the image of `T_V`.

## Scope

All objects are in universe `u`. The base is an arbitrary affine scheme `Spec R`. No
cocharacter, positive system or composition series is given; these appear only in the
source's proof. The proposition does not state the intermediate results of the proof,
such as Zariski-local triviality of étale `B′`-torsors.

## Relation to the Library

- [`Reductive.EtaleLocalSplitStatement`](../Reductive/EtaleLocalSplitStatement.md) states
  Lemma 5.1.3 with the same encoding of split reductive groups.
- [`RelativeBorelEtaleLocalConjugacyStatement`](BorelConjugacyStatement.md) states
  Theorem 5.2.11(2), étale-local conjugacy of Borel subgroups without a splitting.
- [`RelativeParabolicLieContainmentStatement`](ParabolicLieContainmentStatement.md)
  states Corollary 5.2.7(2), which the source's proof of part (2) uses.
- `torusNormalizer` in [`Rational.TorusNormalizer`](../Rational/TorusNormalizer.md) is
  defined as the normalizer of the image of a torus, the subgroup functor used in part (2).

This module proves none of these relations.

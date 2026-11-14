# Statement: Chevalley groups over the integers are split and classified by one fibre

Worker 75.

`Langlands.GroupScheme.ChevalleyGroupClassificationStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It records the paragraph before Conrad's
Proposition 6.4.1 (every Chevalley group is split) and the last assertion of that
proposition (two Chevalley groups are isomorphic over `ℤ` if and only if they are
isomorphic over `ℂ`), the latter generalized from `ℂ` to an arbitrary field. It imports:

- [`Reductive.FibrewiseRootDatum`](FibrewiseRootDatum.md), for `IsFibrewiseRootDatumOf`,
  and transitively `splitTorus.exponentWeightSpace`
  ([`Torus.RelativeAdjointWeights`](../Torus/RelativeAdjointWeights.md)) and `splitTorus`
  ([`Torus.Split`](../Torus/Split.md));
- [`Reductive.Basic`](Basic.md), for `IsReductive` and `IsClosedSubgroup`;
- [`Torus.FieldPointMaximality`](../Torus/FieldPointMaximality.md), for
  `IsFibrewiseMaximalTorus`;
- [`Torus.Relative`](../Torus/Relative.md), for `RelativeTorus.IsTorus`;
- [`Torus.LatticeGalois`](../Torus/LatticeGalois.md), for `algebraBaseMap`.

`GroupScheme S` is `Grp (Over S)`, and `CommGroupScheme S` its commutative version. An
isomorphism `G ≅ G'` in `GroupScheme S` is an isomorphism of group schemes over `S`.
Throughout, `ℤ` denotes `ULift.{u} ℤ`, the integers placed in the universe `u` of the
group schemes and test fields; `Spec ℤ` is `Spec (CommRingCat.of (ULift.{u} ℤ))`.

## Predicates and constructions used

- `IsReductive G`: the structure morphism of `G` is smooth and affine, and every geometric
  fibre of `G` is a connected reductive group over an algebraically closed field (Conrad,
  Definition 3.1.1).
- `RelativeTorus.IsTorus T`: there is an étale cover of the base on each member of which
  the base change of `T` is a finite split torus `𝔾_m^I` (the rank may vary between
  members). Conrad defines tori as fppf-locally split (Appendix B); by his
  Proposition B.3.4 they are étale-locally split, so the notions agree.
- `IsClosedSubgroup t`: the underlying morphism of schemes of the homomorphism `t` is a
  closed immersion.
- `IsFibrewiseMaximalTorus t`, for `t : T ⟶ G` with `T` commutative: for every point `s`
  of the base, the base change of `t` to the residue field `κ(s)` is a maximal torus
  (`IsMaximalTorus`): its source is a torus, it is a closed subgroup, and it does not
  factor through a strictly larger closed torus of `G_κ(s)`. By Grothendieck's theorem
  (Conrad, Remark A.1.2) this is maximality on the geometric fibres, Conrad's
  Definition 3.2.1.
- `splitTorus S I`: the split torus `𝔾_m^I` over `S`, for a finite type `I`.
- `IsFibrewiseRootDatumOf I G i P`, for `i : 𝔾_m^I ⟶ G` and a root datum `P` on the
  coordinate lattices `I → ℤ`: `J` is finite, `P` is reduced, and for every field `k` with
  a `ℤ`-algebra structure, `P`, transported to the character and cocharacter lattices of
  `𝔾_m^I` over `k`, is the root datum of `G_k` with respect to the torus `i_k`
  (`IsRootDatumOf`: actual pairing, roots as the nonzero weights of the adjoint action,
  coroots and reflections realized by normalizing points). Every field is a `ℤ`-algebra in
  exactly one way, so this covers all fibres of `G` over `Spec ℤ` and all their field
  extensions.
- `splitTorus.exponentWeightSpace I G i m`: the `ℤ`-submodule of the Lie algebra of `G` on
  which every point `t` of `𝔾_m^I`, over every `ℤ`-algebra, acts through the adjoint action
  by `∏ tⱼ^{mⱼ}`.
- `algebraBaseMap (ULift ℤ) k`: the morphism `Spec k ⟶ Spec ℤ` of the algebra structure, and
  `(baseChange b).obj G` the base change `G_k` of `G` along it.

## Statement and quantifiers

The proposition first introduces a local predicate `IsChevalley G` on
`G : GroupScheme (Spec ℤ)`: `IsReductive G`, and there are `T : CommGroupScheme (Spec ℤ)` and
`t : T.toGrp ⟶ G` with `RelativeTorus.IsTorus T.toGrp`, `IsClosedSubgroup t` and
`IsFibrewiseMaximalTorus t`. It then asserts the conjunction of two clauses.

1. **(Splitness.)** For every `G : GroupScheme (Spec ℤ)` with `hG : IsReductive G`, every
   `T : CommGroupScheme (Spec ℤ)` and every `t : T.toGrp ⟶ G` with
   `RelativeTorus.IsTorus T.toGrp`, `IsClosedSubgroup t` and `IsFibrewiseMaximalTorus t`,
   there are a type `I : Type u` with `Fintype I`, an isomorphism
   `e : splitTorus (Spec ℤ) I ≅ T.toGrp` of group schemes, a type `J : Type u` and
   `P : RootDatum J (I → ℤ) (I → ℤ)` such that
   - `IsFibrewiseRootDatumOf I G (e.hom ≫ t) P`, and
   - for every `α : J`, there is a `ℤ`-linear isomorphism from
     `splitTorus.exponentWeightSpace I G (e.hom ≫ t) (P.root α)` onto `ℤ`.
2. **(Classification by one fibre.)** For all `G G' : GroupScheme (Spec ℤ)` with
   `IsChevalley G` and `IsChevalley G'`, every field `k : Type u` and every algebra
   structure `[Algebra (ULift ℤ) k]`,
   `Nonempty (G ≅ G') ↔ Nonempty (G_k ≅ G'_k)`, where `G_k` and `G'_k` are the base
   changes along `algebraBaseMap (ULift ℤ) k`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the printed page numbers, which agree with the one-based PDF pages.

- p.230, before Proposition 6.4.1: "we define a Chevalley group to be a reductive group
  scheme G over Z that admits a maximal torus T over Z. By Corollary B.3.6, all tori over
  Z are split (as Spec Z is normal and connected with no nontrivial connected finite étale
  cover). Thus, since any line bundle over Spec Z is trivial, all Chevalley groups are
  necessarily split."
- Proposition 6.4.1, p.230: "A Chevalley group is determined up to isomorphism by its
  associated reduced root datum, and every such root datum arises in this way. Two
  Chevalley groups are isomorphic over Z if and only if they are isomorphic over C."
  Its proof: "By the Isomorphism Theorem, the equivalence between Z-isomorphism and
  C-isomorphism is immediate (as root data do not “know” the base scheme)."
- Definition 5.1.1, p.136: a reductive `G` over `S` "is split if there exists a maximal
  torus T equipped with an isomorphism T ≃ D_S(M) for a finite free Z-module M such that"
  the nontrivial weights on `g` arise from elements of `M`, "each root space g_a is free of
  rank 1 over O_S", and each coroot arises from an element of `M^∨`; "conditions (1) and
  (3) are automatic when S is connected". Over `Spec ℤ`, condition (2) is the content of
  "any line bundle over Spec Z is trivial".
- Definition 3.2.1, p.91: "A maximal torus in a smooth S-affine group scheme G → S is a
  torus T ⊂ G such that for each geometric point s of S the fiber T_s is not contained in
  any strictly larger torus in G_s."
- Corollary B.3.6, p.293: "all Z-tori are split because π1(Spec Z) = 1 (Minkowski)."

## Derivation from the source

- **Chevalley groups.** `IsChevalley` is Conrad's definition: a reductive group over
  `Spec ℤ` with a maximal torus over `Spec ℤ`, that is, a closed subgroup which is a torus
  and is maximal on every geometric fibre (Definition 3.2.1, p.91, here on residue fibres;
  see `IsFibrewiseMaximalTorus` above).
- **Clause 1.** "All Chevalley groups are necessarily split" is encoded with the split
  hypotheses used throughout the Library for Definition 5.1.1 over an affine base (as in
  [`AffineSplitIsomorphismTheoremStatement`](AffineSplitIsomorphismTheoremStatement.md)):
  a coordinate isomorphism of the torus with `𝔾_m^I`, one root datum `P` on `ℤ^I` realized
  on every field fibre, and root spaces free of rank one. The clause is slightly more
  precise than the source sentence: it asserts the splitting for the given maximal torus
  `T`, which is what the source's argument proves (the torus `T` is split by
  Corollary B.3.6, and its root spaces are line bundles on `Spec ℤ`, hence trivial). One
  root datum on all fibres is available because the roots and coroots are constant over the
  connected base `Spec ℤ` (the remark after Definition 5.1.1).
- **Clause 2.** The source compares `ℤ`-isomorphism with `ℂ`-isomorphism. The clause
  replaces `ℂ` by an arbitrary field `k` (in universe `u`, so `ULift ℂ` is an instance).
  This is a derived generalization, proved by the source's argument: an isomorphism
  `G_k ≅ G'_k` gives, after passing to an algebraic closure of `k` and conjugating maximal
  tori, an isomorphism between the root data of `G` and `G'`, which are the root data of
  their geometric fibres by clause 1; the Isomorphism Theorem over `ℤ` then gives
  `G ≅ G'`. The direction from `G ≅ G'` to `G_k ≅ G'_k` is base change. The clause is
  stated for Chevalley groups only; for reductive `ℤ`-groups without a maximal `ℤ`-torus,
  isomorphism over a field does not imply isomorphism over `ℤ`.

## Scope

All objects are in universe `u`. The groups are arbitrary reductive group schemes over
`Spec ℤ` (not necessarily semisimple, adjoint or simply connected), and the root-index
type `J` may be empty. The field `k` of clause 2 has any characteristic and need not be
algebraically closed.

## Not stated

The proposition does not state the other assertions of Proposition 6.4.1: that a Chevalley
group is determined by its root datum (for groups given with their split structures this
is the case `R = ℤ` of
[`AffineSplitIsomorphismTheoremStatement`](AffineSplitIsomorphismTheoremStatement.md)),
and that every reduced root datum arises (recorded by
[`ChevalleyIntegralExistenceStatement`](ChevalleyIntegralExistenceStatement.md)). It does
not state Corollary B.3.6 for general normal bases, the triviality of `Pic(Spec ℤ)`, or
that the split structure of clause 1 is unique.

## Relation to the Library

- [`AffineSplitIsomorphismTheoremStatement`](AffineSplitIsomorphismTheoremStatement.md)
  (Conrad Theorem 6.1.17 over an affine base) uses the same split hypotheses; with clause 1
  its case `R = ℤ` says that Chevalley groups with isomorphic root data are isomorphic.
- [`ChevalleyIntegralExistenceStatement`](ChevalleyIntegralExistenceStatement.md) records
  the existence of a reductive `ℤ`-group with a split maximal torus realizing any given
  reduced root datum on every field fibre.
- [`SplitIsomorphismTheoremStatement`](SplitIsomorphismTheoremStatement.md) is the
  Isomorphism Theorem over a field.

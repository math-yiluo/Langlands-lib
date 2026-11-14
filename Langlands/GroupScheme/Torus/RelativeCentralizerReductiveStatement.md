# Statement: centralizers of tori in reductive group schemes are reductive

Worker 75.

`Langlands.GroupScheme.RelativeTorusCentralizerReductiveStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Rational.TorusCentralizer`](../Rational/TorusCentralizer.md), which provides the
  centralizer subgroup functor `torusCentralizer`;
- [`Torus.Relative`](Relative.md), which provides `RelativeTorus.IsTorus`;
- [`Reductive.Basic`](../Reductive/Basic.md), which provides `IsReductive` and
  `IsClosedSubgroup`.

Through these imports it also uses `SubgroupFunctor.IsRepresentedBy` from
[`SubgroupFunctor`](../SubgroupFunctor.md), and `GroupScheme` and `CommGroupScheme`
from `Langlands.AbelianScheme.GroupScheme`. `GroupScheme S` is `Grp (Over S)`, and
`T.toGrp` is the underlying group scheme of a commutative group scheme `T`.

It states the relative form of the classical fact that torus centralizers in connected
reductive groups are connected reductive: for a reductive group scheme `G` over any
scheme `S` and an `S`-torus `T` in `G`, the centralizer `Z_G(T)` is a closed subgroup
scheme that is reductive over `S`.

## Statement and quantifiers

The proposition quantifies over:

- a scheme `S : Scheme.{u}`;
- a group scheme `G : GroupScheme S` with a proof of `IsReductive G`. `IsReductive G`
  says that `G → S` is smooth and affine and that every geometric fibre is connected
  reductive (Conrad's Definition 3.1.1; see [`Reductive.Basic`](../Reductive/Basic.md));
- a commutative group scheme `T : CommGroupScheme S` and a homomorphism
  `t : T.toGrp ⟶ G`, with proofs of `RelativeTorus.IsTorus T.toGrp` and
  `IsClosedSubgroup t`. `RelativeTorus.IsTorus` says that `T` becomes a split torus
  (`IsSplitTorus`) on each member of some jointly surjective étale cover of `S`, the rank
  being allowed to vary between members. `IsClosedSubgroup t` says that the underlying
  morphism of schemes of `t` is a closed immersion. This is Conrad's `S`-torus `T` in `G`.

`torusCentralizer t` is the subgroup functor of `G` whose points over an `S`-scheme `U`
are the `g ∈ G(U)` such that, for every `S`-scheme `V`, every morphism `a : V ⟶ U` and
every `x ∈ T(V)`, the points `a ≫ g` and `x ≫ t` of `G(V)` commute. This is Conrad's
functorial centralizer `Z_G(T)` (Definition 2.2.1): `g` centralizes `T` after every base
change. For a homomorphism `z : Z ⟶ G`, `(torusCentralizer t).IsRepresentedBy z` means
that the underlying morphism of `z` is a monomorphism and that the image subgroup functor
`SubgroupFunctor.range z` equals `torusCentralizer t`.

## Conclusion

The conclusion is the conjunction of two assertions.

1. There are a group scheme `Z : GroupScheme S` and a homomorphism `z : Z ⟶ G` with
   `IsClosedSubgroup z` and `(torusCentralizer t).IsRepresentedBy z`. That is, the
   centralizer is represented by a closed subgroup scheme of `G`.
2. For every group scheme `Z : GroupScheme S` and every homomorphism `z : Z ⟶ G` with
   `(torusCentralizer t).IsRepresentedBy z`, the group scheme `Z` is reductive:
   `IsReductive Z`. In particular `Z → S` is smooth and affine.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the printed page numbers.

- p.83, the paragraph before Remark 3.1.5: "In the classical theory of connected
  reductive groups, it is a fundamental fact that torus centralizers are again connected
  reductive [Bo91, 13.17, Cor. 2]. In the relative case this remains valid: if G is a
  reductive S-group scheme and T is an S-torus in G then the closed subgroup Z_G(T) is
  S-smooth (see Lemma 2.2.4) and its geometric fibers are connected reductive by the
  classical theory, so Z_G(T) is reductive over S."
- Lemma 2.2.4, pp.64–65: "Let G → S be a finitely presented S-affine S-group, and Y a
  finitely presented closed subscheme of G. Assume that Y is a subgroup of multiplicative
  type or […]. Then Z_G(Y) exists as a finitely presented closed subgroup; it is smooth
  when G is smooth and Y is a subgroup of multiplicative type […]."
- Definition 2.2.1, p.64: "The functorial centralizer Z_G(Y) on S-schemes assigns to any
  S-scheme S′ the set of g ∈ G(S′) such that g centralizes Y_{S′} inside G_{S′}. A closed
  subgroup of G representing Z_G(Y), if one exists, is denoted Z_G(Y) […]."
- Definition 3.1.1, p.81: "An S-torus is an S-group T → S of multiplicative type with
  smooth connected fibers. A reductive S-group is a smooth S-affine group scheme G → S
  such that the geometric fibers G_s̄ are connected reductive groups." The following
  discussion on p.81: "By Proposition B.3.4, any S-torus becomes a power of G_m
  étale-locally on S."

## Derivation from the source

- **Tori.** By Definition 3.1.1 and the sentence after it, an `S`-torus is étale-locally
  on `S` a power of `G_m`. `RelativeTorus.IsTorus` encodes this directly, as an étale
  form of split tori; it is the Library's predicate for relative tori. The proposition
  does not state its comparison with Conrad's multiplicative-type definition.
- **"T in G".** Conrad's torus in `G` is a subgroup, and a monomorphism from a group of
  multiplicative type into a separated group scheme is a closed immersion (Conrad p.83,
  after Proposition 3.1.6, citing Lemma B.1.3). The hypothesis `IsClosedSubgroup t`
  records this.
- **Existence.** "The closed subgroup `Z_G(T)`" uses Lemma 2.2.4 for the multiplicative
  type subgroup `Y = T` of the finitely presented `S`-affine group `G`. Assertion 1 is
  the existence part: a closed subgroup representing the functorial centralizer.
- **Reductivity.** Conrad's conclusion "`Z_G(T)` is reductive over `S`" is assertion 2.
  A subgroup functor determines a representing monomorphism up to unique isomorphism over
  `G`, so assertion 2 is stated for every representative instead of a chosen one. It
  also covers representatives that are not assumed closed; by assertion 1 a closed one
  exists. The proposition does not state the uniqueness of representatives.

## Scope

All objects are in universe `u`. The proposition does not state:

- the field-level theorem that torus centralizers in connected reductive groups are
  connected reductive (Borel 13.17, Cor. 2), which Conrad's argument applies to geometric
  fibres;
- the description `Lie(Z_G(T)) = Lie(G)^T` or the finite presentation of `Z_G(T)` from
  Lemma 2.2.4;
- Remark 3.1.5, for centralizers of multiplicative type subgroups that need not be tori,
  whose fibres can be disconnected; the Library has no relative multiplicative-type
  predicate.

## Relation to the Library

- `SplitTorusCentralizerReductiveStatement` in
  [`Rational.SplitTorusCentralizerReduction`](../Rational/SplitTorusCentralizerReduction.md),
  proved in [`Rational.SplitTorusCentralizerReductiveProof`](../Rational/SplitTorusCentralizerReductiveProof.md),
  is the field case for a split torus: over a field, every representative of the
  centralizer of a split-torus homomorphism into a connected reductive group is connected
  reductive.
- `splitTorusCentralizer_hasSmoothClosedRepresentative_overRing` in
  [`Torus.RelativeCentralizerSmooth`](RelativeCentralizerSmooth.md) proves that, over an
  affine base `Spec R`, the centralizer of a split-torus homomorphism into a smooth affine
  group has a smooth closed representative. This is the existence part of assertion 1
  for split tori over affine bases.
- `TorusCentralizerSmoothStatement` in [`Torus.CentralizerSmoothStatement`](CentralizerSmoothStatement.md)
  states smoothness of torus centralizers over a field.

This module proves none of these relations.

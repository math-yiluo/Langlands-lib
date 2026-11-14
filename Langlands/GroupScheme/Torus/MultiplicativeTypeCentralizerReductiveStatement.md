# Statement: centralizers of multiplicative-type groups in connected reductive groups

Worker 75.

`Langlands.GroupScheme.MultiplicativeTypeCentralizerReductiveStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Rational.TorusCentralizer`](../Rational/TorusCentralizer.md), which provides the
  centralizer subgroup functor `torusCentralizer`;
- [`Torus.MultiplicativeType`](MultiplicativeType.md), which provides
  `IsMultiplicativeType`;
- [`IdentityComponent`](../IdentityComponent.md), which provides `identityComponent`.

Through these imports it also uses `IsConnectedReductive` and `IsClosedSubgroup` from
[`Reductive.Basic`](../Reductive/Basic.md), `SubgroupFunctor.IsRepresentedBy` from
[`SubgroupFunctor`](../SubgroupFunctor.md), and `GroupScheme` and `CommGroupScheme` from
`Langlands.AbelianScheme.GroupScheme`. `GroupScheme S` is `Grp (Over S)`, and `H.toGrp`
is the underlying group scheme of a commutative group scheme `H`.

It states the field case of Conrad's Remark 3.1.5, which rests on
Conrad–Gabber–Prasad, Propositions A.8.10(2) and A.8.12: for a connected reductive group
`G` over a field and a group `H` of multiplicative type mapping to `G`, the centralizer
`Z_G(H)` is smooth and its identity component is connected reductive.

## Statement and quantifiers

The proposition quantifies over:

- a field `k : Type u`;
- a group scheme `G` over `Spec k` with a proof `hG : IsConnectedReductive G`. This says
  that `G` is smooth, affine and connected over `k`, and that the unipotent radical of
  its base change to an algebraic closure of `k` is trivial;
- a commutative group scheme `H` over `Spec k` with `IsMultiplicativeType H.toGrp`. This
  says that for some field extension `K` of `k` and some finitely generated abelian group
  `Λ`, the base change of `H` to `K` is isomorphic to the diagonalizable group `D(Λ)`
  over `K` (`Diagonalizable.groupScheme`). In particular `H` is of finite type;
- an arbitrary homomorphism `i : H.toGrp ⟶ G`. It is not required to be a closed
  immersion or a monomorphism;
- a group scheme `C` over `Spec k` and a homomorphism `j : C ⟶ G` with
  `(torusCentralizer i).IsRepresentedBy j` and `hclosed : IsClosedSubgroup j`.

`torusCentralizer i` is the subgroup functor of `G` whose points over a `k`-scheme `U` are
the `g ∈ G(U)` such that, for every `k`-scheme `V`, every morphism `a : V ⟶ U` and every
`x ∈ H(V)`, the points `a ≫ g` and `x ≫ i` of `G(V)` commute. Despite its name it is
defined for any homomorphism from a commutative group scheme. It is the functorial
centralizer `Z_G(H)` (Conrad, Definition 2.2.1). It is also the scheme-theoretic fixed
locus `G^H` of the action of `H` on `G` by conjugation through `i`: the published
`AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer` in
[`AutomorphicAction`](../AutomorphicAction.md) identifies the two. The condition
`(torusCentralizer i).IsRepresentedBy j` means that the underlying morphism of `j` is a
monomorphism and that the image subgroup functor `SubgroupFunctor.range j` equals
`torusCentralizer i`. `IsClosedSubgroup j` says that the underlying morphism of schemes
of `j` is a closed immersion.

## Conclusion

The conclusion is `∃ hC : Smooth C.X.hom, IsConnectedReductive (identityComponent C)`.

1. `C` is smooth over `k`.
2. With that smoothness, the identity component `identityComponent C` is connected
   reductive.

The published `identityComponent` needs `Smooth C.X.hom` and `IsAffineHom C.X.hom` as
instances. The first is the witness `hC`. The second is derived inside the statement and
is not a hypothesis: `j` is a closed immersion, hence affine, and `G → Spec k` is affine
by `hG.isAffineHom`; the composite is the structure morphism of `C` by `Over.w`. The
statement uses the same construction as `KernelCentralizerComponentReductiveStatement`.

The proposition does not assume that a closed representative exists. Existence is the
published theorem `fieldCentralizerRepresentability`. It proves
`FieldCentralizerRepresentabilityStatement` (see
[`FixedRepresentabilityStatement`](../FixedRepresentabilityStatement.md)): over a field,
`torusCentralizer j` has a closed representative for every homomorphism `j` from an
affine commutative group scheme. A multiplicative-type group is affine.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the printed page numbers.

- Remark 3.1.5, p.83: "Let H be a multiplicative type subgroup of a reductive S-group G.
  Even over an algebraically closed field, H need not lie in a maximal torus of G.
  Nonetheless, Z_G(H) is smooth (by Lemma 2.2.4) and the geometric fibers Z_G(H)_s have
  reductive identity component (by [CGP, A.8.12], which applies to a wider class of
  fibers H_s […]). The fibers of Z_G(H) can be disconnected."
- Definition 2.2.1, p.64: the functorial centralizer `Z_G(Y)`.

Brian Conrad, Ofer Gabber and Gopal Prasad, *Pseudo-reductive groups*, second edition,
Cambridge University Press, 2015. It is registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, file
`Conrad-Gabber-Prasad--Pseudo-reductive groups (book, 2nd edition)--2015.pdf` (SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`).

- Proposition A.8.12, printed p.552 (PDF p.578): "Let G be a connected reductive group
  over a field k, and H an affine k-group scheme of finite type equipped with a left
  action on G. Assume that H_k̄ is linearly reductive. Then the identity component of
  the scheme-theoretic fixed locus G^H is a connected reductive k-group." Its proof
  begins: "Proposition A.8.10(1),(2) ensures that G^H is a smooth closed k-subgroup of
  G."
- Proposition A.8.10(2), printed p.548 (PDF p.574): for `k` noetherian, `Y` and `H`
  locally of finite type and the geometric fibres of `H` linearly reductive, "if Y is
  smooth then Y^H is smooth."
- Printed p.547 (PDF p.573), before Proposition A.8.10: an affine group of finite type
  over an algebraically closed field is linearly reductive "if the identity component
  H⁰ is of multiplicative type and the component group H/H⁰ has order not divisible by
  char(F)".

## Derivation from the source

- **Field case.** Conrad's remark is for a reductive group over a base `S`. Over
  `S = Spec k`, a reductive `S`-group is a connected reductive `k`-group (Conrad,
  Definition 3.1.1), which is `IsConnectedReductive`. "`Z_G(H)_s` has reductive identity
  component" for the single geometric fibre then says that the identity component of
  `Z_G(H)` is connected reductive. The statement uses the published `identityComponent`
  and `IsConnectedReductive`, which refer to the algebraic closure of `k` internally.
- **Linear reductivity.** `H` is affine of finite type. Over an algebraically closed
  field it becomes a diagonalizable group `D(Λ) ≅ D(Λ_free) × D(Λ_tors)` with `Λ` finitely
  generated. Its identity component is of multiplicative type and its component group
  has order prime to the characteristic, so `H` is geometrically linearly reductive by
  the CGP criterion quoted above. Hence A.8.10(2) and A.8.12 apply to the action of `H`
  on `G` by conjugation through `i`, whose fixed locus is `torusCentralizer i`. These
  facts, including the passage from the extension `K` in `IsMultiplicativeType` to an
  algebraic closure of `k`, are proof obligations; this definition does not prove them.
- **Arbitrary homomorphisms.** A.8.12 allows any action of `H` on `G`, so `i` need not be
  a closed immersion. Conrad's "multiplicative type subgroup" is the case where `i` is a
  closed immersion.
- **Representatives.** A subgroup functor determines a representing monomorphism up to
  unique isomorphism over `G`, so the conclusion is stated for every closed
  representative. The proposition does not state this uniqueness.

## Scope

All objects are in universe `u`. The proposition does not state:

- the relative version of Remark 3.1.5 over a general base `S`; the Library has no
  relative multiplicative-type predicate;
- the general form of A.8.12 for an arbitrary geometrically linearly reductive group `H`
  with an arbitrary action on `G`;
- Conrad's further claims that `H` need not lie in a maximal torus and that `Z_G(H)` can
  be disconnected;
- `Lie(Z_G(H)) = Lie(G)^H` (A.8.10(1)).

## Relation to the Library

- `KernelCentralizerComponentReductiveStatement` in
  [`Rational.KernelCentralizerComponentReductiveStatement`](../Rational/KernelCentralizerComponentReductiveStatement.md)
  is the special case where `H` is the full kernel of a nonzero character of a split torus
  mapping to `G`. That statement assumes smoothness of `C`; the present one concludes it.
- `TorusCentralizerSmoothStatement` in
  [`Torus.CentralizerSmoothStatement`](CentralizerSmoothStatement.md) states smoothness
  of `C` when `H` is a closed torus in a smooth affine group.
- `diagonalizableCentralizer_hasSmoothClosedRepresentative` in
  [`Torus.CentralizerSmooth`](CentralizerSmooth.md) proves that a closed split
  diagonalizable subgroup `D(M)` of a smooth affine group over `k` has a smooth closed
  centralizer representative.
- `SplitTorusCentralizerReductiveStatement` in
  [`Rational.SplitTorusCentralizerReduction`](../Rational/SplitTorusCentralizerReduction.md)
  is the case of a split torus, where the centralizer is connected.

This module proves none of these relations.

# Reductive identity components of relative multiplicative-type centralizers

Worker 735.

This internal support module proves part (3) of
`RelativeMultiplicativeTypeCentralizerStatement`
([`Torus.RelativeMultiplicativeTypeCentralizerStatement`](RelativeMultiplicativeTypeCentralizerStatement.md))
*conditionally*. It takes two Library statements as hypotheses:

- `IdentityComponentClopenStatement`
  ([`Reductive.IdentityComponentClopenStatement`](../Reductive/IdentityComponentClopenStatement.md)),
  which is Conrad's Proposition 3.1.3;
- `MultiplicativeTypeCentralizerReductiveStatement`
  ([`Torus.MultiplicativeTypeCentralizerReductiveStatement`](MultiplicativeTypeCentralizerReductiveStatement.md)),
  which is the case of a base field.

It also takes as hypotheses closed representability of the centralizer and smoothness of
the representative. In the target statement these are parts (1) and (2), which are proved
in a separate module. The module proves neither sibling statement and adds no axioms. Its
one definition, the predicate `HasReductiveIdentityComponent`, names the conclusion of
part (3). All schemes are in universe `u`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014, registered as
`conrad-2014-reductive-group-schemes`. Page numbers are printed page numbers.

- Remark 3.1.5, p.83: "Nonetheless, Z_G(H) is smooth (by Lemma 2.2.4) and the geometric
  fibers Z_G(H)_s have reductive identity component (by [CGP, A.8.12] …). … By
  Proposition 3.1.3, the open subgroup Z_G(H)⁰ is reductive (hence affine) over S and
  closed in Z_G(H)."
- Proposition 3.1.3, p.82: "Let G → S be a smooth separated group scheme of finite
  presentation such that G⁰_s is reductive for all s ∈ S. Then G⁰ is a reductive S-group
  that is open and closed in G, …"

The main theorem follows the last two sentences of Remark 3.1.5. The field case
supplies reductivity of the fibres, and Proposition 3.1.3 then gives reductivity and
closedness of `Z_G(H)⁰`. The comparison lemmas below are internal. They pass between
the fibre `Z⁰_s` of the relative identity component and the identity component of the
fibre `Z_s`, and between the relative and field-level multiplicative-type predicates.
Conrad does not spell out these steps.

## Notation

`GroupScheme S` is `Grp (Over S)`. For a homomorphism `f`, `f.hom.hom.left` is the
underlying morphism of schemes. `RelativeIdentityComponent.residueFiber G s` is the base
change of `G` along `S.fromSpecResidueField s : Spec κ(s) ⟶ S`. In the Lean source
`IsMultiplicativeType` without prefix is the field-level predicate of
[`Torus.MultiplicativeType`](MultiplicativeType.md), and
`RelativeMultiplicativeType.IsMultiplicativeType` is the fppf-local relative predicate
(Conrad, Definition B.1.1, p.280).

## Definition

### `HasReductiveIdentityComponent`

For a group scheme `Z` over `S`, `HasReductiveIdentityComponent Z` is the proposition:
for every group scheme `Z₀` over `S` and every homomorphism `z₀ : Z₀ ⟶ Z` with
`IsRelativeIdentityComponent Z z₀`,

- `IsReductive Z₀`;
- `z₀.hom.hom.left` is a closed immersion;
- for every `s : S`, the residue fibre `RelativeIdentityComponent.residueFiber Z₀ s` is
  connected reductive over `κ(s)`.

`IsRelativeIdentityComponent Z z₀` says that `z₀` is an open immersion and that a point
`x : T ⟶ Z` of any `S`-scheme `T` factors through `z₀` exactly when, for every `s : S`, its
residue fibre lands in the identity component of `Z_s`. So the predicate says that the relative
identity component `Z⁰` of `Z`, in any of its representatives, is reductive, closed in `Z`,
and has connected reductive fibres `Z⁰_s = (Z_s)⁰`. This is the conclusion that Conrad's
Remark 3.1.5 draws for `Z = Z_G(H)`, and it is literally the conclusion of part (3) of
`RelativeMultiplicativeTypeCentralizerStatement` for a fixed representative `Z`.

*Provenance.* Internal. The definition only names this conjunction, so that part (3) can be
stated as a property of `Z`; it introduces no new notion. Conrad does not give it a name.

## Theorems

### `isOpenImmersion_baseChange_map`

For `b : S' ⟶ S` and a homomorphism `j : P ⟶ Q` of group schemes over `S` whose
underlying morphism is an open immersion, the base-changed homomorphism
`(GroupScheme.baseChange b).map j` again has an open immersion as underlying morphism.

*Proof.* The square formed by the base-changed map, the two first projections and `j` is
a pullback square. It is obtained by pasting with the defining pullback squares of
`P_{S'}` and `Q_{S'}`, as in the proof of `IsClosedSubgroup.baseChange`. Open immersions
are stable under pullback.

### `IsConnectedReductive.of_isOpenImmersion_range_eq_identitySet`

Let `k` be a field, `C` a smooth affine group over `k`, and `j : P ⟶ C` a homomorphism
whose underlying morphism is an open immersion with image exactly the identity component
`IdentityComponent.identitySet C`. If `identityComponent C` is connected reductive, then
so is `P`.

*Proof.* The identity component of `C` is clopen. Hence `j` is a preimmersion with closed
image, and so a closed immersion. `P` is nonempty because the image contains the identity
point. `P` is preconnected because `j` is an embedding whose image is a connected
component. So `P` is connected, and `IdentityComponent.isoOfIsOpenImmersion` identifies
`P` with `identityComponent C`. Then `IsConnectedReductive.of_iso` transports connected
reductivity.

### `relativeMultiplicativeTypeCentralizer_isConnectedReductive_residueFiber`

Assume `MultiplicativeTypeCentralizerReductiveStatement`. Let `G` be reductive over `S`,
`H` a commutative group scheme with `RelativeMultiplicativeType.IsMultiplicativeType H`,
and `i : H ⟶ G` a homomorphism. Let `z : Z ⟶ G` be a closed subgroup representing
`torusCentralizer i`, and `z₀ : Z₀ ⟶ Z` a homomorphism with
`IsRelativeIdentityComponent Z z₀`. Then for every `s : S` the residue fibre `Z₀_s` is
connected reductive over `κ(s)`.

*Proof.* Base change along `b = S.fromSpecResidueField s`.

- `G_s` is connected reductive by `IsReductive.isConnectedReductive_residueFiber`.
- `H_s` is of multiplicative type over the field `κ(s)` by
  `RelativeMultiplicativeType.IsMultiplicativeType.field_baseChange`, from
  [`Torus.RelativeMultiplicativeTypeFieldComparison`](RelativeMultiplicativeTypeFieldComparison.md).
- `z_s` represents `torusCentralizer i_s`, by `torusCentralizer_baseChange` and
  `IsRepresentedBy.baseChange`. It is closed by `IsClosedSubgroup.baseChange`.

The field statement therefore makes `Z_s` smooth with `(Z_s)⁰` connected reductive.
`Z → S` is affine, because `z` is a closed immersion into the affine `G`. Hence
`Z_s → Spec κ(s)` is affine. The base change `(z₀)_s` is an open immersion by the first
lemma. Its image is `IdentityComponent.identitySet Z_s` by `range_residueFiberInclusion`
([`RelativeIdentityComponentFiberComparison`](../RelativeIdentityComponentFiberComparison.md)).
The second lemma gives the conclusion.

This step uses only the clopenness of the identity component over a field. It does not
use Proposition 3.1.3, which needs the fibres as input.

### `relativeMultiplicativeTypeCentralizer_reductive`

Assume `IdentityComponentClopenStatement` and
`MultiplicativeTypeCentralizerReductiveStatement`. Let `G` be reductive over `S`, `H`
with `RelativeMultiplicativeType.IsMultiplicativeType H`, and `i : H ⟶ G` a
homomorphism. Suppose `torusCentralizer i` is closed-representable. Let `z : Z ⟶ G` be
any representative with `Z → S` smooth, and let `z₀ : Z₀ ⟶ Z` satisfy
`IsRelativeIdentityComponent Z z₀`. Then:

- `IsReductive Z₀`;
- `z₀.hom.hom.left` is a closed immersion;
- for every `s : S`, `Z₀_s` is connected reductive over `κ(s)`.

These are the three conclusions of part (3) of the target statement. The extra
hypotheses are closed representability and `Smooth Z.X.hom`. The target statement's
parts (1) and (2) supply them when `G` is reductive.

*Proof.* Closed representability gives a closed representative `c : C ⟶ G` of
`torusCentralizer i`. The imported `SubgroupFunctor.IsRepresentedBy.isClosedSubgroup` from
[`Dynamic.RepresentedStructure`](../Dynamic/RepresentedStructure.md) transports
closedness between two representatives of the same subgroup functor: they are isomorphic
over `G`, so `z` is an isomorphism followed by the closed immersion `c`. Hence `z` is a
closed subgroup, and `Z → S` is affine, being a closed immersion into the affine `G`
followed by `G → S`. It is therefore separated and quasi-compact. The fibre clause is the previous theorem. With
smoothness of `Z`, these are the hypotheses of `IdentityComponentClopenStatement`
applied to `Z` and `z₀`. Its first two conclusions are reductivity of `Z₀` and
closedness of `z₀`. Its third conclusion, about `Z/Z⁰`, is discarded.

### `relativeMultiplicativeTypeCentralizer_hasReductiveIdentityComponent`

Under the hypotheses of `relativeMultiplicativeTypeCentralizer_reductive`, except the
choice of `z₀`, `HasReductiveIdentityComponent Z` holds: every smooth representative `Z`
of the centralizer has a reductive relative identity component.

*Proof.* Unfold the definition and apply `relativeMultiplicativeTypeCentralizer_reductive`
to each `z₀`.

## Imports

Besides the two sibling statements and the target statement's module, the module
imports:

- [`Dynamic.RepresentedStructure`](../Dynamic/RepresentedStructure.md), for
  closedness of any representative of a subgroup with a closed representative;
- [`Reductive.BaseChange`](../Reductive/BaseChange.md), for
  `IsReductive.isConnectedReductive_residueFiber`;
- [`RelativeIdentityComponentFiberComparison`](../RelativeIdentityComponentFiberComparison.md),
  for `range_residueFiberInclusion`;
- [`Torus.RelativeMultiplicativeTypeFieldComparison`](RelativeMultiplicativeTypeFieldComparison.md),
  for `RelativeMultiplicativeType.IsMultiplicativeType.field_baseChange`;
- [`Torus.MaximalBaseChangeForwardReduction`](MaximalBaseChangeForwardReduction.md), for
  `torusCentralizer_baseChange` and, through its imports, `IsRepresentedBy.baseChange`,
  `IsClosedSubgroup.baseChange` and `IsConnectedReductive.of_iso`.

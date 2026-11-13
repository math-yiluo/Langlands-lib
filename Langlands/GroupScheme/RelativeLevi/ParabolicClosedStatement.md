# Statement: parabolic subgroups of reductive group schemes are closed

Worker 75.

`Langlands.GroupScheme.RelativeParabolicClosedStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports [`RelativeLevi.Basic`](Basic.md) (for
`IsRelativeParabolicSubgroup`); `IsReductive` and `IsClosedSubgroup` come in through that
import.

## Statement and quantifiers

The proposition quantifies over:

- every scheme `S : Scheme.{u}`;
- every pair of group schemes `G P : GroupScheme S`;
- every group-scheme homomorphism `i : P ⟶ G`.

It has two hypotheses:

1. `IsReductive G` ([`Reductive.Basic`](../Reductive/Basic.md)): `G` is smooth and affine
   over `S`, and its geometric fibre at every point `s`, over the chosen algebraic closure
   of the residue field `κ(s)`, satisfies `IsPseudoReductive`. Over an algebraically closed
   field this means smooth, connected and affine with trivial unipotent radical, so the
   geometric fibres are connected reductive groups.
2. `IsRelativeParabolicSubgroup i` ([`RelativeLevi.Basic`](Basic.md)): `P` is smooth and
   affine over `S`, `i` is a monomorphism of `S`-schemes, and for every point `s` of `S`
   the residue fibre `i_s : P_s ⟶ G_s` over `κ(s)` satisfies the field predicate
   `IsParabolicSubgroup`.

The conclusion is `IsClosedSubgroup i`, which is by definition
`IsClosedImmersion i.hom.hom.left`: the underlying morphism of schemes `P ⟶ G` is a closed
immersion.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014; registered as `conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
one-based PDF pages, which agree with the printed page numbers of this file.

- Proposition 5.2.3, p.152, first assertion: "Let G → S be a reductive group scheme, and Q
  a parabolic subgroup of G. Then Q → G is a closed immersion".
- Definition 5.2.1, p.151: a parabolic subgroup of a reductive group scheme is a smooth
  `S`-affine `S`-group with a monic homomorphism to `G` that is parabolic on every fibre;
  the paragraph after it says that closedness is not required in the definition.

## Derivation from the source

The Lean proposition is the first assertion of Proposition 5.2.3, verbatim up to the
translation of its terms. Hypothesis 1 is Conrad's notion of reductive group scheme
(Definition 3.1.1, p.81). Hypothesis 2 is Definition 5.2.1, as explained in the Markdown of
[`RelativeLevi.Basic`](Basic.md): there parabolicity of a fibre over `κ(s)` is expressed by
`IsParabolicSubgroup`, which asks for a closed subgroup containing a Borel subgroup after
base change to an algebraic closure. That is the classical equivalent of properness of
`G_s/P_s`. The conclusion is the closed-immersion assertion. The remaining assertions of
Proposition 5.2.3 (étale-local existence of a maximal torus inside `Q`, and the local
dynamic description `Q = P_G(λ)` in the split case) are not part of this proposition.

## Scope

All objects are in universe `u`. The base `S` is an arbitrary scheme: it need not be
affine, Noetherian, reduced or connected, and the empty scheme is allowed. No maximal
torus, Borel subgroup, cocharacter or splitting over `S` is assumed.

## Relation to the Library

- The published `RelativeParabolicSelfNormalizerStatement`
  ([`RelativeParabolicNormalizerStatement`](../RelativeParabolicNormalizerStatement.md))
  and `RelativeParabolicQuotient.ExistenceStatement`
  ([`RelativeParabolicQuotientStatement`](../RelativeParabolicQuotientStatement.md)) assume
  a closed subgroup over an affine base. This proposition supplies closedness for
  parabolic subgroups in the sense of Definition 5.2.1.

This module proves none of these relations.

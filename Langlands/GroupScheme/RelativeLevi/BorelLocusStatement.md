# Statement: the Borel locus of a parabolic subgroup scheme is open and closed

Worker 75.

`Langlands.GroupScheme.RelativeBorelLocusClopenStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports [`RelativeLevi.Basic`](Basic.md), for
`IsRelativeParabolicSubgroup` and `RelativeLevi.residueFiberHom`, and
[`Reductive.QuasiSplit`](../Reductive/QuasiSplit.md), for `IsGeometricBorelSubgroup`.

## Statement and quantifiers

The proposition quantifies over:

- every scheme `S : Scheme.{u}`;
- every pair of group schemes `G P : GroupScheme S`;
- every group-scheme homomorphism `i : P ⟶ G`.

It has two hypotheses:

1. `IsReductive G` ([`Reductive.Basic`](../Reductive/Basic.md)): `G` is smooth and
   affine over `S`, and its geometric fibre at every point `s`, over the chosen
   algebraic closure of the residue field `κ(s)`, satisfies `IsPseudoReductive`. Over
   an algebraically closed field this means smooth, connected and affine with trivial
   unipotent radical, so the geometric fibres are connected reductive groups.
2. `IsRelativeParabolicSubgroup i` ([`RelativeLevi.Basic`](Basic.md)): `P` is smooth
   and affine over `S`, `i` is a monomorphism of `S`-schemes, and for every point `s` of
   `S` the residue fibre `i_s : P_s ⟶ G_s` over `κ(s)` satisfies the field predicate
   `IsParabolicSubgroup`.

The conclusion is that the set

    {s : S | IsGeometricBorelSubgroup (RelativeLevi.residueFiberHom i s)}

is open and closed in the underlying topological space of `S` (`IsClopen`). Here
`RelativeLevi.residueFiberHom i s` is the base change of `i` along `Spec κ(s) ⟶ S`.
`IsGeometricBorelSubgroup` says that this fibre is a Borel subgroup over `κ(s)` (the
field predicate `IsBorelSubgroup`) and stays one after base change to the algebraic
closure of `κ(s)`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the one-based PDF pages, which agree with the printed page numbers.

- Theorem 5.2.11(1), p.157: "Let G → S be a reductive group scheme. Let P ⊂ G be a
  parabolic subgroup. If P_s is a Borel subgroup of G_s then P_U is a Borel subgroup of
  G_U for some open U ⊂ S around s, and the open locus of s ∈ S such that P_s is a Borel
  subgroup is also closed."
- Proof of Theorem 5.2.11, p.158: part (1) follows from fibre dimension considerations
  for the smooth map `P → S`, since the isomorphism class of the fibral root datum is
  locally constant over `S`.
- Definition 5.2.1, p.151 (parabolic subgroups), and Definition 3.1.1, p.81 (reductive
  group schemes).

## Derivation from the source

Theorem 5.2.11(1) makes two assertions about the locus of points `s` at which `P_s` is
a Borel subgroup of `G_s`:

- it is open, which is the first sentence: around each point of the locus there is an
  open `U` over which all fibres of `P` are Borel subgroups;
- it is closed.

The proposition states exactly these two assertions as `IsClopen` of that locus. The
first sentence of the source is phrased as "`P_U` is a Borel subgroup of `G_U`". By
Definition 5.2.10 this means that `P_U` is parabolic in `G_U`, which always holds, and
that every fibre of `P_U` at a point of `U` is a Borel subgroup. The fibres of `P_U`
are the fibres of `P` at the points of `U`, so this is openness of the locus. The
proposition states openness of the locus directly. It does not mention the restriction
`P_U` or the relative Borel predicate.

Over the residue field `κ(s)`, which need not be algebraically closed, "`P_s` is a
Borel subgroup of `G_s`" means a Borel `κ(s)`-subgroup: a subgroup whose base change to
an algebraic closure is a Borel subgroup in the classical sense. The source uses Borel
`k`-subgroups in this sense in Exercise 5.5.1(iii), pp.181–182, where parabolicity of
`k`-subgroups is checked over `k̄`. The proof of part (1) quoted above also uses only
geometric fibre dimensions. The field predicate `IsBorelSubgroup` alone only asks for
maximality among `κ(s)`-subgroups, which is weaker over non-closed fields. The Lean
condition is therefore the existing `IsGeometricBorelSubgroup`. The Library's
field-level `IsQuasiSplit` uses the same condition.

## Scope

All objects are in universe `u`. The base `S` is an arbitrary scheme: it need not be
affine, Noetherian, reduced or connected, and the empty scheme is allowed. No maximal
torus, splitting or cocharacter over `S` is assumed.

## Not stated

Parts (2) and (3) of Theorem 5.2.11 are not stated: étale-local conjugacy of Borel
subgroups, and representability of the functor of Borel subgroups by a smooth proper
`S`-scheme `Bor_{G/S}` with an ample line bundle.

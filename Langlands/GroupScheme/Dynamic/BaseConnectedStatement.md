# Statement: connected fibres of dynamic subgroups without smoothness

Worker 3483.

`Langlands.GroupScheme.DynamicBaseConnectedStatement.{u} : Prop` is a
statement-only proposition definition. This module proves no theorem and
introduces no axiom. It imports the actual dynamic subgroup functors from
[`Dynamic.Basic`](Basic.md), Mathlib's finite-presentation morphism
interface and its `GeometricallyConnected` predicate.

## Quantifiers and conclusion

The statement quantifies over an arbitrary scheme `S : Scheme.{u}`, a group
scheme `G : GroupScheme S` with affine and locally finitely presented structure
morphism, a cocharacter `χ : (Gm S).toGrp ⟶ G`, a group scheme `H` over `S`,
and a homomorphism `j : H ⟶ G`. It asserts:

1. if `j` represents `Dynamic.unipotent χ`, then `H → S` is geometrically
   connected;
2. if `j` represents `Dynamic.parabolic χ` and `G → S` is geometrically
   connected, then `H → S` is geometrically connected;
3. if `j` represents `Dynamic.centralizer χ` and `G → S` is geometrically
   connected, then `H → S` is geometrically connected.

The representation hypotheses are
`SubgroupFunctor.IsRepresentedBy`: the underlying morphism of schemes over
`S` is a monomorphism, and its range is the specified subgroup functor on
every test scheme. In particular, nonreduced tests are included. The dynamic
functors concern the conjugation orbit `t ↦ χ(t) g χ(t)⁻¹`: extension to the
affine line defines `P`, extension with value `1` at `0` defines `U`, and
constancy defines `Z`. No representative is constructed or asserted to exist.

`GeometricallyConnected H.X.hom` means that for every field `K : Type u` and
every morphism `Spec K ⟶ S`, the pullback of `H → S` has connected underlying
space. This expresses geometrically connected fibres; it does not assert
connectedness of the total space when the base is disconnected.

Relative affineness means that the inverse image of each affine open in `S`
is affine. The scheme `S` need not itself be affine. No smoothness, flatness,
Noetherian, reducedness or connectedness hypothesis on `S` is imposed.
The trivial cocharacter is included.

## Original sources

Brian Conrad, *Reductive group schemes*, Panoramas et Synthèses 42–43
(2014), registered as `conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
Printed and one-based PDF page numbers agree.

Theorem 4.1.7 starts on p.112 with a finitely presented affine group over a
ring and an action of `G_m` on that group. Part (2), p.113, states that the
fibres of `U` are connected and that those of `P` and `Z` are connected if
the original group's fibres are connected. Smoothness is introduced only
in part (4). The convention following the theorem specializes the action
to conjugation by a cocharacter. The proof on p.114 explicitly distinguishes
the nonsmooth connectedness argument from the smooth open-cell argument.
The paragraph after Example 4.1.9, also p.114, states arbitrary base-change
compatibility and extends Theorem 4.1.7 to any base scheme.

Brian Conrad, Ofer Gabber and Gopal Prasad, *Pseudo-reductive groups*,
second edition (2015), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, file
`Conrad-Gabber-Prasad--Pseudo-reductive groups (book, 2nd edition)--2015.pdf`,
SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
Proposition 2.1.8(4), printed p.53, PDF p.79, is the connected-fibres
assertion cited in Conrad's proof. Its hypothesis is an affine group of
finite presentation over a ring; part (4) assumes no smoothness.

## Derivation and retained hypotheses

The Lean formulation specializes the action to conjugation, as supported
by both sources. It uses the arbitrary-base version explicitly stated by
Conrad. An affine morphism is quasi-compact and separated, hence
quasi-separated. Together with local finite presentation, these properties
give finite presentation, retaining the source's finiteness hypothesis.

The geometric formulation follows by applying the source to every base
change `Spec K ⟶ S`. The pullback of `G` is still affine and finitely
presented. Dynamic subgroup formation commutes with this base change.
If `G → S` is geometrically connected, this pullback of `G` is connected.
Part (2), or CGP part (4), therefore makes the corresponding `P` and `Z`
connected; `U` is connected without that hypothesis. Running over all `K`
and all such morphisms gives exactly Mathlib's geometric predicate.
This argument does not use a smoothness assumption or a
connectedness-versus-geometric-connectedness equivalence.

Quantification over arbitrary representatives is justified by uniqueness
of a representative over `G`. Each supplied `j` is isomorphic over `G` to
the source's closed representative; the same holds after base change.
Connectedness is invariant under the induced scheme isomorphism.

## Relation to existing targets

[`DynamicBaseSmoothConnectedStatement`](BaseSmoothConnectedStatement.md)
assumes smoothness and also concludes smoothness of the representatives.
The present proposition isolates the connectedness conclusion with the
source's weaker hypothesis on `G`. The field target
`DynamicConnectedStatement` in
[`SmoothConnectedStatement`](SmoothConnectedStatement.md) likewise assumes
smoothness. Both existing interfaces are retained.

[`DynamicBaseRepresentabilityStatement`](BaseRepresentabilityStatement.md)
asserts existence of finitely presented closed representatives with the same
hypotheses on `G`; it is a separate target. The present statement assumes
representatives and asserts their connectedness.

This module supplies neither representability nor a proof of connectedness,
and makes no assertion about abstract actions beyond conjugation.

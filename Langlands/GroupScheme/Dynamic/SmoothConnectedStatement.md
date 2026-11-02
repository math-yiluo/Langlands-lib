# Smoothness and connectedness of dynamic subgroups

This file states two propositions about the dynamic subgroup functors
`Dynamic.parabolic χ`, `Dynamic.centralizer χ` and `Dynamic.unipotent χ` of
[Dynamic.Basic](Basic.md). It proves neither of them.

Both statements quantify over every field `k : Type u`, every group scheme
`G : GroupScheme (Spec (CommRingCat.of k))` whose structure morphism `G.X.hom`
is `Smooth` and `IsAffineHom`, every cocharacter
`χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G`, every group scheme `H` over
`Spec k` and every homomorphism `j : H ⟶ G`. The hypothesis on `j` in each
clause is `F.IsRepresentedBy j` for the relevant functor `F`: `j` is a
monomorphism of the underlying schemes over `Spec k` and its range subgroup
functor is `F` (see [SubgroupFunctor](../SubgroupFunctor.md)). Nothing asserts
that such an `H` exists. The trivial cocharacter is included.

## `DynamicSmoothStatement`

For all the data above, the conjunction of three implications:

* if `j` represents `Dynamic.parabolic χ`, then `H.X.hom` is `Smooth`;
* if `j` represents `Dynamic.centralizer χ`, then `H.X.hom` is `Smooth`;
* if `j` represents `Dynamic.unipotent χ`, then `H.X.hom` is `Smooth`.

This is the smoothness assertion of Conrad–Gabber–Prasad, *Pseudo-reductive
groups*, second edition, Proposition 2.1.8(3) (printed p.53), for a smooth
affine `k`-group over a field: "if `G` is `k`-smooth, … `P_G(λ)`, `U_G(λ)`, and
`Z_G(λ)` are all smooth". CGP states it over any ring for a smooth affine group
of finite presentation; only the field case is formalized here. In CGP the
subgroups are the representing closed subschemes; here the statement is
phrased for an arbitrary representative `j`, which is the same group up to
unique isomorphism.

## `DynamicConnectedStatement`

For all the data above, the conjunction of:

* if `j` represents `Dynamic.unipotent χ`, then the underlying topological
  space of `H.X.left` is a `ConnectedSpace`;
* if the underlying space of `G.X.left` is a `ConnectedSpace`, then
  representatives of `Dynamic.parabolic χ` and of `Dynamic.centralizer χ` have
  connected underlying spaces.

This is Conrad–Gabber–Prasad, Proposition 2.1.8(4) (printed p.53), over a
field: "The fibers of `U_G(λ)` over `Spec k` are connected, and the same holds
for `P_G(λ)` and `Z_G(λ)` if `G` has connected fibers". Over a field the only
fiber is the scheme itself. CGP states part (4) for affine groups of finite
presentation over a ring, without smoothness; this statement keeps the smooth
affine hypotheses of the first statement, so it is a special case of CGP's
assertion. A connected space is in particular nonempty, which holds for group
schemes because of the identity section.

## Provenance and scope

Source ID: `conrad-gabber-prasad-2015-pseudo-reductive` (Proposition 2.1.8,
printed pp.53–54, PDF pp.79–80). The phrasing with arbitrary representatives
and the restriction to a base field are choices of this formalization. These
are proposition targets: the file contains no proof, axiom or instance
asserting them.

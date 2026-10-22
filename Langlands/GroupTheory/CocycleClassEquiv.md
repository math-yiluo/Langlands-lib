# Cochains and extension equivalences from equal second cohomology classes

This module proves the converse of the published
`Langlands.NormalizedTwoCocycle.cohomologyClass_eq_of_cochain`. From that
converse it builds a continuous equivalence between the cocycle extensions
of two normalized cocycles with the same class. All declarations are in
`Langlands.NormalizedTwoCocycle`. Here `G` is a group, `A` is an abelian
multiplicative group, `MulDistribMulAction G A` is the given action, and both
carriers inhabit one universe `Type u`. Mathlib's cohomology API, used through
`cohomologyClass`, requires this.

## The converse cochain theorem

`exists_cochain_of_cohomologyClass_eq` assumes normalized cocycles `c, d`
with `cohomologyClass c = cohomologyClass d`. Both classes lie in Mathlib's
actual `groupCohomology (coefficientRepresentation G A) 2`. The theorem gives a
function `b : G → A` with

`c(g,h) * b(g*h) = b(g) * (g • b(h)) * d(g,h)` for all `g, h`.

This is exactly the equation that `cohomologyClass_eq_of_cochain` assumes. The
proof uses Mathlib's `groupCohomology.H2π_eq_iff`, which turns class equality
into membership of the difference of the additive cocycles in
`coboundaries₂`. It then takes the additive one-cochain `x` that witnesses
this range membership and sets `b(g) = (x g).toMul`. At `(g,h)` the
multiplicative form of the witness equation is

`(g • b(h)) / b(g*h) * b(g) = c(g,h) / d(g,h)`.

Here the differential is the published `differential₁₂` convention, which
holds definitionally. Multiplying by `d(g,h) * b(g*h)` and rearranging in the
commutative group `A` gives the displayed equation. No normalization of `b`
is claimed or needed.

`cohomologyClass_eq_iff_exists_cochain` states the equivalence. Its forward
direction is the theorem above. Its reverse direction is the published
`cohomologyClass_eq_of_cochain`, reused rather than reproved.

## The chosen cochain is not unique

`classCochain hcd` chooses such a `b` from a proof `hcd` of class equality,
and `classCochain_spec` states its equation. The module claims no uniqueness
or canonicity for the chosen cochain. As an unformalized remark, the classes
do not determine the cochain. If `b` works, then so does `b * z` for every
multiplicative crossed homomorphism `z`, that is, every `z` with
`z(g*h) = z(g) * (g • z(h))`.

`MapData.ofCohomologyClassEq hcd` packages `classCochain hcd` as the published
`MapData c d (MonoidHom.id A) (MonoidHom.id G)` from
`Langlands.GroupTheory.CocycleMap`. With identity components, the action
equivariance holds by reflexivity. The compatibility equation is
`classCochain_spec`. `ofCohomologyClassEq_cochain` records that its cochain is
`classCochain hcd`.

## The continuous extension equivalence

In the topology section `G` has a topology that is assumed discrete,
`[DiscreteTopology G]`, and `A` is a topological group. Each extension has
the published topology induced from the product `A × G` by the coordinate
bijection. `continuousEquivOfCohomologyClassEq hcd : c.Extension ≃ₜ* d.Extension`
is the published `MapData.continuousEquivOfEquivs`. It is applied to the
identity continuous multiplicative equivalences of `A` and `G` and to
`MapData.ofCohomologyClassEq hcd`. The cochain is continuous because `G` is
discrete (`continuous_of_discreteTopology`). Neither the extension group nor
its topology is rebuilt.

The coordinate formulas come from the published construction and hold by
reflexivity. On an element `(a, g)`:

- `continuousEquivOfCohomologyClassEq_apply`: the equivalence is the
  underlying `MapData` homomorphism;
- `continuousEquivOfCohomologyClassEq_left`: the new left coordinate is
  `a * b(g)` with `b = classCochain hcd`;
- `continuousEquivOfCohomologyClassEq_right`: the right coordinate `g` is
  unchanged;
- `continuousEquivOfCohomologyClassEq_symm_apply`: the inverse sends `(a, g)`
  to `(a / b(g), g)`.

The equivalence fixes the coefficient subgroup and commutes with projection
to `G`, in both directions:

- `continuousEquivOfCohomologyClassEq_inl`: `Extension.inl c a` maps to
  `Extension.inl d a`. This reuses `MapData.toMonoidHom_inl`, since `b(1) = 1`
  is derived there from normalization of `c` and `d`.
- `continuousEquivOfCohomologyClassEq_symm_inl`: the inverse sends
  `Extension.inl d a` to `Extension.inl c a`.
- `projection_continuousEquivOfCohomologyClassEq` and its `_symm` variant:
  `Extension.projection` is preserved.

The equivalence depends on the chosen cochain. Equal classes give some
equivalence over both ends, and the module claims no unique or canonical
one. Unformalized here: changing `b` to `b * z` composes the equivalence
with the twist `(a, g) ↦ (a * z(g), g)`.

## Provenance

This is internal derived material. The converse is proved directly in
Mathlib's cochain complex through `H2π_eq_iff`, using the differential
convention published in `Langlands.GroupTheory.CocycleCohomology`. The
equivalence specializes `Langlands.GroupTheory.CocycleMap` to identity
components. The cochain convention is that of Artin and Tate, *Class Field
Theory* (2009), Chapter XIII section 1, printed pp.127–130 (PDF pp.136–139),
registered as `artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`. The
displayed equation is their p.129 equation (*) multiplied by `b(g*h)` in the
abelian coefficient group. On p.129 they show that a cochain satisfying (*)
gives a homomorphism of extensions over the given end maps. Their Theorem 1
on p.130 then says that extensions with the same class are equivalent over
the identity on both ends. This module proves that implication for the actual
Mathlib second cohomology classes, with the identity end maps. On p.130 they
also show that such homomorphisms form a torsor under one-cocycles. The
non-uniqueness described above is the elementary part of that remark. The
module formalizes no statement about this torsor or about the action of
`H¹` modulo inner automorphisms.

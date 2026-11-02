# Lifted subgroup actions on small-etale objects and their sections

Author: Worker 13.

This internal construction equips actual small-etale objects over a scheme
with subgroup actions lifting the given scheme action. It constructs the
corresponding category, labelled transport automorphisms, and functorial
representations on sections of transport sheaves. It prepares local
smoothness constructions; it imposes no smoothness or analytic continuity
condition.

The inputs are a scheme `Y : Scheme.{u}`, a group `G : Type w`, its action
`ρ : G →* (Aut Y)ᵐᵒᵖ`, and a subgroup `H : Subgroup G`. The opposite
automorphism convention agrees with `EtaleCohomologyAction`: the scheme
automorphism attached to `hk` is the composite attached to `h` and then `k`,
so contravariant sheaf evaluation gives a left action on sections.

`LocalAction ρ H` retains a genuine small-etale object `U → Y`, a
homomorphism `H →* (Aut U)ᵐᵒᵖ`, and equivariance of the structure map.
Its morphisms are ordinary small-etale maps whose underlying scheme maps
commute with every subgroup operator. Identities and composition use the
ordinary maps; associativity and unit laws follow from their laws.
`LocalAction.forget` is faithful and retains these actual schemes and maps.

`transport U h` is the transport endomorphism labelled by the specified
element `h : H`, with underlying scheme automorphism given by the lifted
action. Equivariance supplies its transport-square equation. The
`transport_one` and `transport_mul` equations prove the action laws while
retaining the labels, including when the base action is nonfaithful.
`transportIso` has inverse the arrow for `h⁻¹`.
`Hom.comm_transport` states the corresponding commuting square for an
equivariant ordinary map.

The whole scheme has a constructed `LocalAction.whole ρ H`, obtained by
restricting `ρ` to `H`. Its transport arrows are exactly the existing
`wholeMap` arrows. For `K ≤ H`, `restrict` restricts both the action and
equivariant maps to `K`; it leaves the small-etale object and ordinary
maps unchanged.

For any category `A`, `LocalAction.sectionAction A U` takes a transport
sheaf to its actual value on `U` with subgroup action induced by the
labelled arrows. Sheaf morphisms act by their components on `U`.
`sectionActionForgetIso` identifies forgetting the subgroup action with
the existing evaluation functor. `sectionRestriction` is the natural
equivariant restriction along a morphism of lifted objects. Its action
compatibility follows from `Hom.comm_transport` and contravariance of the
sheaf; its naturality is the original sheaf-morphism naturality equation.
`sectionDiagram` packages these restrictions as a contravariant functor
on lifted objects. `wholeSectionIso` recovers the existing global section
action restricted to `H`, while `restrictSectionIso` identifies subgroup
restriction before and after evaluation.

For a commutative ring `R : Type uR` and module carriers in `Type uM`,
`LocalAction.sectionRepresentation R U` applies the existing
`Rep.ActionToRep` to this action. It is additive, and it preserves finite
limits because its underlying module functor is actual sheaf evaluation
and representation forgetting reflects limits. The natural
`representationRestriction` has underlying linear map exactly the
original transport sheaf restriction. `wholeRepresentationIso` identifies
the whole-object representation with `sectionRepresentation ρ R` followed
by Mathlib's subgroup restriction functor.

All universes are independent: schemes use `u`, the group and its subgroup
use `w`, a general target category has object and morphism universes `uA`
and `vA`, and coefficients and module carriers use `uR` and `uM`.
There is no group-smallness hypothesis.

The provenance is internal assembly of the existing labelled transport
category and its actual evaluation functors with categorical subgroup
actions and Mathlib representation restriction. No new assertion is
attributed to Harris or Berkovich. A lifted action is genuine geometric
input data, not an assumed cohomology group or comparison theorem. Only
the whole-object lift and restriction of a supplied lift are constructed
here. Existence of local lifts for arbitrary small-etale neighborhoods,
joint continuity, a full smooth equivariant etale category, analytic
specialization, compact supports and the Harris comparison remain
separate obligations.

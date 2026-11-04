# Maximal tori in Lie-element centralizers

This derived module assembles the maximal-torus part of Milne,
*Algebraic Groups* (2017), Proposition 17.90, printed p.381 / PDF p.397.
The field has arbitrary universe and characteristic. All groups, tangent
vectors, subgroup representatives and homomorphisms are actual group
schemes and their dual-number identity kernels.

Let `j : C → G` be a smooth affine closed representative of the all-test
centralizer of a tangent vector `X` in an affine group `G`. The module
retains the following explicit inputs:

- `X` belongs to the tangent submodule of its element centralizer.
- Every Cartan subgroup of the identity component of `C` is connected and
  geometrically nilpotent.
- Every tangent lift of `X` into a closed subgroup of `G` is semisimple in
  the published representation-tested sense.
- The exact `NilpotentCentralTorusStatement` and
  `UnipotentSemisimpleStatement` hold.

The self-membership premise is the elementary tangent centralization fact
used at the start of the source argument. The Cartan structure input is
the connected nilpotence conclusion of Milne Proposition 17.44, printed
pp.364–365 / PDF pp.380–381. The lift-semisimplicity input is local to the
fixed vector `X`; the module does not prove semisimplicity reflection
under closed embeddings. There is no separate assumption that `X` is
semisimple in `G`, because the stronger displayed premise already
requires semisimplicity of every closed-subgroup lift, including the
identity lift. The ambient group need not be smooth or connected.

`Lie.exists_tangent_lift_identityComponent_elementCentralizer` lifts `X`
to the identity component by the published equality between the tangent
submodule of a smooth represented subgroup and the tangent image of its
identity component. For any prescribed maximal torus in that component,
the represented-centralizer identity places its ambient image in the
element centralizer. Monomorphic cancellation reflects this containment
to the lifted vector. The torus has an actual closed Cartan
representative, whose connected nilpotence is supplied by the explicit
input. Lift-semisimplicity is applied to the composite closed inclusion
of this Cartan into `G`. The published `Lie.cartanTangentFactor` then
gives a tangent vector in the prescribed torus. Composing the tangent
identities recovers the original `X`.

`Lie.elementCentralizerIdentityTorusFactor` chooses that actual tangent
preimage, and its companion theorem proves the reconstruction identity.
`preservesMaximalTori_identityComponent_elementCentralizer_of_cartanLifts`
applies the published all-test maximality adapter to each such preimage.
Its conclusion is exactly `PreservesMaximalTori` for the inclusion of the
centralizer's identity component into `G`, as needed by the Cartan
induction modules.

The registered 2017 errata snapshot dated 2026-11-02 makes no correction
to Propositions 17.44 or 17.90. These are conditional constructions and
deductions within the Cartan generation proof. They do not discharge the
listed structural inputs or prove `CartanGenerationStatement`.

# Local section representations on the finite rational transport site

Author: Worker 13.

This internal construction evaluates actual categorical sheaves on the existing
varying-open-subgroup rational transport site. It constructs each object's
subgroup action on its entire section object, and restriction intertwiners along
every original labelled arrow.

The base `K : Type u` is a complete ultrametric normed field, `P` is a presented
strict affinoid algebra over `K`, and `G : Type v` is a topological group with a
`RationalSpectralAction G P`. The inherited topologies on the actual open
subgroups are retained. An object `X` consists of an actual open subgroup
`X.subgroup` and an invariant unit-radius rational presentation `X.domain`.
The site is exactly `OpenSubgroupTransport.finiteTopology`: a covering sieve
contains a finite family whose labelled point images cover the target locus.
Empty families are allowed. No new site or covering condition is supplied here.

All declarations are in the namespace
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction.OpenSubgroupTransport`.

For `k : X.subgroup`, `operator X k` is the original kind of transport arrow
`X ⟶ X` with label `k⁻¹`. Subgroup closure and invariance of the actual rational
locus prove its two intrinsic fields. These arrows satisfy

- `operator X 1 = 𝟙 X`;
- `operator X (k * l) = operator X k ≫ operator X l`;
- `operator X k ≫ f = f ≫ operator Y (f.groupHom k)` for every `f : X ⟶ Y`.

The inverse label is necessary: transport composition has label
`(f ≫ g).label = g.label * f.label`. Contravariant evaluation then produces a
left action. `operatorIso` uses `operator X k⁻¹` as inverse; the two group laws
prove the inverse identities. Distinct labels remain distinct even if the
original action has a kernel.

`operator_restriction` identifies the bounded algebra pullback along this arrow
with `X.sectionOperator k`, the existing forward operator on the actual rational
quotient. Its proof uses the quotient's `hom_ext` universal property, compares
both maps after the actual base map, and applies the existing
`sectionAction_comp_baseMap` identity. This fixes the sign convention by an
equality of bounded algebra maps.

For an arbitrary category `A : Type uA` with morphism universe `vA`,
`presheafSectionAction A X` sends a presheaf `F` to `F.obj (op X)` with operator
`F.map (operator X k).op`. The functor sends every natural transformation to its
component at `op X`. The operator group laws and naturality of the component
prove the action and intertwining laws.

For every original `f : X ⟶ Y`, `presheafSectionRestriction A f` is a natural
transformation from evaluation at `Y`, restricted along the actual conjugation
homomorphism `f.groupHom`, to evaluation at `X`. Its underlying component is
exactly `F.map f.op`. The commuting operator equation proves equivariance;
ordinary presheaf naturality proves naturality in `F`. The identity and
composition lemmas state the original contravariant restriction laws on these
underlying morphisms. For changing subgroups, composition is understood with
the existing `Hom.groupHom_comp` equality.

`TransportSheaf A` is Mathlib's categorical sheaf category on this finite
topology. `evaluation A X` is its ordinary section functor.
`sectionAction A X` composes the presheaf construction with `sheafToPresheaf`;
`sectionActionForgetIso` is the identity on section objects and morphisms.
`sectionRestriction` is the same restriction transformation whiskered by that
inclusion. Thus its components are the actual sheaf restrictions. For each
category `J`, evaluation preserves limits of shape `J` whenever `A` has those
limits: Mathlib's inclusion of sheaves preserves them, and presheaf limits are
computed objectwise. A separate instance records preservation of finite limits
when `A` has finite limits.

For `R : Type uR` an arbitrary commutative ring, and independently chosen module
carrier universe `uM`, `ModuleSheaf R` specializes the sheaf category to
`ModuleCat.{uM} R`. `sectionRepresentation R X` then applies Mathlib's
`Rep.ActionToRep` to obtain the full section module as a representation of
`X.subgroup`. The action is exactly the linear map underlying
`F.obj.map (operator X k).op`. Evaluation of sheaf morphisms proves additivity.
`sectionRepresentationForgetIso` identifies its module-valued forgetful
composite with ordinary evaluation by the identity. Finite-limit preservation
follows from this identification and reflection of limits by the
representation-to-module forgetful functor.

`representationRestriction R f`, the entry declaration, is natural in the
module sheaf and intertwines these representations after restriction along
`f.groupHom.toMonoidHom`. Its linear map is precisely the actual module sheaf
map `F.obj.map f.op`. The construction uses the already proved categorical
action intertwiner, and naturality is ordinary sheaf naturality.
`representationRestriction_id_hom` and
`representationRestriction_comp_hom` give the identity and composition equations
on those linear maps, including the contravariant order of composition.

The field, group, category object and morphism, coefficient ring and module
carrier universes are independent. No coefficient topology, finite dimension,
admissibility, nonempty rational locus or faithful geometric action is assumed.
The section representations are algebraic: no smoothness, continuity, exactness,
compact support, derived or full analytic/etale comparison is asserted. This
unit does not construct arithmetic coefficients, uniformization or the Harris
specialization.

The provenance is internal. The construction uses the already implemented
`OpenSubgroupTransport`, `OpenSubgroupTransportCovering` and
`OpenSubgroupInvariantSections` constructions and their original quotient maps;
Mathlib supplies `Action`, categorical sheaves, sheaf limits, `Rep.ActionToRep`
and `Rep.resFunctor`. The new group, naturality, intertwining and preservation
obligations are proved from those constructions. No theorem is attributed to
Harris or Berkovich, and no desired action, sheaf condition or comparison is
assumed as a replacement for constructing it.

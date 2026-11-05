# Conditional simultaneous reductive and parabolic spreading

This internal construction assembles the exact simultaneous model data under
the explicit `GenericReductivitySpreadingStatement.{u}` and
`ParabolicDynamicStatement.{u}` premises. It does not prove either premise.

For every number field `F : Type u`, actual connected reductive group `G` and
actual parabolic inclusion `p : P ⟶ G`,
`modelDataOfSpreadingStatements` returns a dependent pair consisting of a
finite set `S` of finite places of `F` and the exact published
`ModelData R F p`, with `R = (S : Set (FinitePlace F)).integer F`.
The field, algebra and fraction-ring structures are the canonical structures
on this actual S-integer subalgebra. The exceptional set may depend on the
supplied group and parabolic.

The implementation uses the forward implication of the classification premise
to choose a generic cocharacter whose dynamic subgroup functor is precisely
`SubgroupFunctor.range p`. `reductiveModelData` constructs a good actual
arithmetic ambient model under the openness premise.
`enlargedCocharacterData` extends the chosen cocharacter to the canonical
finite enlargement of that model and recovers the chosen generic cocharacter
through the enlarged model's prescribed `genericIso`.

Smoothness and connected reductivity at every field-valued point persist
under the enlargement. The latter assertion implies the exact integral
`IsReductive` predicate via `isReductive_of_fieldReductive`. Noetherianity of
the enlarged actual S-integer ring is supplied by
`adelicSIntegersNoetherian`.

Closedness of `p` makes it a representative of its subgroup functor. The
proof transports that representative through the inverse of the enlarged
model's prescribed generic isomorphism, then uses
`Dynamic.parabolic_eq_comap_of_iso` and the exact cocharacter recovery equation
to identify its range with the generic dynamic subgroup of the integral
cocharacter. This supplies the exact range equality required by
`DynamicParabolic.modelData`.

The resulting parabolic model is the actual affine dynamic group, with a
generic identification to the supplied `P`. Its actual closed inclusion
extends the original `p` and satisfies `IntegralModel.Hom.generic_comm`.
`DynamicParabolic.modelData` supplies smoothness of this model and, at every
actual field-valued point, ambient connected reductivity, parabolicity of the
same inclusion and connectedness of the same parabolic fibre. Its
field-parabolic clause uses the reverse implication of the explicit
classification premise; connectedness uses the existing dynamic connectedness
proof. No auxiliary cocharacter or model is assumed as input to this assembly.

The theorem `existenceStatement_of_spreadingStatements` has the unchanged
published `ExistenceStatement.{u}` as its conclusion under exactly those two
premises. It packages the constructed dependent pair into the required
existence and nonemptiness assertions.

The provenance is internal: the new declarations assemble the imported
arithmetic model and cocharacter constructions, represented-subgroup
transport and dynamic model construction. They impose no splitness,
anisotropy, rank or proper-parabolic restriction. The two structural
premises and the full unconditional existence proof remain open.

# Good arithmetic models over canonical completion integers

Fix a number field `F : Type u`, a finite set `S` of its finite places, a
place `v` outside `S`, and a supplied
`ReductiveParabolicSpreading.ModelData` over the actual ring of `S`-integers.
The datum contains simultaneous integral models of the supplied groups and
their homomorphism, a closed model inclusion, a reductive ambient model, a
smooth subgroup model, and the three specified conditions after every
field-valued base change.

`canonicalModelData` specializes this entire datum to the canonical valuation
ring of the original completion `FiniteCompletion F v`. It uses exactly
`FiniteCompletion.valuativeRel v` and the original completion field, topology,
and coefficient map. The ambient and subgroup models are the existing
`canonicalModel` constructions, retaining their specified generic-fibre
isomorphisms. The corresponding projection theorems identify these models by
reflexivity.

The compatible inclusion is `Hom.baseChangeCoefficients` applied to the
original model inclusion. Thus its generic morphism is exactly the pullback
of the supplied `p : P ⟶ G`. Its model morphism is the actual pullback along
`canonicalIntegerMap`, as `canonicalModelData_inclusion_hom` records.
The explicit algebra structures and scalar towers are the same as in
`CanonicalIntegralModelCompletions`: the inclusion of the `S`-integers into
the completion factors both through `F` and through its canonical integers.
Closedness is preserved for this actual map by the existing coefficient
homomorphism theorem.

The three field conditions follow from `GoodFieldFibers.baseChange`, applied
to the original datum and this same coefficient morphism. Ambient and subgroup
smoothness are preserved by base change. The extended ambient model is affine
by its existing integral-model construction. `GoodFieldFibers.isReductive`
combines its smoothness and affineness with the transported field conditions
to establish the existing geometric-fibre definition of reductivity. Thus
all fields of the resulting `ModelData` are provided, including tests over
every field algebra over the canonical integers.

`canonicalModelData_specialFibre` specializes those tests to the actual
residue quotient `IntegralModel.residueBaseMap`. The conclusion gives
connected reductivity of the actual ambient special fibre, parabolicity of
the actual `Hom.specialFibreMap`, and connectedness of the subgroup's actual
special fibre. The proof uses `GoodFieldFibers.atFieldPoint`, so it retains
the specified quotient morphism directly. In particular, it does not replace
the residue field with an isomorphic preferred field or change its
coefficient map.

This module is internal transport derived from the supplied model datum,
actual coefficient base change, and the existing all-field comparison
theorems. It is uniform in universe `u`. It does not construct good arithmetic
models from generic reductivity and parabolicity, prove local integral
maximality or covering, or prove the joint integral Iwasawa family existence
statement.

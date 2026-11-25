# Actual Cartan components over their finite stabilizer fields

Derived interface material comparing actual Cartan components
over their finite separable stabilizer fields, retaining their full star
images. All groups and Tits indices are actual Library objects, and the
results apply over arbitrary fields at every universe parameter.

`CartanConnected.mapAcrossFields` transports connectivity through an injective
vertex map preserving every ordered Cartan entry, allowing different ground
fields. Its proof follows the four constructors of the equivalence closure.
Applying it to the forward and inverse vertex equivalences of an actual
`SeparableScalarExtension` proves `cartanConnected_iff`.
`SeparableScalarExtension.cartanComponentEquiv` restricts the full vertex
equivalence to the entire component of a specified vertex.

`componentFieldIndexComparison` chooses the previously constructed actual
Tits-index scalar-extension comparison for the finite separable field
`cartanComponentField`, using its chosen separable-closure equivalence.
`componentFieldCartanEquiv` is the resulting equivalence from the original
component to the corresponding actual component of the base-changed group.
Every ordered Cartan entry is preserved by the comparison's existing
`cartan_eq` field.

The component field's full absolute Galois group is identified with the
original component's full stabilizer by `cartanComponentAbsoluteGaloisEquiv`.
Its value as a ground-field automorphism is exactly conjugation through the
chosen closure equivalence followed by scalar restriction. Thus the actual
index comparison's `star_eq` is the same action used by this full group
equivalence. This proves `componentFieldIndexComparison_component_stable`:
every absolute Galois element over the component field stabilizes the
corresponding actual component.

`componentFieldIndexComparison_stabilizer_lift` takes the inverse full group
equivalence to lift each stabilizing original Galois element. Substitution in
`star_eq` proves its equality on all simple vertices simultaneously.
`componentFieldIndexComparison_star_lift` takes the forward group equivalence;
it supplies a stabilizing original element and the same simultaneous equality.
Restricting these equalities to a Cartan component retains both full
permutation image lifts.

This construction concerns the actual index of the whole base-changed group.
It does not identify the component with an actual almost-simple factor,
construct a factor-root embedding, or claim component-factor existence. It
uses no downstream local rank-one or Kneser–Tits result.

# Composition of supplied coproduct cofans

These internal categorical constructions use only the universal properties of
actual supplied cofans. They assume no existence of coproducts in any larger
index universe.

`sigmaCofan` composes each inner leg with its outer leg. Its universal
property, `sigmaCofanIsColimit`, first descends a test cofan through each
inner coproduct and then through the outer coproduct. Uniqueness applies
the outer and then the inner hom-extensionality properties.

`someCofan` deletes the `none` leg of an option-indexed cofan. If that
summand is a zero object, `someCofanIsColimit` extends every test cofan
by the zero morphism at `none` and descends through the supplied coproduct.
Its uniqueness at the omitted leg follows from the zero-object property.

The constructions are elementary consequences of Mathlib's cofan interfaces,
with independent inner, outer and category universes. They support the
assembly of finite cuspidal induced coproducts in the Bernstein argument.

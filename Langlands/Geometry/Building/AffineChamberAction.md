# The actual affine action on chambers and transport of coroot reflections

`Chambers Ψ` bundles the existing chamber subsets with their `IsChamber`
property. The root stabilizer acts by the actual image of the subset under
its affine automorphism, using the imported `IsChamber.image` theorem from
`IwahoriWeylChamberLemmas`. The action laws follow from image under the identity
and composition. No chamber transport or stabilizer theorem is assumed.

`IsCoroot.map` transports a coroot by the linear part of a root-preserving
affine automorphism and pulls its defining root back by the inverse.
The root-coroot pairing remains two. Reflection preservation of the root
set follows by pulling back along the automorphism, applying the original
coroot axiom, and then using the root-stabilizer equivalence.
`conjugate_affineReflection` proves equality of actual affine automorphisms
by evaluating them at a point and using preservation of affine addition.

These are internal constructions and elementary consequences of the existing
published definitions, with independent vector-space and torsor universes.
They require no nonempty arrangement, crystallographic assumption, or
transitivity assertion. They support the actual-action adapter in the
affine Weyl chamber simple-transitivity proof.

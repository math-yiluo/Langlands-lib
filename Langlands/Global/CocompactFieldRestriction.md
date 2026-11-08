# Matching character restrictions to a cocompact field

This internal auxiliary module implements Claim 2 of Worker 1843's plan. The
field has the discrete topology, and the target is a commutative topological
ring. The quotient of the ring's additive group by the field image is assumed
compact and Hausdorff. The continuous additive character is nontrivial and is
trivial on the field. No self-duality theorem is an assumption.

`discreteEmbedding` regards the field map as a continuous map from a discrete
group. `restriction` maps a ring element to the character of the discrete field
given by multiplication followed by the original additive character. Field
triviality makes this map invariant under adding a field element, so
`quotientRestriction` descends it to the compact quotient.

`evaluationHom` maps a field element to evaluation at that element on the full
continuous dual of the discrete field. This dual is a compact Hausdorff group,
and the evaluation characters separate its points by function extensionality.
If the pullback of one evaluation character along the quotient restriction map
is trivial, multiplication by its field parameter makes the original additive
character identically one. For a nonzero parameter this contradicts
nontriviality: multiply a test element by the inverse field parameter.
Consequently only the zero parameter gives a trivial pulled-back evaluation.

The compact character range theorem now proves that `quotientRestriction` is
surjective. Finally, restrict an arbitrary continuous character of the ring to
the discrete field, choose a preimage in the quotient, and choose a ring
representative. The result `exists_parameter` matches all its field values with
a single multiplication character. The proof does not assert that the original
field map was continuous for any topology other than the discrete topology used
here. In the actual adelic application this discrete topology is chosen locally.

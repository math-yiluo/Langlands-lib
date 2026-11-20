# Slices of covariant sections along an embedded group

The ambient sections have left covariance for a subgroup `P` of `G`. Their
restrictions to the right action of `A` through `α` have a common open right
stabilizer for each section. A continuous homomorphism `j` from the local group
`H` to `A` and a compatible map from the local subgroup `L` to `P` specify the
local action and covariance.

For an argument `a` commuting with the image of `H`, the map
`localSliceIntertwiner` sends a section `f` to the function
`x ↦ q (f (α (j x) * a))`, where `q` intertwines the restricted ambient
coefficient and the local coefficient. Left covariance follows from the
subgroup compatibility and equivariance of `q`. The preimage under `j` of
a common open right stabilizer of `f` fixes the whole slice. Commutation of
`a` with the local action gives right equivariance of the slicing map.

If every element of `G` is a product of an element of `α (j H)` and such
an argument `a`, the slices for all away arguments and separating coefficient
maps jointly detect every value of a section. This yields separating
intertwiners to actual smooth induction at `H`.

Langlands expresses global induction as a restricted tensor product of
local inductions and gives the local constituent description in Lemma 1.
In the proof of Proposition 2 he obtains covariance for the projected
sections and embeds their representation in `Ind δ⁻¹ σ`, where `δ²` is
the modular function. See *On the notion of an automorphic representation*,
Corvallis Part I (1979), printed pp. 203 and 205 (PDF pp. 198 and 200),
source `langlands-1979-notion-automorphic-representation`.

The slicing construction uses the left covariance and right-translation
action in `Langlands/Representation/Induction/Definitions.lean`. Its
coefficient representations are parameters, so the construction applies
with any twists supplied in those representations.

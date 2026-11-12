# Conrad's Proposition 5.14 for separated algebraic spaces

`Langlands.Global.adelicSpaceWeilRestriction` proves exactly the published
`Langlands.Global.AdelicSpaceWeilRestrictionStatement.{u}` in environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`. It imports the original statement and
leaves its Lean/Markdown pair and import closure unchanged. The statement is
Conrad's Proposition 5.14: along a finite extension of global fields, the Weil
restriction of a separated finite-type algebraic space is separated and of finite
type, and its original canonical full adelic map is a homeomorphism for arbitrary
separated finite-type models of the two field spaces.

The proof uses the actual integral models and full adele rings. Its supporting
local comparisons preserve the original coefficient maps and completion
topologies, include every infinite number-field factor, and retain finite
inseparable extensions of function fields. The local comparisons are applied
with the proved module-topology hypotheses at the actual completions. The proof
adds no hypothesis to the published target.

The implemented route begins with the published finite-projective space Weil
restriction theorem. Over the original field extension a module over the lower
field is free, so this theorem constructs the original field Weil sheaf as an
algebraic space and proves its finite-type and separated properties. Separatedness
of the upper space supplies the quasi-separatedness input. This gives the
algebraicity proof used throughout the exact canonical map in the conclusion.

For number fields, `AdelicSpaceWeilRestrictionProof.numberFieldSpaceWeilRestriction`
uses published spread existence to choose a separated finite-type upper model
`Z₀` outside an upper support `U`. Let `V` be the image of `U` under actual
restriction of finite places. Then `U` is contained in the full upper preimage
of `V`. Base change `Z₀` to this upper support, obtaining `Z`. Separatedness and
finite type persist under base change, and the published generic-fibre
identification after support enlargement, composed with the original model
identification, gives `eZ`.

The original lower and full-preimage upper S-integer rings form a finite
projective extension. Apply the published space Weil theorem to `Z` to construct
its actual integral Weil model `WZ`, separated and of finite type.
`NumberFieldSpaceWeilGenericFiber.genericFiberIsoOfIso` gives its specified
isomorphism `eWZ` to the original field Weil space. The full model homeomorphism
from that module has these two original spread topologies and is exactly the
canonical full adelic tensor map on forward functions.

For global function fields,
`AdelicSpaceWeilRestrictionProof.curvePlaceSpaceWeilRestriction` starts with a
separated finite-type upper model outside a nonempty support `U`. Choose the
original parameter `s` to be the image of `RatFunc.X` in the lower field. The
published function-field theorem supplies finite dimensionality over `k(s)`.
The principal exceptional-set construction provides a nonzero chart denominator
`t` whose lower support `V` contains the actual restrictions of every place in
`U`. This support is nonempty because `U` is nonempty. The full upper preimage
of `V` contains `U`, so base-changing the upper model gives `Z` and the specified
upper generic-fibre isomorphism. The original principal lower and full-preimage
upper integral bases form a finite projective extension, including inseparable
field extensions. Apply the space Weil theorem to obtain the separated
finite-type model `WZ`. The actual generic-fibre comparison and full canonical
homeomorphism are supplied by `CurvePlaceSpaceWeilGenericFiber`; the upper
support nonemptiness follows from the published place-restriction lemma.

The supporting full integral-model homeomorphisms used in both cases are proved
from arithmetic stages. Published filtered-ring point comparison covers both
full point sets by stages. A common lower stage, injectivity of coefficient
change for a separated upper space, and stage-homeomorphism injectivity prove
full counit injectivity. Cofinal full-preimage upper stages and inverse stage
homeomorphisms prove surjectivity. The original stage homeomorphisms give
continuous forward lifts; upper-stage enlargement followed by inverse stage
homeomorphisms gives continuous backward lifts. The final-topology comparison
therefore constructs the full homeomorphism. The generic-fibre comparison
identifies its counit evaluation with the actual canonical tensor map by the
cartesian Weil test isomorphism and both original coefficient evaluation maps.
Naturality retains the arbitrary upper generic-fibre identification `eZ`.

Finally, both endpoint proofs introduce the arbitrary lower and upper supports,
models and generic-fibre identifications quantified by the published statement.
Published independence of the spread topology replaces each of those topologies
with the corresponding topology of the constructed model. The pointwise
canonical-map identity from the generic-fibre module identifies the function in
the statement with the constructed homeomorphism, giving `IsHomeomorph`. This
step preserves all arbitrary-model quantifiers. The final theorem pairs the two
characteristic cases to prove the exact conjunction.

Validation: development check `3fda23e8-b40a-4fec-8c37-d113f02aca34` compiled the
full proof with zero diagnostics. Check `da42f013-f264-4075-b5bf-b41258208cba`
completed the Lake build and inspected `Langlands.Global.adelicSpaceWeilRestriction`;
its only reported axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Independent semantic review and official exact-target validation are separate
requirements of the proof submission.

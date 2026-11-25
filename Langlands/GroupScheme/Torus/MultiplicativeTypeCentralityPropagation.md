# Propagation of centrality from an open unit neighbourhood

This internal helper propagates all-test commutation on an open neighbourhood
of the unit through a connected field group locally of finite type. It
pulls back the flat surjective multiplication map from two copies of the
open along an arbitrary group-valued point. The two lifted open-valued
points commute with the source image, so their product does as well.
Flat surjective maps are epimorphisms, hence the tested commutation descends.

`evaluate_eq_of_baseChange_eq` transports equality of actual base-changed
families to equality under the canonical relative evaluations.
`commute_baseChange` transports all-test commutation on a parameter subscheme
through arbitrary base change of that parameter, the source group, and the
ambient group. It uses the actual pullback point equivalences and projection
of the parameter map. `commute_on_parameter` extracts all-test commutation
from constancy of an actual conjugation family by evaluating along each
parameter-valued test.

`commute_of_unitOpen` assumes a connected field group `G` locally of finite
type, a homomorphism `i : H → G`, and an open immersion `j : P → G` whose
range contains the unit. It assumes that every parameter-valued test point
of `P` commutes with the image of every `H`-point on that test scheme.
For any `G`-point, the proof pulls back multiplication from `P × P`.
`ConnectedFieldOpenProduct.flat` and `.surjective` make the projection to
the test scheme an epimorphism. The two lifted `P`-points commute with the
image point and so does their product. Cancelling that epimorphism descends
commutation. `isCentral_of_unitOpen` applies this after every test restriction,
giving precisely `IsCentral i`. No multiplicative-type assumption is needed
for these field lemmas.

`isCentral_residue_of_unitOpen` applies this to one connected residue fibre of
a relative group `G → S` locally of finite type. It assumes that the unit
point above the selected base point lies in the open's range, and that the
open centralizes the homomorphism on every test. The open immersion pulls
back to the fibre, all-test commutation persists by `commute_baseChange`,
and the base-point equivalence shows that the fibre unit projects to the
original unit point. Thus the fibre homomorphism is central.

`exists_open_isCentral` proves SGA 3, Exposé IX, Théorème 5.6(a), conditional
on the entire published `MultiplicativeTypeCentralRigidityStatement`.
Its source `H` is of multiplicative type; `G → S` is locally of finite
presentation, quasi-compact and quasi-separated; all canonical residue
fibres of `G` are connected; and `i` is central on the selected residue fibre.
The earlier `centralizingOpenAt` construction gives an open `W` in the
underlying scheme of `G`, containing the unit above the selected point,
where universal conjugation agrees with the constant family.

Pull `W` back along the unit section to an open `U` of `S`. At every point
of `U`, its residue-fibre open contains the unit. The preceding connected
field argument shows that the homomorphism is central on that entire
residue fibre. The earlier arbitrary-base theorem
`isCentral_of_fibres_of_centralRigidity`, applied over `U`, then gives
centrality after base change along `U → S`.

`centralityNeighbourhood` chooses one such `U`.
`mem_centralityNeighbourhood` records that it contains the selected point,
and `isCentral_centralityNeighbourhood` proves centrality on it.

There is no noetherian, smoothness, reducedness, affineness, separatedness,
or monomorphism assumption in this conditional local-spreading theorem.
The central-rigidity premise is retained and not proved here. This module
does not prove the normal immersed-subgroup clause 5.5 or claim the full
unconditional statement `MultiplicativeTypeFibrewiseCentralityStatement`. Its
provenance is the internal derivation through the named Library results,
including the helpers of the module `MultiplicativeTypeFibrewiseCentralityReduction`.

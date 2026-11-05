# Positive-power torus and additive factorization of rational points

The theorem `positivePowerTorusAdditiveFactorization` proves exactly
`Langlands.GroupScheme.PositivePowerTorusAdditiveFactorizationStatement.{u}`.
For every field `k : Type u`, smooth affine group scheme `G` over `k`,
and actual rational point `x`, a strictly positive natural power of `x`
is the product of an actual rational point of an actual closed torus in `G`
and the value at coordinate one of an actual homomorphism from the
one-dimensional additive group scheme to `G`.
There is no hypothesis on connectedness, reductivity, field perfection,
algebraic closedness, or characteristic.

The assembly is an internal consequence of the constructions imported from
`PositivePowerFactorizationData` and `CharacteristicZeroPointFactors`.
It first proves the stronger existence result `nonempty_factorizationData`
for any affine locally finite type ambient group, without requiring ambient
smoothness. The constructed data include commutation of the two chosen
ambient rational factors. `positivePowerFactorizationData` chooses these data,
and `positivePowerTorusAdditiveFactorization_commute` exports their witnesses,
factorization equation, and commutation.

The proof separates characteristic zero from prime characteristic using
`CharP.exists'`. In characteristic zero, it constructs the connected
commutative power envelope of `x`. The imported
`connectedCommutativePowerEnvelope` takes the smooth commutative schematic
closure of the rational cyclic subgroup and then its identity component.
It supplies an actual closed inclusion into `G`, a positive natural exponent
`m`, and an actual rational point of the envelope mapping to `x ^ m`.
Its smoothness construction uses geometric reduction from separating rational
coordinate evaluations, and its positive exponent comes from the finite
permutation of connected components induced by translation.

The imported `characteristicZeroPointFactors` factors that envelope point
with exponent one. Its implementation takes the central maximal torus and
the smooth connected affine quotient of a geometrically nilpotent group.
The quotient is commutative by fpqc commutator descent and unipotent by the
nilpotent no-torus criterion. Since a characteristic-zero field is perfect,
the perfect-field split-series theorem and the characteristic-zero commutative
classification give natural vector coordinates on the quotient.
The torus-vector extension construction provides a torus retraction over
the original field, obtained by finite Galois splitting and fpqc descent,
and a complementary quotient section. A vector-group line through the
projected rational point, evaluated at coordinate one, gives the actual
additive morphism. Thus this branch does not require a split original torus
or an algebraically closed field.

`ConnectedCommutativePowerEnvelope.factorizationOfPointFactors` composes the
torus inclusion and additive morphism with the envelope inclusion. It retains
the envelope's positive exponent, composes closed immersions, and transports
the point equation through `rationalPoints.map`. The factors commute inside
the commutative envelope, and their images still commute in `G`.

In prime characteristic, `positiveCharacteristicFactorizationData` already
supplies the required ambient data. It applies the central-torus construction
inside the same connected commutative power envelope. A uniform power
`p ^ r` kills the image in the unipotent quotient. The represented scheme
kernel then gives an actual rational torus point over the original field
whose image is this power. The final exponent is `m * p ^ r`, which is
strictly positive, and the additive morphism is the zero homomorphism.
This branch applies to imperfect fields and uses no surjectivity assertion
on rational points of the quotient.

Finally, smoothness in the exact target supplies local finite type.
Forgetting the extra commutation field proves the target with its original
imports and statement unchanged. `VectorGroup.coordinateOnePoint k`
definitionally unfolds to the target's literal inverse coordinate-map image
of `Multiplicative.ofAdd (fun _ => 1)`. The additive parameter is therefore
one; the identity point has coordinate zero. All inclusions, morphisms, and
points use the existing actual group-scheme and `rationalPoints.map`
interfaces, and rank-zero tori and trivial additive morphisms are permitted.

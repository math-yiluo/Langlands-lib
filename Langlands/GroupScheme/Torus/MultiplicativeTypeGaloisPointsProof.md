# Points of a group of multiplicative type over intermediate fields

`Langlands.GroupScheme.multiplicativeTypeGaloisPoints` proves
`Langlands.GroupScheme.MultiplicativeTypeGaloisPointsStatement.{u}`. The theorem
identifies points over each intermediate field of a separable closure by
evaluating all characters of the base change. It proves injectivity and
characterizes the range by multiplicativity and equivariance under the
automorphisms fixing the intermediate field.

## Lean proof

The proof obtains a diagonalizable model `G_Ks ≅ D(M)` over the separable
closure using `MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed`
and preservation of multiplicative type under algebraic base change.
`modelCharacters` pulls the diagonalizable characters back along this
isomorphism. `modelPoints` transports the diagonalizable point equivalence
along the same isomorphism and applies the isomorphism
`Γ(Spec Ks, 𝒪) ≅ Ks` to units. The formula in `eval_modelCharacters`
identifies character evaluation with application of the corresponding
homomorphism `M → Ksˣ`. It gives separation of points by characters and
realizes every multiplicative family of character values as a point.
Multiplicativity at the zero character and cancellation in `Ksˣ` supply the
identity law for that homomorphism.

On the original affine group, `GaloisPoint.coordinates` identifies points
with algebra maps out of the affine coordinate ring. Extension from `K` to
`Ks` postcomposes these maps with the inclusion, so it is injective. A
coefficient automorphism acts on the coordinate map by postcomposition.
Consequently extended points are fixed by the subgroup fixing `K`.
Conversely, for a fixed point, `InfiniteGalois.fixedField_fixingSubgroup`
puts each coordinate in `K`. `AlgHom.codRestrict` then gives the coordinate
map of a `K`-point that extends to the original point.

`baseChangeCoeffEquiv` carries this fixedness criterion to rational points
of `G_Ks`. Simultaneous Galois transport of a character and a point acts on
their evaluation by the coefficient automorphism. Thus the character
values of an extended point are equivariant. For the converse, realize a
multiplicative family as a point over `Ks`. For an automorphism fixing
`K`, evaluate the conjugate point at a character by using its inversely
transported character and the simultaneous transport identity.
Equivariance of the given family implies that the conjugate has the
original character values. Character separation makes the point fixed, so
coordinate descent realizes the family over `K`. The two injections,
extension on points and evaluation on the diagonalizable model, give
injectivity of the map in the statement.

## Source

The target is Remark 12.26 on printed page 240 of J. S. Milne,
*Algebraic Groups* (2017), registered as `milne-2017-algebraic-groups`
with SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The proof implements the argument recorded with the
[statement](MultiplicativeTypeGaloisPointsStatement.md), using the point
and character descriptions of Proposition 12.3 and Lemma 12.4 on printed
pages 231–232 and separable-closure splitting as in Theorem 12.18(a) ⇒ (d)
on printed page 237. The fixed-field argument uses Mathlib's infinite
Galois correspondence and applies to every intermediate field in the
statement.

# Coroot character calibration for coherent rank-one coordinates

For either algebraic coordinate record over an arbitrary field `k : Type u`,
`corootPoint` is the group homomorphism from the units of the coordinate
extension to the rational points of the supplied commutative group scheme `Z`.
It is the inverse of `WeilGm.rationalUnitsEquiv`, followed by the rational point
map of the record's actual induced-torus morphism `coroot`. The theorem
`map_corootPoint` restates the record's compatibility with the diagonal matrix
after mapping into `G`.

For `AlgebraicSL2RootCoordinates`, `character_corootPoint` says that the
positive coordinate's rational character, evaluated at the extension of this
point to the coordinate field, is `t ^ 2`. The proof compares two conjugations
of the upper root element at parameter one: the character action supplied by
the coordinate record and the explicit diagonal matrix conjugation in SL2.
Injectivity of the coordinate equivalence then gives the character equality.

For `AlgebraicSU3RootCoordinates`, the corresponding character value is
`SU3Root.diagonalRootScalar (SU3Root.fieldInvolution C.base C.extension) t`.
The proof uses `rationalLift C.base C.extension 1`, whose first coordinate is
one. It bundles the published diagonal conjugation formula as an equality in
the special unitary subgroup and maps it through the common homomorphism
`rho`. Comparison with the supplied character action, followed by injectivity
of the coordinate equivalence and projection to the first coordinate, gives
the scalar equality.

Both `eval_corootPoint` theorems additionally assume that `S` and `Z` are
affine, restriction evaluation along `s : S.toGrp ⟶ Z.toGrp` is bijective,
and the extension additive valuation `w` is norm calibrated to the integer
valuation `v` on `k`. They identify the root pairing
`eval S b (IntegerValuation.centralizerValuation v s h (C.corootPoint t)).toAdd`,
coerced from the real numbers to `WithTop ℝ`, with `2 • w (t : C.extension)`
in SL2 and with `w (t : C.extension)` in SU3. The SU3 theorem also assumes
invariance of `w` under the quadratic involution.

The proofs apply norm calibration to the positive rational character, use
`IntegerValuation.characterNormOrder_eq_eval` and the coordinate's restriction
identity to compute the centralizer pairing, and then use the proved character
equality. The final calculations are the additive valuation power law for SL2
and `SU3Root.diagonalRootScalar_value` for SU3.

This is an internal comparison derived from the supplied algebraic coordinate
records and the published explicit matrix, character norm, and valuation
identities. It asserts no coordinate existence, apartment origin, or coordinate
depth formula.

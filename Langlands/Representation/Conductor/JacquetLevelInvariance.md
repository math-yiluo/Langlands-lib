# Jacquet group invariance on the original carrier

This internal unit transfers the published integral Jacquet generation
identities to the actual general linear group over the field and to its
representation fixed spaces. It also applies the published negative-level
Whittaker obstruction to the source's integer scaling convention. It is
auxiliary progress toward the conductor theorem; the analytic derivation of
the two invariances remains an obligation.

Let `F` be a field, `O` a subring, and the matrix rank be `n + 1`.
`fieldJacquetLevelMirabolic O n I` is the field image of the actual integral
group `integralJacquetMirabolic n I`, for an ideal `I` of `O`. At the unit
ideal it equals `fieldJacquetMirabolic O n`, the intersection of the integral
field subgroup with the last-row mirabolic. The proof retains actual
integral invertible representatives and reflects the last-row conditions
through the injective subring inclusion.

`fieldJacquetLevelMirabolic_map_inverseTranspose` identifies its
inverse-transpose image with
`congruenceSubgroup O n I ⊓ oppositeMirabolic n F`. The inclusion of
integral matrices commutes with inverse transpose, and the last-column
condition is reflected through the same subring inclusion. Thus this is
the actual field group, with both matrix and inverse integrality retained.
For a subgroup, plain transpose and inverse transpose have the same image.

If `O` is a local ring and `0 < n`, the two field Jacquet groups generate
`congruenceSubgroup O n I`. The proof applies subgroup image to the published
integral generation theorem and uses preservation of subgroup suprema.
It includes the unit ideal, so it includes the full integral group at
level zero.

For any representation over a commutative coefficient ring, with an
independent carrier universe, `jacquetInvariantSpace` is the intersection
of the fixed subspaces of `fieldJacquetMirabolic O n` and
`congruenceSubgroup O n I ⊓ oppositeMirabolic n F`.
`jacquetInvariantSpace_eq_fixedVectors` proves that it equals the fixed
subspace of the actual field congruence subgroup. The stabilizer of each
vector is a subgroup, so fixing two subgroups is equivalent to fixing
their supremum. With `O` the valuation integer ring and
`I = maximalIdeal ^ a`, the specialization
`jacquetInvariantSpace_eq_levelFixedVectors` identifies it with the
unchanged `levelFixedVectors π a`. This argument requires neither topology
nor smoothness, admissibility, irreducibility, or Whittaker genericity.

For a rank-at-most-one valued field with a topology and a nontrivial
unitary additive character, `one_le_valuation_of_jacquet_invariant`
proves `1 ≤ v(q)` for every nonzero standard Whittaker function invariant
on the right under both `fieldJacquetMirabolic` and
`scaledOppositeJacquetMirabolic q`. If instead `v(q) < 1`, the published
negative-level vanishing theorem would force the function to be zero.
`nonneg_of_uniformizer_jacquet_invariant` substitutes `q = ϖ^(-m)` for an
integer `m` and an `IsUniformizingElement` witness. If `m < 0`, the positive
power `v(ϖ)^(-m)` is below one, a contradiction. No relation between `m`
and any epsilon factor is assumed or proved.

The provenance is internal: the new results follow from
`MirabolicLevelGeneration`, `NegativeLevelGeneration`, the unchanged
congruence definitions, and elementary properties of subgroup images,
stabilizers, and valuations. Those imported modules document the original
JPSS 1981 Section 5.3 argument and its corrected negative-level group
boundary. This unit neither uses the flawed essential-vector existence
argument nor asserts full field general linear group generation.

No essential vector, nonzero vector, minimal fixed level, dimension-one
fixed space, functional equation, or factor comparison is constructed.
In particular, the two Jacquet invariances and Whittaker nonvanishing
are supplied to the sign lemmas. These lemmas do not prove
`EssentialConductorStatement`.

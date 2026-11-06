# Finite-level approximation in the original quotient L2 space

This internal proposition targets finite-level approximation on the existing
`Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i)`. Its finite representation
is exactly `haarQuotientL2FiniteRightAction`, obtained by restricting the original
right action along `AdelicGroupPoints.ofFinite`. The quotient, measure, null
classes, norm and finite adelic point topology retain their original meanings.

The conclusion chooses one sequence `K n` of actual open subgroups. Each
underlying set is compact in the original finite adelic group. Their carriers
form an antitone basis of the identity neighborhood filter: they decrease and
every identity neighborhood contains one, hence contains every sufficiently
late member. The sequence is chosen before quantifying over the L2 vector,
so it works for every vector at once.

For each member, `A n` is the existing operator
`haarQuotientL2FiniteAverage` with compactness of its inherited subtype
installed from the displayed original-set compactness proof. It is the actual
Bochner integral against normalized probability Haar measure on that subgroup.
There is no independently supplied approximation operator or smoothness
assumption. The proposition requires every output to lie in the existing
`Langlands.fixedVectors` submodule for that exact subgroup and requires
`A n φ` to converge to `φ` in the original L2 norm for every vector.
It also states density of the existing `Langlands.IsSmoothVector` set for
this finite action.

The hypotheses are those of the original canonical quotient action: an
arbitrary number field, affine locally finite-type group scheme, supplied
finite split central torus, injective finite-index character restriction
and norm-one right-Haar invariance. Connected reductivity, a matrix embedding
and a preexisting locally profinite premise are not additional assumptions.

Provenance is internal. The intended derivation combines the actual finite
adelic compact open basis with second countability and
`Filter.HasBasis.exists_antitone_subbasis`. Continuity at the identity of each
original orbit makes its difference from the input uniformly small on every
sufficiently late subgroup. The probability Haar norm estimate then bounds
the difference of its average from the input. The actual fixed-vector
identity puts each approximant in the existing smooth set, giving density.
These facts explain the derived target; this statement file does not prove it.

This is density for the finite adelic action. Archimedean differentiability,
simultaneous smooth automorphic tensor realization as in Getz–Hahn 6.1,
admissibility, growth, decay, trace and spectral assertions remain separate
obligations.

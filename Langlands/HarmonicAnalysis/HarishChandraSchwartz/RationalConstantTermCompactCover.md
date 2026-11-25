# Actual compact Cartan reduction for constant terms

This module applies the bounded-kernel compact reduction
to the actual rational-point weights in `RationalConstantTerm`. It addresses
the difference between the structural compact subgroup `K0`, the subgroup `K`
defining the spherical functions, and the subgroup preserving the height.
All results here are derived helpers; the full actual constant-term estimate
remains a separate proof target.
The proposition `RationalConstantTermCompactCoverStatement.{u}` is proved by
`rationalConstantTermCompactCover`, at arbitrary field universe `u`.

For each real exponent, the ambient and standard Levi kernels
`Ξ(g)(1 + σ(g))^r` and `Ξ^M(m)(1 + σ(m))^r` have uniformly bounded
translations by any compact subgroup. This holds for every matrix
representation of nonzero size; closedness is not needed for these helpers.
The proofs use the published translation bound for `Ξ`, its standard Levi
analogue proved here from the generic spherical translation bound,
nonnegativity, inversion symmetry and subadditivity of the actual height.
Both kernels are bi-invariant under the open intersection of the subgroup
defining `Ξ` with `rationalHeightSubgroup ρ`, read inside the Levi when
appropriate. The generic compact-uniformity theorem supplies the constants.

`rationalLeviCartanRepresentatives i ν J F0` is the set of actual Levi points
`f i(a)` with `f` in the finite centralizer family `F0` and `a` in the full
torus chamber `CAplus F S J`. The supplied
`StandardLeviCartanCovering` gives a double-coset cover by these points and
`K0 ∩ M_J(F)`. The proof takes the representative of `m = k₁ f i(a) k₂`
to be `k₁⁻¹ m k₂⁻¹`; this has the required expression and already belongs
to the actual Levi subgroup.

`rationalConstantTermEstimate_of_compact_doubleCosetCover` extends a
constant-term estimate on any supplied representative set to all of the
actual standard Levi. Its only analytic premise is the estimate on that set.
It verifies the compact kernel bounds above, the compactness of
`K0 ∩ M_J(F)`, the actual conjugation modulus relation and triviality of
the modulus on `K0 ∩ M_J(F)`, then applies
`constantTermEstimate_of_doubleCosetCover`.

The groups are the actual points of connected reductive affine groups of
finite type over arbitrary nonarchimedean local fields. The maximal split
torus, generic cocharacter and standard root subset are the same as in
`RationalConstantTerm`. No equality between `K0` and `K`, nor invariance
of the height under `K0`, is required. This module does not supply the
representative estimate, weighted unipotent integrability, the Levi lower
bound or the change of minimal-parabolic orientation.

Source motivation: J.-L. Waldspurger, *La formule de Plancherel pour les
groupes p-adiques, d'après Harish-Chandra* (2003), literature ID
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`,
Proposition II.4.5 and its initial Cartan reduction, printed pp.262–263.
The bounded-translation adaptation to independently supplied compact
subgroups is derived here.

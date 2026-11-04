# Nonidentity normalizers from actual proper homogeneous quotients

These are internal constructions from the published actual fixed-coset,
projective-orbit and torus-diagonalization APIs and the fixed-line comparison
in `TorusFixedQuotientPoints`. They introduce no new external assertion.

`nonidentityNormalizerOfFixedCosets` works over an arbitrary field. Let an
actual maximal torus `i : T ⟶ G` factor through a closed subgroup
`j : P ⟶ G`. Supply internal conjugacy of maximal tori in `P`, an actual
quotient morphism with exact all-test right-coset fibers, and containment
of the whole-torus centralizer points in `P`. Two supplied rational group
points have distinct quotient sections, both fixed by the torus on every
test. The construction returns an actual element of `normalizerPoints i`
together with a proof that its class in `relativeWeylGroup i` is not the
identity.

The fixed-coset comparison first supplies normalizer representatives
`n₁,n₂` of the two specified sections. The construction returns `n₁⁻¹*n₂`.
If its class were the identity, the two classes would be equal; applying
the actual coset map would equate the two distinct sections. This argument
requires neither rational lifts of any other quotient section nor a
finiteness assertion for the Weyl quotient.

`nonidentityNormalizerOfNonfixedProperFlagQuotient` works over an
algebraically closed field, in any universe. The ambient group is locally
of finite type. Supply a closed subgroup `P`, an actual factorization of
`i` through `P`, containment of the whole-torus centralizer points in `P`,
internal conjugacy of maximal tori in `P`, and a flat, surjective,
quasi-compact quotient morphism onto a proper scheme with exact all-test
`P`-coset fibers, and a finite-dimensional matrix representation whose
coordinate-line stabilizer is exactly `P` on all tests. A supplied
rational group point has nonfixed quotient section for the canonical
quotient action restricted to `T`. The result is an actual normalizer
point with nonidentity class. No dynamic-parabolic, solvability, rank-one
or reductivity hypothesis is required by this generic construction.

The implemented proof obtains homogeneous-equation closedness of the
coordinate-line orbit directly from
`ProjectiveOrbit.exists_eq_smul_orbit_of_isProper`, using the exact fibers
and stabilizer. The proved `torusFiniteGaloisSplitting` supplies the torus
diagonalization through `FlagCore.exists_torusDiagonal`; no universal
splitting premise remains. Smoothness of the torus follows from maximal
torus membership, and separatedness of the quotient follows from
properness. The fixedness comparison makes the supplied orbit line
nonfixed. Two extreme-weight contractions then supply nonproportional
fixed orbit lines and their actual group representatives. The same
comparison supplies all-test fixedness of their quotient sections; exact
quotient fibers prove the sections distinct. The supplied torus factor
and centralizer containment give the remaining inputs of
`nonidentityNormalizerOfFixedCosets`.

`Dynamic.nonidentityNormalizerOfNonfixedProperFlagQuotient` is a small
specialization for a closed representative `P` of the actual dynamic
parabolic of a supplied cocharacter of `T`. Its canonical torus factor
and the containment of the torus centralizer in the dynamic centralizer
and then in the dynamic parabolic discharge the generic factorization
and centralizer inputs. It retains the same supplied proper quotient,
line stabilizer, internal conjugacy and nonfixed section.

The generic construction retains actual torus factorization and
centralizer containment, internal torus conjugacy, the proper represented
quotient and exact line stabilizer, and a nonfixed rational section as
explicit inputs. In particular, it does not prove centralizer containment
for an arbitrary prescribed Borel subgroup. These constructions do not
establish the remaining inputs, a tangent-dimension bound, or
`RankOnePositiveRootUniquenessStatement`.

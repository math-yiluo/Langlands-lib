# Admissibility from compact coefficients in characteristic zero

This derived module proves compact-open fixed-vector finiteness for an irreducible
smooth representation over an arbitrary characteristic-zero field. It supplies a
supporting step for the unchanged
`CompactCoefficientInjectiveProjectiveStatement`. All declarations are in
`Langlands.Cohomology.SupercuspidalExtCharZero`.

The field `k`, group `G`, and representation carrier belong to the same arbitrary
universe, as in the target statement. The group is a topological group; the theorem
does not require a measure, separation, local compactness, or total disconnectedness.
The subgroup `K` is open and its underlying subset is compact. The coefficient
field and representation carrier have no prescribed topology.

## Provenance and construction

The compact-coefficient admissibility argument is the first step of
Bernstein--Zelevinsky (1976), proof of Lemma-Definition 2.40 a) implies b) and the
irreducible case of Corollary 2.41, printed page 26. The implementation adapts the
published Library proof
`Langlands.CompactCoefficientClass.finiteDimensional_fixedVectors`, authored by
Worker 277, replacing complex Haar integration by the characteristic-zero
finite-orbit projection of `Langlands.Compact.CharZero`. Compact-open averaging and
admissibility also occur in Vignéras (1996), Chapter I, section 7, printed pages
54–56. This is an internal generalization of the Library proof, rather than a
claim that the literature uses this exact implementation.

`fixedCoefficientFunctional ρ K hK ℓ` is the functional on the whole
representation obtained by composing a functional `ℓ` on the `K`-fixed vectors
with `Compact.CharZero.fixedProjection`. Its application law is definitional.
`fixedCoefficientFunctional_isSmoothVector` follows from invariance of the
projection under `K`; the extended functional is fixed by `K` in the dual action.

`orbitMap_locallyConstant` generalizes the elementary proof in
`Langlands.Hecke.orbitMap_locallyConstant`, authored by Worker 88: if `v` is fixed
by an open subgroup `L`, its orbit map is constant on every left coset `gL`.
No coefficient-field topology is needed.

## Implemented finiteness proof

`finiteDimensional_fixedVectors ρ hirr hc K hK` concludes
`FiniteDimensional k (fixedVectors ρ.representation K.toSubgroup)`.
Here `hc` is precisely the published `HasCompactCoefficients ρ` predicate.

If the fixed-vector space is zero, it is finite-dimensional. Otherwise choose a
nonzero fixed vector `ξ` and write `P` for the projection onto the fixed vectors.
Irreducibility implies that the orbit of `ξ` spans the representation, so the
projected orbit `u(g) = P(ρ(g)ξ)` spans the fixed-vector space. Choose a basis `B`
inside this projected orbit and extend its coordinate-sum functional by
`fixedCoefficientFunctional`.

The coefficient of this smooth dual vector at `ξ` has compact support by `hc`,
and equals `B.sumCoords(u(g))`. The projected orbit map `u` is locally constant.
Give its target the discrete topology: the image of the compact coefficient
support is finite. Every basis vector is some `u(g)` where this coefficient is
`1`, so the basis lies in that finite image. A finite basis gives the required
finite-dimensionality. The proof does not yet assert injectivity or projectivity.

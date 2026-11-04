# Actual projective data for a supplied proper homogeneous quotient

Author: Worker 1547.

This internal construction packages existing Chevalley and projective-orbit
results for an actual supplied quotient. It works over every field in universe
`u`, in every characteristic. The ambient group `G` is smooth and affine, and
`b : B → G` is an actual closed subgroup. The supplied map `q : G → Q` is smooth,
surjective and quasi-compact, `Q` is proper over the field, and its fibers on
every relative scheme test are exactly the right cosets of the range of `b`.
There is no connectedness, reductivity, algebraic-closure or solvability
assumption. Neither a representation nor smoothness of `B` is supplied.

`HomogeneousQuotient.ProjectiveEmbeddingData b q hfib` stores a natural number
`n`, a coordinate `j : Fin (n+1)`, an actual matrix representation `ρ` of `G`,
and the exact all-test coordinate-line stabilizer equality

`x ∈ range b` if and only if `ρ(x)e_j = c e_j` for a unit `c` of the test
scheme's global sections.

It also stores an actual map `φ : Q → Pⁿ`, its closed-immersion property, the
factorization `q ≫ φ = lineOrbitMap n j ρ`, and matrix equivariance for the
canonical scheme action of `G` on this same quotient. The data structure only
requires flatness, surjectivity and quasi-compactness of `q`; smoothness of the
ambient group and quotient map and properness of `Q` are hypotheses of its
constructor.

`projectiveEmbeddingData` constructs these data. The closed inclusion is monic,
and `HomogeneousQuotient.smooth_subgroup_of_smooth_quotient` identifies `B` with
the smooth identity fiber of the exact quotient. Then
`Chevalley.exists_line_stabilizer` supplies `n`, `j`, `ρ` and the exact
coordinate-line stabilizer on all relative scheme tests. The existing
`ProjectiveOrbit.quotientOrbitMap` descends its coordinate-line orbit map through
`q`. Its factorization theorem gives the stored equality.
`ProjectiveOrbit.isClosedImmersion_quotientOrbitMap` uses smoothness of `G` and
`B` and properness of `Q` to prove that this same descended map is a closed
immersion. Finally,
`ProjectiveOrbit.isMatrixEquivariant_quotientOrbitMap` applies because the
canonical quotient action sends the lift of `h` under the action of `g` to the
lift of `gh`.

`ProjectiveEmbeddingData.restrict_equivariant` applies the existing restriction
law to any group homomorphism into `G`. In particular, it gives the actual
matrix-equivariant closed embedding for the torus action when a torus inclusion
is supplied.

The provenance is internal composition of the named published constructions.
This module introduces no further structural theorem about algebraic groups.
Properness and exact quotient existence remain hypotheses. It supplies neither
a projective torus fixed-point dimension theorem nor the bound that a rank-one
quotient has dimension at most one. Those are separate prerequisites in the
positive-root uniqueness proof.

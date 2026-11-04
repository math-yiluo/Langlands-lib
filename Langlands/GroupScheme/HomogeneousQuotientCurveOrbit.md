# Actual orbits on smooth homogeneous quotient curves

This internal helper concerns an actual quotient map `q : G.X ⟶ Q` by a
supplied subgroup homomorphism `b : B ⟶ G`. Its exact all-test fiber condition
is `q(g) = q(h)` if and only if `g⁻¹h` belongs to the all-test range of `b`.
The map is quasi-compact, flat and surjective when its descended action is
used. These are hypotheses, rather than a construction of the quotient.

The stabilizer of the actual identity coset is exactly the range of `b`.
Evaluation of the descended action at a lift identifies the stabilizer
equation with `q(g) = q(1)`; the exact fiber condition proves the equality on
every test scheme. If `b` is monic, it represents this stabilizer.
Consequently restriction along `i : U ⟶ G` fixes the identity coset on all
tests exactly when the range of `i` is contained in the range of `b`.

Over any field, a smooth surjective map from a smooth connected affine group
has smooth, reduced and irreducible target. Smoothness descends from the
source, smooth schemes over a field are reduced, and the continuous
surjection carries the irreducibility of the group to the target.

Over an algebraically closed field, suppose in addition that the quotient
is separated and has topological Krull dimension at most one, and that `U`
is smooth, connected and affine. If its all-test range is not contained
in the range of `b`, `curveOrbitData` constructs a rational `U`-point that
moves the identity coset and proofs that the orbit map of that same coset
is dominant and quasi-compact. The construction uses the published
nonfixed curve orbit argument, after deriving nonfixedness from the exact
stabilizer computation. The field, schemes and groups have universe `u`.

The final theorem applies the existing conditional unipotent dominant
orbit bound. It assumes the explicit proposition
`AlgClosedReductiveNormalSolvableTorusStatement`, a pseudo-reductive ambient
group, a solvable closed `B`, smooth connected affine unipotent groups `H`
and `U`, a monic `i : U ⟶ G`, a closed `j : H ⟶ U`, the Lie-dimension
bound `dim Lie(U) ≤ dim Lie(H) + 1`, noncontainment of `U` in `B`, and
containment of the composite `H ⟶ G` in `B`. The actual stabilizer
calculation makes `H` fix the identity coset; `curveOrbitData` supplies
the required dominant quasi-compact orbit. The conclusion is that the
range of `j` is trivial, `dim Lie(H) = 0` and `dim Lie(U) ≤ 1`.

This is an internal derivation from existing Library results. No external
structural assertion is discharged here. In particular the final theorem
retains the normal-solvable-torus proposition as an explicit input.
Quotient existence, its dimension bound, subgroup noncontainment and the
positive-root uniqueness target remain separate obligations.

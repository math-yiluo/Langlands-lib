# Affine neighbourhoods of finite sets in an ample proper fibre

The theorem
`Langlands.AlgebraicGeometry.Picard.properFibreAmpleAffineOpen` proves exactly
`ProperFibreAmpleAffineOpenStatement.{u}` in every universe. For a proper
morphism `f : X ⟶ S` with locally noetherian base, a specified actual line
bundle `L` on `X`, and an arbitrary point `s : S`, ampleness of the
pullback of `L` to the scheme-theoretic residue-field fibre implies that
every finite set of points of `X` mapping to `s` is contained in one
affine open of `X`.

The implemented proof applies the published implication
`properFibreAmpleAffineOpen_of_spreading` from
`ProperFibreAmpleAffineOpenReduction` to the published theorem
`properFibreAmpleSpreading` from `ProperFibreAmpleSpreadingProof`.
The latter discharges the implication's entire spreading premise:
the same specified bundle becomes ample on the inverse image of an
affine open neighbourhood `V` of `s`.

The imported reduction puts the finite set inside `U = f ⁻¹ᵁ V`,
takes its finite inverse image under the open inclusion `U.ι`, and
applies `exists_isAffineOpen_of_finite_of_ample` to the actual restricted
bundle on `U`. The image of the resulting affine open under `U.ι`
is an affine open of `X` containing the original finite set.
This is the proof implemented by the imported reduction.

This module is an internal composition of these published Library
results; their paired explanations supply the geometric derivations
and source comparisons. It adds no hypothesis to the exact target.
The finite set may be empty, points need not be closed, and schemes
may have nilpotents. The target and all imported pairs are preserved.
The application to canonical polarization bundles, integral CM models
and representability remains with its assigned owners.

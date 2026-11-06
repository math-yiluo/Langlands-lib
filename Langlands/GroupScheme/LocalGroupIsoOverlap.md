# Universal overlap discrepancy

Author: Worker 1442.

This is an internal categorical adapter for the existing natural local group
isomorphisms and actual automorphic actions. It follows from representability
of pairs of cover points and group points by products in the relative scheme
category. It uses no external structural existence theorem.

An actual morphism `δ : U ⊗ U ⟶ A.X` represents a family of acting points by
pullback along `lift b c` for each pair of cover points `b,c : T ⟶ U`.
`LocalGroupIso.HasOverlapDiscrepancy` is one equality of morphisms on
`(U ⊗ U) ⊗ G.X`: the first local map, corrected by the action of `δ`, equals
the second local map at the universal group point.

`discrepancy_of_overlap` pulls this equality back along `lift (lift b c) g`.
Naturality of the local maps and the actual action recovers the equation for
every test scheme and every group point. `hasOverlapDiscrepancy_iff` proves
the converse by evaluation at the universal pair and universal group point.
`discrepancy_on_refinements_of_overlap` then gives the same equation after
every refinement of a test, with acting point `t ≫ (lift b c ≫ δ)`.

For an existing natural cocycle `ξ`, `Cocycle.overlap` is its value at the
universal pair of cover points. The theorem `toFun_eq_lift_overlap` derives
all its values from this morphism using naturality.
`LocalGroupIso.hasDiscrepancy_iff_overlap` identifies the existing
`HasDiscrepancy` condition with the single universal equation.

All results hold over arbitrary base schemes in arbitrary universe `u`,
without hypotheses on the cover object or the group schemes. The file
constructs no cocycle from `δ` and assumes no cocycle identity for an
arbitrary `δ`. It does not construct quasi-split models, adjoint quotients,
finite Galois extensions, or inner discrepancies.

# Local positive-depth exchange of the original root blocks

This internal construction packages the original constant-depth two-factor block as a subgroup and proves its local opposite exchange at every positive depth. The block's carrier remains the original set product; neither factor is removed.

Actual doubled-root centrality gives closure of that carrier under multiplication and inversion. The supplied centralizer-depth image normalizes every root-depth subgroup because it lies in the original centralizer-zero subgroup, hence in the actual norm-one kernel. Full omega compatibility makes its points fix the original apartment point, and the actual normalizer action preserves each root direction. Conjugation therefore preserves both factors of the original block.

For a supplied commutator-friendly centralizer filtration, four constituent exchanges retain the same positive depth `r`. The ordinary opposite-root exchange gives a central coordinate at `2r`, which lies in the filtration at `r`. The mixed doubled-positive exchange gives a central coordinate at `r/2+r`, also at least `r`, and retains the original positive block. Applying this mixed result to inverses in the opposite direction gives the mixed doubled-negative exchange. Ordinary exchange in the doubled-root direction handles the two doubled factors; absent doubled roots are treated as identity subgroups.

The general group lemma `twoFactorBlockExchange` combines these four inclusions. It expands both blocks in their original order, applies the constituent exchanges, moves centralizer factors using the proved normalizer containments, and absorbs products inside the two actual block subgroups and the supplied centralizer subgroup. Consequently `filtrationBlock_mul_opposite_subset` proves
`B_a,r B_-a,r ⊆ B_-a,r j(Z(F)_r) B_a,r`
for every actual root and `r > 0`, with the original two-factor blocks on both sides. The full apartment axioms and commutator friendliness are explicit hypotheses; the other centralizer-filtration axioms are not needed for this local result.

This is the complete local block exchange step, including nonreduced relative root systems. Global exchange across positive systems, full Moy–Prasad covering, covariance, centralizer-filtration existence and the host simultaneous-basis theorem are not established by this module.

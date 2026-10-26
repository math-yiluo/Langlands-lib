# Cyclic factor selection in the actual restricted product

`Langlands.flathCyclicVectorSelection` proves exactly the published
`Langlands.FlathCyclicVectorSelectionStatement`, with independent index,
local group, and carrier universes. It selects one nonzero ambient vector
whose coordinate cyclic representations are all admissible and irreducible.
Outside a finite exceptional set the vector is fixed by each reference
subgroup and its cyclic representation has a one-dimensional reference fixed
space. The whole reference tail, including infinitely supported elements,
fixes the selected vector.

The helper `selection_of_splittings` pulls the given representation back
through each actual continuous multiplicative coordinate splitting. Published
group-transport lemmas preserve admissibility and irreducibility; the singleton
formula identifies its first restriction with the coordinate action. The two
conjuncts of the published `twoFactorCyclicExtraction` theorem supply the
refinement and spherical hypotheses of `select_of_extraction`. Irreducibility
gives a nonzero ambient vector, and full-tail fixedness starts that finite
selection argument. The selection machinery preserves all previously chosen
cyclic properties while refining the vector at the finitely many exceptional
coordinates.

`selection_of_twoFactorCyclicExtraction` discharges the splitting and initial
tail hypotheses using the published restricted-product topology. The
complement is the actual `ComplementGroup H {i}` in universe `max uI uG`.
Openness supplies its topological-group structure, and compactness with local
compactness supplies its locally compact structure. Hausdorffness and total
disconnectedness are inherited from the coordinate groups. The inverse of
`singletonSplitEquiv` supplies the splitting and its singleton formula.
`exists_tail_fixed_of_isSmooth`, applied to the smoothness included in
admissibility, supplies a full reference tail fixing each vector. The final
theorem applies the published two-factor extraction proof at universes `uG`,
`max uI uG`, and `uV`.

This is an internal derived selection step for Flath factorization, combining
the published cyclic-extraction, finite-selection, and restricted-product
topology results. It adds no tensor decomposition assumption, countability
condition, or restriction on the index type; in particular finite and empty
index types are retained. The local carriers are cyclic subspaces of the
original carrier. This module proves selection only: constructing the actual
restricted-tensor equivalence remains a separate step in the final existence
proof. The target Lean/Markdown pair and its imports are unchanged.

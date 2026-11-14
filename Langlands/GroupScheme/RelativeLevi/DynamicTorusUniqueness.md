# Dynamic Levi complements containing the defining cocharacter

Worker 592.

This internal result specializes the published arbitrary-base dynamic Levi
conjugacy calculation in `Rational.DynamicLeviConjugacyReduction`. It supplies
a uniqueness step for relative Levi subgroups once the actual dynamic
presentation and the equality of their radical images have been established.

For any scheme `S`, a separated group scheme `G`, a cocharacter `χ`, and a
representative `j : P ⟶ G` of `P_G(χ)`, suppose `l : L ⟶ P` has a retraction
`q : P ⟶ L`. The all-test kernel of `q`, viewed in `G`, is required to be
exactly `U_G(χ)`. If `χ` factors as `μ ≫ l ≫ j`, the theorem proves
`range (l ≫ j) = Z_G(χ)` as subgroup functors.

Given any representation `z : Z ⟶ G` of that centralizer, the definition
`centralizerComplementIso` constructs an isomorphism `L ≅ Z`. The theorem
`centralizerComplementIso_hom_comp` states that its composite with `z` is
`l ≫ j`, so the isomorphism respects the actual inclusions in `G`.

The proof cancels the monomorphic `j` to identify the cocharacter of `P`
with `μ ≫ l`. Its image under `q` is `μ` by the retraction identity. Thus
the conjugacy equation in the imported
`range_comp_innerIso_inv_eq_centralizer` holds with conjugating point `1`.
That theorem gives the asserted equality after simplifying the identity
inner automorphism.

For the isomorphism construction, the retraction identity makes `l`
monomorphic, and `j` is monomorphic because it represents the parabolic.
Their composite therefore represents the centralizer by the range equality.
The published uniqueness-of-representatives construction
`SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy` supplies the
isomorphism and its compatibility with the inclusions.

No reductivity, torus, parabolic, radical existence, or descent theorem is
asserted. Those hypotheses must supply the displayed actual presentation,
retraction, kernel equality and cocharacter factorization in an application.
This is derived content from the cited Library lemmas, not a transcription
of an additional literature assertion.

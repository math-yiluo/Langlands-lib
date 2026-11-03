# Limits in a closed normalized subgroup

This internal derivation defines `SubgroupFunctor.IsLimitStable F χ`: every
limit under `χ` of any point of `F` belongs to `F`, on every test scheme.

For any base scheme, a represented closed subgroup normalized by the range of
`χ` has this property. The orbit lies in the subgroup by normalization.
`AffineLine.exists_lift_of_unitInclusion` then factors every orbit extension
through the closed subgroup. Evaluation at zero gives the limit in the
subgroup. The cocharacter need not factor through the subgroup, and no
separatedness is required for this assertion.

Over `Spec R` for any commutative ring `R` and in a group whose underlying
scheme is affine, the existing closed representative
`Dynamic.Affine.unipotentHom χ` supplies this result for any normalizing
cocharacter `ψ`. Range containment in `Dynamic.centralizer χ` implies the
required normalization, because the dynamic centralizer lies in the dynamic
parabolic and that parabolic normalizes `U(χ)`.

The auxiliary `Dynamic.range_le_centralizer ψ` proves that the image of a
cocharacter lies in its own dynamic centralizer. On every test scheme, the
universal parameter and the given multiplicative-group point commute;
their images in the ambient group commute, so conjugation fixes the latter.

If `Dynamic.centralizer ψ ≤ Dynamic.centralizer χ`, any point in
`U(χ) ∩ P(ψ)` belongs to `U(ψ)`: its `ψ`-limit lies in `U(χ)` by the preceding
result, and in `Z(ψ) ≤ Z(χ)` by uniqueness of limits. Since a point in
`U(χ) ∩ Z(χ)` is the identity, that limit is the identity. This also proves
`U(χ) ∩ P(ψ) = U(χ) ∩ U(ψ)` as subgroup functors. Affineness over `Spec R`
supplies the separatedness used by the existing uniqueness theorem.

These affine conclusions quantify over all test schemes, including nonaffine
and nonreduced ones. They impose no field, smoothness, connectedness,
finite-presentation or reductivity assumption.

The provenance is an internal consequence of the published modules
`Dynamic.ClosedSubgroup`, `Dynamic.AffineRepresentability` and
`Dynamic.LimitMap`. The application to two cocharacters comes from the joint
Bruhat proof development of Workers 1226 and 1262. This unit does not assert
centralizer containment for generic cocharacters or a Bruhat factorization.

# Levi-first multiplication for represented dynamic subgroups

This is an internal comparison between the actual scheme morphisms already defined in
`Rational.LeviSubgroup` and `Dynamic.SchemeDecomposition`. It uses no new geometric
structure theorem or external source assertion.

For group schemes `L` and `U` over an arbitrary base scheme `S`,
`subgroupProductReversal L U` is the isomorphism of schemes over `S` sending
`(l, u)` to `(u⁻¹, l⁻¹)`. Its inverse has the same formula with the two group
schemes exchanged. The two inverse identities follow from the product projections
and involutivity of inversion.

For homomorphisms `l : L ⟶ P` and `r : U ⟶ P`,
`subgroupProductReversal_hom_comp_subgroupMultiplication` identifies reversal
followed by `subgroupMultiplication r l` with `subgroupMultiplication l r`
followed by inversion in `P`. The proof uses preservation of inverses by the
homomorphisms and the formula `(a b)⁻¹ = b⁻¹ a⁻¹` in the group of scheme maps.
Since both reversal and inversion are isomorphisms,
`isIso_subgroupMultiplication_reverse_iff` proves that multiplication is an
isomorphism in one factor order exactly when it is so in the other order.
No commutativity or normality hypothesis is needed for this comparison.

Suppose the separated group scheme `G` has a cocharacter `χ`, and `iP`, `iZ`
and `iU` represent its dynamic parabolic, centralizer and unipotent subgroup
functors on every test scheme. Given actual homomorphisms `l : Z ⟶ P` and
`r : U ⟶ P` with `l ≫ iP = iZ` and `r ≫ iP = iU`,
`Dynamic.subgroupMultiplication_eq_multiplication` identifies the unipotent-first
subgroup multiplication with the existing `Dynamic.multiplication`. It checks
the equality after the monomorphism representing the parabolic. The existing
`Dynamic.isIso_multiplication` and the order comparison then prove
`Dynamic.isIso_subgroupMultiplication` for the Levi-first map.

`Dynamic.leviMultiplicationIso` packages that actual Levi-first multiplication
as an isomorphism `Z.X ⊗ U.X ≅ P.X` in `Over S`. Its forward morphism is exactly
`subgroupMultiplication l r`, as recorded by `leviMultiplicationIso_hom`.
All these constructions are universe-general. The point formulas represent
scheme morphisms, so the isomorphism is stronger than a bijection on field points.

This module is a bridge for the multiplication clause in `IsRationalLeviSubgroup`.
It supplies no existence of a parabolic cocharacter, no reductivity of a
centralizer and no identification of the represented unipotent subgroup with
a geometric unipotent radical. Those remain separate obligations before this
bridge can construct a rational Levi in the parabolic radical/torus theorem.

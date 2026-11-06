# The unit cell for the same extended negative-rho character

This is an internal composition of the published negative-rho character,
bi-covariant centralizer criterion and Bruhat unit-cell lift. It preserves
the same torus, subgroup, cocharacter, root datum and character throughout.
It is a conditional construction within the Steinberg big-cell task.

Let `k : Type u` be a field, let `G` and `H` be group schemes over `Spec k`
with affine structure morphisms, and let `T` be a commutative group scheme.
The construction is supplied with connected reductivity of `G`, splitness
of `T`, a maximal-torus embedding `j`, a finite root datum `P` on the actual
character and cocharacter lattices with `IsRootDatumOf j P`, a base of `P`,
and generation of the full integral cocharacter lattice by the coroots.
The root index type lies in `Type u`.

An actual cocharacter `nu` is supplied whose dynamic parabolic is represented
by `i : H → G` and whose dynamic centralizer is represented by the same `j`.
The character on `H` is the published extension of negative rho along the
actual dynamic limit homomorphism. A normalizing rational point `n` is
supplied whose inverse pullback on characters sends negative rho to rho.

The general `conjugateTorusFactor` construction composes the torus factor
through `H` with the inverse normalizing automorphism. Its composition with
the conjugate subgroup inclusion is the original `j`. Applying this
construction to the centralizer-to-parabolic inclusion proves that the
restrictions of the same negative-rho character to the two copies of the
torus are additive negatives.

Suppose a supplied coordinate `d` of `G` is left covariant for this
negative-rho coordinate and right inverse covariant for the identical
coordinate through the conjugate subgroup. Both covariance statements are
on all relative test schemes. The coroot values of its restricted weight
are the negative dual heights, hence nonzero. The published bi-covariant
centralizer theorem therefore proves that every normalizing rational point
where `d` is a unit centralizes this same embedded torus.

For the global construction, `k` is additionally algebraically closed,
the supplied rational Bruhat covering holds for `i` and `j`, and the
conjugate inclusion represents the opposite dynamic parabolic of `nu`.
Connected reductivity supplies the smoothness and local finite type of `G`.
The affine dynamic construction supplies an actual representative of the
unipotent subgroup, so no separate unipotent representative is assumed.
`negativeRhoUnitCellLift` uses these data and the proved centralizer
criterion to construct a morphism into the unipotent/opposite-parabolic
multiplication cell. Its composition with multiplication is the original
point. Projection, parabolic containment and inversion give
`g = i(c) i'(c')⁻¹` whenever `d(g)` is a unit.

The relative test scheme is arbitrary, including nonaffine and nonreduced
schemes, and the two factors are global points of that original scheme.
This construction does not prove existence of the supplied structural
data, the normalizing point with its negative-rho action, the Bruhat cover,
or a coordinate with both covariance laws. It proves neither normalization
of `d` nor Steinberg irreducibility, and does not prove the full
`SteinbergBigCellStatement`.

# Primitive normalized polarizations of Harris data

This internal module chooses a canonical integral representative of the
polarization class of a polarized Harris action. The ordinary Harris relation
`TateNormalizedCMOrdinaryRelated` identifies polarizations up to a rational
scalar. The ordinary moduli functor of `PolarizedFiniteLevel` instead uses an
actual polarization of fixed degree. The representative chosen here is the
primitive actual homomorphism of which the given polarization is a positive
integer multiple. It adds no literature assertion and no new premise.

## Definition

`HarrisPrimitivePolarization X lam0` is the definition of the module. For a
polarized Harris action `X` (`PositivePolarizedAction`) and an actual
homomorphism `lam0` from its abelian scheme to its constructed dual, it says
that `lam0` is primitive (`Tate.IsPrimitiveHom`) and that `k • lam0` equals
the polarization of `X` for some positive integer `k`.

`harrisIntegralLattice_finrank_pos` records that the actual integral source
lattice has positive rank. Its rank is `2 [E:ℚ] n²` by the published
`harrisIntegralSource_rank`, and `1 < n` is part of the central simple
unitary datum.

## Existence from a normalized frame

`harrisPolarization_divisor_le` takes a normalized Harris frame `eta` at an
algebraically closed point `s` of the base, with every positive integer a unit
on the base. If `k • lam0` equals the polarization for a positive `k`, then
`k` is at most the number of `s`-points in the kernel of the polarization.
That kernel is finite by the published
`GroupScheme.IsIsogeny.finite_ker_pointsHom`, because a polarization is an
isogeny. The polarization `k • lam0` kills the actual `k`-torsion points
(`Tate.levelMap_nsmul_self`), so these points inject into the kernel. Through
the published `harrisIntegralFrameTorsionEquiv` and
`harrisIntegralReducedSourceCoordinates`, the `k`-torsion points correspond
to functions from a basis of the source lattice to `ZMod k`. There are
`k ^ r` of them with `r` the positive rank, and `k ≤ k ^ r`.

`exists_harrisPrimitivePolarization` applies
`Tate.exists_isPrimitiveHom_nsmul_eq` with this bound. It gives a primitive
`lam0` with `k • lam0` equal to the polarization.

## Uniqueness

`harrisPrimitivePolarization_unique` assumes a connected locally noetherian
base, the finite-étale torsion statement and an algebraically closed point.
Two primitive polarizations of the same `X` are then equal, by
`Tate.eq_of_nsmul_eq_nsmul_of_isPrimitiveHom`. No frame is needed for
uniqueness.

This module does not show that the primitive representative is a
polarization, compute its degree, compare it along the ordinary Harris
relation or along base change, or construct a moduli map.

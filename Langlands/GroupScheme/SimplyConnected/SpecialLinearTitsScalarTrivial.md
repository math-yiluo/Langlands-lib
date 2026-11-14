# Scalar inner representatives give trivial discrepancies

Module: `Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsScalarTrivial`.

This module connects the projective descent of the inner part of the Tits cocycle
with the predicate `HasTrivialDiscrepancy` from
`Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsOuterDiscrepancy`. It has no
literature counterpart of its own: it is internal glue for the descent behind
`OuterTypeAUnitarySplitPresentationStatement`. Mathematically it records the standard
fact that conjugation by a nonzero scalar matrix is the identity, so a
coordinate change that turns every inner cocycle value into a scalar trivialises the
corresponding discrepancies.

Setting: `K → L` is a field extension, `G` is a group scheme over `Spec K`, and
`E : LocalGroupIso (SL_{n+1}) G (cover K L)` identifies `G` with `SL_{n+1}` after
base change to `L`. For `σ : L ≃ₐ[K] L`, `discrepancy E σ` is the automorphism of
`SL_{n+1}` comparing `E` with its `σ`-twist, and `HasInnerDiscrepancy E σ X` says that
on every test `Z` with cover point `a : Z ⟶ cover K L` this automorphism is
conjugation by the coefficient image of `X ∈ GL_{n+1}(L)`.

## `HasInnerDiscrepancy.discrepancy_eq_self_of_scalar`

If `HasInnerDiscrepancy E σ (scalar c)` for some unit `c : Lˣ`, then
`discrepancy E σ a g = g` for every test `Z`, cover point `a` and point `g` of
`SL_{n+1}` over `Z`.

Proof: compare images in `GL_{n+1}` (`SpecialLinearGroup.toGL_injective`). By the
hypothesis the image of the discrepancy is `s * g * s⁻¹` with `s` the coefficient
image of `scalar c`. The lemma `map_scalar_mul_conjugate` (from
`Langlands.LinearAlgebra.SpecialLinearHermitianNormalization`), applied with `J = 1`,
says that conjugation by the image of `scalar c * 1` agrees with conjugation by the
image of `1`, which is the identity.

## `hasTrivialDiscrepancy_coordinateChange_of_scalar`

Let `H` be a subgroup of `L ≃ₐ[K] L`, `x : (L ≃ₐ[K] L) → GL_{n+1}(L)` with
`HasInnerDiscrepancy E σ (x σ)` for every `σ ∈ H`, and `P ∈ GL_{n+1}(L)` such that for
every `σ ∈ H` there is a unit `c : Lˣ` with

`P⁻¹ * x σ * σ(P) = scalar c`

where `σ(P)` is `GeneralLinearGroup.map σ.toRingHom P`. Then
`HasTrivialDiscrepancy (coordinateChange E P) H`: in the presentation changed by `P`,
every discrepancy for `σ ∈ H` is the identity on every test.

Proof: for `σ ∈ H`, the Library lemma `HasInnerDiscrepancy.coordinateChange`
(`SpecialLinearTitsCoordinateChange`) shows that `P⁻¹ * x σ * σ(P)` is an inner
representative of the discrepancy of `coordinateChange E P`. By hypothesis this matrix
is `scalar c`, and the previous lemma gives the identity.

The theorem is the scalar analogue of the Library lemma
`discrepancy_coordinateChange_eq_self`, which treats an exact coboundary
`x σ = P * σ(P⁻¹)` for a single `σ`.

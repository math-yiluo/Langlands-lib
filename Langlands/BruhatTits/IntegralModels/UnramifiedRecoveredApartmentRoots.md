# Prescribed upper tori and root intersections in recovered apartment models

This derived adapter applies the published integral-torus and neutral-root
constructions to `RecoveredApartmentFixerModels`, retaining the supplied
apartment and its original generic torus. It is a supporting construction for
the special-apartment chamber problem.

Let `F : Type u` be a nonarchimedean local field, `K = inertiaFixedField F`,
and `G` an affine connected reductive group scheme over `F`. Supply a
commutative group scheme `T`, an inclusion `iT : T → G` whose base change
`iT_K` is a maximal split torus and an underlying-scheme monomorphism, an
actual apartment `D` for `iT_K`, and its centralizer `C` with the full integer
`IsOmegaCompatible` condition. For any subset `Ω` of this apartment, supply
`M : RecoveredApartmentFixerModels D Ω`. In particular, its upper full
integral points are exactly the character-valuation kernel intersected with
the pointwise fixer of `D.apartmentMap '' Ω`.

In the namespace `RecoveredApartmentFixerModels`,
`upperFullApartmentTorus` constructs
`IntegralSplitTorusData M.upper.full iT_K`, and
`upperFullApartmentTorus_isClosedSubgroup` proves its inclusion closed.
`upperNeutralApartmentTorus` factors the same actual integral split torus
through `M.upper.neutral`; its inclusion is also closed. Both data retain
the generic identification with the prescribed `T_K` and the commuting
square with the original `iT_K`.

For every actual relative root `a` of `iT_K`,
`rootGroupPoints_inf_upperNeutral_eq_rootFixer` identifies

```text
rootGroupPoints iT_K a ∩ M.upper.neutral.integralPoints
  = D.rootFixer a Ω.
```

`rootGroupPoints_inf_upperNeutral_eq_full` identifies this intersection
with the corresponding intersection for `M.upper.full`. For nonempty
`Ω` bounded above under every real affine functional,
`rootGroupPoints_inf_upperNeutral_eq_filtration` gives the exact
filtration `D.filtration x a (D.rootFixerDepth a x Ω)` at every reference
point `x` of the original apartment.

For any supplied `UnramifiedZeroDatum F G_K`, with no compatibility
requirement on its torus,
`rootGroupPoints_inf_upperNeutral_eq_zeroFixer` identifies the same
intersection with that of
`E.zeroPoints ∩ D.pointwiseFixer (D.apartmentMap '' Ω)`.
`sharpFixer_le_upperNeutral` places the entire sharp fixer
`D.sharpFixer Ω` in the upper neutral integral points. Apart from the
filtration formula, these results impose no nonemptiness or boundedness
condition on `Ω`.

The proof forms `buildingDataOfApartment hG hiT D C hDC`, whose apartment
and generic torus are exactly the supplied ones. It applies
`unramifiedIntegralSplitTorusData` to `M.full_integralPoints` and uses
`IntegralSplitTorusData.factorNeutral` and its closedness theorem.
The root equalities and sharp inclusion specialize the published
`UnramifiedNeutralRoots` and `UnramifiedZeroRoots` theorems; the full
intersection equality uses the constructed split torus and the full
model's supplied smoothness. This is internal composition of existing
results and introduces no new literature assertion.

The constructions work at arbitrary universe `u` and in every residue
characteristic. The recovered models remain supplied. This adapter does
not assert equality of the entire neutral subgroup with a zero fixer,
special-fibre maximality of the constructed torus, quotient-root
survival, or the existence of an ordinary coefficient-stable chamber.

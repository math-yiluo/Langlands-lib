# Inflation and restriction for the number-field Hasse kernel

Module: `Langlands.GroupScheme.Rational.NumberFieldHasseInflation`.

## The main theorem

`Cocycle.isTrivial_of_baseChange_isTrivial_of_kernel` concerns a number field `F`, an
affine group scheme `G` over `Spec F` (the hypothesis is `IsAffine G.X.left`) and two finite
Galois extensions `L/F` and `E/F` in the same universe. It also takes a finite Galois
extension `M/F` with compatible `F`-algebra maps `L → M` and `E → M`, given as scalar towers
`F → L → M` and `F → E → M`. No reductivity, simple connectedness or type hypothesis is used.

Let `ξ : Cocycle G (GaloisCocycle.cover F L)` satisfy:

- `ξ.LocallyTrivial`: triviality after pullback to the full cover at every place of `F`;
- `(ξ.baseChangePullback (Spec.algebraMap F E)).IsTrivial`: triviality of the base change
  of `ξ` to `E` on the full pullback cover `Spec (L ⊗_F E) → Spec E`;
- every locally trivial cocycle of `G` on the cover `GaloisCocycle.cover F E` is trivial.

Then `ξ.IsTrivial`.

In Galois-cohomological terms this is the inflation–restriction argument: a class of
`H¹(L/F, G)` that dies in `H¹(E, G)` comes, after inflation to `M`, from `H¹(E/F, G(E))`;
the class it comes from is again locally trivial, so it vanishes when the localization
kernel of the cover `E/F` is trivial. The theorem is used to pass from an arbitrary finite
Galois cover to a quadratic cover in the Hasse principle for simply connected groups, as in
Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994), §6.8 (for instance the
argument for groups of type `¹E_6` on printed p. 383), where a class in the kernel of
localization is first shown to split over `K(√-1)`.

## The proof

1. Refine `ξ` to the cover `Spec M` with `GaloisCocycle.coverMap F L M`. By
   `GaloisCocycle.value_refine` its value at `σ ∈ Aut(M/F)` is the extension of the value of
   `ξ` at the restriction of `σ` to `L`.
2. `GaloisCocycle.exists_galois_coboundary_of_baseChange_isTrivial`, applied to the
   triviality over `E`, gives a point `a` of `G` over `M` such that for every
   `E`-automorphism `τ` of `M` the refined value at `τ` equals `a · τ(a)⁻¹`.
3. Twist the refined cocycle by `a`. Its value at `σ` is `a⁻¹ · value σ · σ(a)`. If `σ`
   restricts to the identity on `E`, then `σ` fixes the image of `E` (by
   `AlgEquiv.restrictNormal_commutes`), so it is an `E`-automorphism; step 2 shows that the
   twisted value at `σ` is `1`.
4. `GaloisCocycleTowerRecovery.value` descends the twisted values to points of `G` over `E`
   indexed by `Aut(E/F)`, with the cocycle identity
   (`GaloisCocycleTowerRecovery.value_mul`) and exact recovery after extension
   (`GaloisCocycleTowerRecovery.extend_value`). `GaloisCocycle.ofValues` turns them into a
   cocycle `θ` on `GaloisCocycle.cover F E`. The values of `θ` refined to `M` agree with the
   twisted values, so by `GaloisCocycle.toFun_eq_of_value_eq` the refinement of `θ` and the
   twisted cocycle agree on all pairs of points.
5. `θ` is locally trivial. Local triviality passes to refinements
   (`Cocycle.LocallyTrivial.refine`) and to cohomologous cocycles
   (`Cocycle.LocallyTrivial.of_cohomologous`, from the published
   `Cocycle.Cohomologous.baseChange`), so the refinement of `θ` to `M` is locally trivial. At
   a place `v`, `Cocycle.baseChange_pullback_refine_toFun` identifies the base change of
   this refinement with the refinement of the base change of `θ` along the pullback of
   `Spec M → Spec E`. The pullback of `Spec M` to the completion is flat, quasi-compact and
   surjective over the completion (`fieldExtension_fpqc` and stability under pullback), so
   `Cocycle.IsTrivial.of_refine_fpqcCover` gives triviality of the base change of `θ`.
6. The hypothesis on `E/F` makes `θ` trivial. Hence its refinement, the twisted cocycle,
   the refined cocycle (`Cocycle.IsTrivial.of_twist`) and finally `ξ`
   (`GaloisCocycle.isTrivial_of_refine`) are trivial.

## Auxiliary results

- `Cocycle.IsTrivial.of_cohomologous`: triviality passes to cohomologous cocycles.
- `Cocycle.cohomologous_twist`: a cocycle is cohomologous to each of its twists.
- `Cocycle.cohomologous_of_toFun_eq`: cocycles with equal values on all pairs of points are
  cohomologous.
- `Cocycle.LocallyTrivial.of_cohomologous`: over a number field, local triviality passes to
  cohomologous cocycles.

## Provenance

This is an internal composition of the Library's Galois-value interface for natural
cocycles (`GaloisCocycle`, `GaloisCocycleRefinement`, `GaloisCocycleConstruction`,
`GaloisCocycleLocalTrivialization`, `GaloisCocycleTowerRecovery`), cohomology of cocycles
(`CocycleCohomology`) and fpqc reflection (`CocycleAffineRefinement`). It is the
nonabelian inflation–restriction sequence for a normal subgroup of a finite Galois group,
in the form used in Platonov and Rapinchuk (1994), §6.8.

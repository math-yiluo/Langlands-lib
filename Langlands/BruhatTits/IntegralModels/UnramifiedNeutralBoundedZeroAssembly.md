# Neutral integral points for bounded nonempty apartment subsets

This internal module builds on `UnramifiedNeutralZeroAssembly` and discharges its
zero-fixer decomposition premise for every bounded nonempty apartment subset.
The universe parameter `u` is arbitrary. The group is any actual affine group
scheme over `K = inertiaFixedField F` with supplied
`C : MaximalUnramified.BuildingData F G` and original
`E : UnramifiedZeroDatum F G`; it need not descend to `F`.

`UnramifiedZeroDatum.wholeApartmentZeroFixer_sup_sharpFixer_eq` proves

```text
E.zeroPoints ∩ Fix(C.apartmentMap '' Ω)
  = (E.zeroPoints ∩ Fix(C.apartmentMap '' univ)) ⊔ C.sharpFixer Ω.
```

Here `Ω` is nonempty and every real affine function on the apartment is bounded
above on `Ω`. The pointwise fixers use the original building action. The join
is a join of subgroups of the original `rationalPoints G`. This theorem has
no additional universal proposition premise.

The proof applies
`wholeApartmentZeroFixer_sup_sharpFixer_eq_of_simplyConnectedNormalizer`
to the published unconditional theorem
`MaximalUnramified.simplyConnectedNormalizerAffineWeyl`. The latter concerns
simply connected groups; the imported zero-normalizer comparison handles the
simply connected derived cover supplied by `E`. Consequently the present
theorem imposes no simply connectedness hypothesis on `G`. All other
normalizer, root-fixer and boundedness arguments are those of the imported
integer-valued comparison.

`unramifiedNeutral_integralPoints_eq_zeroFixer_of_bounded` then applies the
existing neutral assembly with this proved decomposition. It assumes an actual
`D : RelativeComponentModelData (fixedFieldIntegers F) K G` and the exact
full-point equality

```text
D.full.integralPoints =
  characterValuationKernel (MaximalUnramified.valuation F) G
    ∩ Fix(C.apartmentMap '' Ω).
```

Its remaining two universal premises are
`UnramifiedTorusIwahoriModelStatement.{u}` and
`UnramifiedTorusConnectedBoundStatement.{u}`. They respectively supply the
smooth connected model of the norm-defined torus Iwahori subgroup and the
upper bound for every smooth connected torus model. The conclusion identifies
`D.neutral.integralPoints` with the original zero fixer of `Ω`. No compatibility
assumption on the original torus choices in `E` remains.

`unramifiedNeutralBoundedZeroFixerEquiv` packages this equality as a
multiplicative equivalence. Its coercion theorem is reflexive because
`MulEquiv.subgroupCongr` preserves each ambient rational point.

The provenance is internal composition of the published normalizer proof,
bounded zero-fixer reduction and neutral assembly. This module does not
prove either torus premise, construct the full model, or extend the conclusion
to translated apartment images. Those are further parts of the complete
`UnramifiedParahoricModelStatement`, which `unramifiedParahoricModel` (module
`UnramifiedParahoricModelProof`) proves.

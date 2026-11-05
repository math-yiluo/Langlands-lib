# Canonical torsor structure on actual square-zero Picard lifting fibres

This internal construction uses the published actual Picard obstruction,
quotient/kernel equivalence and nested-thickening naturality, together with
Mathlib's definition of an additive torsor. It assumes no further external
mathematical assertion.

Let `i : Y ⟶ X` be a closed immersion of schemes in any common universe `u`,
with compact underlying spaces and `hi : i.ker ^ 2 = ⊥`. Write
`Q = SquareZeroPicardFibres.infinitesimalClasses i hi`, the actual additive
quotient `H¹(X,ker(i)) / image(boundaryMap i hi 0)`. Its relation subgroup
is the image of the actual unit-H⁰ connecting map, with no asserted
scalar stability. Let `E = infinitesimalClassesEquivKernel i hi`, the
published additive equivalence from `Q` to the kernel of actual scheme
Picard pullback.

The abbreviation `fibre i y` is exactly the subtype
`{x : Group X // Group.pullback i x = y}`. The group `Group X` classifies
actual tensor-invertible module sheaves, and its pullback is the existing
scheme-module pullback. No lift of `y` is chosen in this abbreviation.

`fibreTranslate i hi y q x` has ambient Picard value `E(q).val + x.val`.
The kernel property of `E(q)` and the fibre property of `x` show that
this value still pulls back to `y`. The instance `fibreAddAction` gives
this operation the notation `q +ᵥ x`. Additivity of `E` and the ambient
group laws prove its identity and associativity laws. The action exists
even on an empty fibre. `coe_vadd` records the ambient value.
`coe_vadd_mk` specializes it to a representative `a : H¹(X,ker(i))`:
the resulting ambient class is `oneAddPicardMap i hi a + x.val`, using
the actual published `1+a` Picard map.

`fibreDifference i hi y x x'` is `E.symm` applied to the kernel element
with ambient value `x.val - x'.val`. Pulling back this difference gives
`y - y = 0`. Equivalence cancellation and addition/subtraction cancellation
prove `fibreDifference_vadd` and `fibreDifference_vadd_cancel`: taking
the difference of `q +ᵥ x` and `x` recovers `q`, and translating `x'`
by the difference of `x` and `x'` recovers `x`. These formulas use no
distinguished lift.

The theorem `fibre_nonempty_iff` restates the existing `picard_lift_iff`
as nonemptiness of this actual subtype precisely when
`SquareZeroPicardObstruction.obstructionMap i hi y = 0`. Given a proof
of that vanishing, `fibreAddTorsor` constructs
`AddTorsor Q (fibre i y)`. Its action is `fibreAddAction`, its
subtraction is `fibreDifference`, and its nonemptiness comes from the
obstruction criterion. The construction takes no chosen lift as input.
It is a named structure rather than a global torsor instance, so a
consumer can install it locally when the obstruction vanishes.

For a chosen actual lift `x` of `y`,
`infinitesimalClassesEquivFibre_eq_vadd` identifies the published
chosen-lift classifier with evaluation `q ↦ q +ᵥ x`.
`infinitesimalClassesEquivFibre_add` proves compatibility with translation
of parameters by the action law.
`infinitesimalClassesEquivFibre_symm_eq_difference` identifies its inverse
with the canonical difference from the chosen lift. The first and last
identities are definitional.

For a further morphism `j : Z ⟶ Y`, assume also compactness of `Z`,
that `j ≫ i` is a closed immersion, and square-zero kernel for `j ≫ i`.
The published `SquareZeroPicardNaturality.fibreMap i j y` keeps the ambient
Picard class and maps to the fibre over `Group.pullback j y`. The theorem
`fibreMap_vadd` proves that this map intertwines the canonical actions
through the published `infinitesimalClassesMap i j hi hji`.
`fibreDifference_fibreMap` proves that it also intertwines canonical
differences. Both follow from the published compatibility of `E` with
the actual inclusion of pullback kernels; the difference proof also
cancels the quotient/kernel equivalences. No separate immersion or
nilpotence hypothesis on `j` is used for these identities.

The fibre has a canonical action and difference, and a torsor structure
when nonempty. This module supplies no scalar structure, finiteness,
general scheme base-change comparison, representability of a family of
lifting fibres, or proof of the full fppf Picard representability target.

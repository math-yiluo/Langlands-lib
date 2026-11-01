# Open-cover descent of the normalized Harris determinant

Author: Worker 344.

This is an internal derivation from the published actual Lie determinant,
its base-change theorem, rational-action classes, and Mathlib's separation
theorem for sections on a scheme open cover. It introduces no new assertion
from external literature. The arithmetic data, signature charts and
determinant predicates are those of the imported modules.

All schemes and arithmetic fields in this file have universe zero. The
reflex-field result has the existing totally real field `E`, totally complex
quadratic extension `F`, central simple unitary datum `D`, CM section `Φ`,
signature charts `C`, and proof `hΦ` that `Φ` is a CM section. It takes an
actual structure map to the existing cocharacter reflex field, an actual
abelian scheme `B`, and its rational algebra action `i`. The later results
specialize to the existing normalized Harris section from the imaginary
quadratic CM field `L` and embedding `τ₀`, with an actual map `p` to `Spec F`.
There is no additional `IsCMField F` assumption.

## Descent of the actual determinant

`harrisRationalLieDeterminantCondition_of_openCover` proves the original
all-family, all-chart, all-smaller-open determinant condition if it holds
for the actual family and action pulled back along each map of any
`S.OpenCover`. The cover need not be finite, affine, or locally directed.
The test schemes need not be reduced.

The proof fixes an arbitrary finite family of order elements, finite Lie
chart, and smaller open. For each cover member it uses the actual
`lieBaseChangeChart`. The theorem
`lieRationalSectionDeterminant_baseChange_of_naturality`, supplied with the
proved `lieBaseChangeNaturalityStatements`, identifies the pulled-back Lie
polynomial with the image of the original polynomial under the actual map
on structure-sheaf sections. The prescribed reflex polynomial has the
matching pullback identity. The local determinant assumption therefore
equates these two mapped polynomials.

Polynomial extensionality reduces global equality to equality of each
coefficient. Mathlib's `Scheme.OpenCover.ext_elem` then separates the two
actual sections by their restrictions to the inverse images of the chosen
smaller open. Thus the proof establishes equality in the full section ring,
including its nilpotents; it does not replace the equation by tests on
geometric points or polynomial functions.

`harrisTaylorCMRationalLieDeterminantCondition_of_openCover` transfers this
descent result through the existing equivalence between the normalized CM
predicate and the reflex-field predicate.
`harrisTaylorReflexStructure_comp` identifies the structure maps on each
cover member. The proof retains the existing conjugated
`harrisTaylorReflexToCM` normalization through that equivalence.

## Rational-action classes and test maps

`harrisTaylorCMDeterminantClassCondition_of_openCover` proves the same
descent for an actual `RationalAlgebraAction.IsoClass`. It chooses an actual
representative using `classOf_surjective`, applies the representative
descent theorem, and uses
`harrisTaylorCMDeterminantClassCondition_classOf` on the actual pulled-back
representatives. The quotient and its existing equivariant rational
isomorphism relation are unchanged.

`HarrisTaylorCMDeterminantPullbackCondition` is a property of each actual
map `g : T ⟶ S`. It applies the existing class determinant predicate over
`g ≫ p` to the actual pullback of the class of `(B, i)`. The class formulation
allows successive pullbacks to be compared by the existing strict equality
`RationalAlgebraAction.pullbackClass_comp`.

`harrisTaylorCMDeterminantPullbackCondition_iff` proves that this property is
exactly `HarrisTaylorCMRationalLieDeterminantCondition` on
`(baseChange g).obj B` with action `(rationalBaseChangeEnd g B).comp i`
and structure map `g ≫ p`. It is an equivalence with the full existing
predicate, with no weakening of its order-family, Lie-chart, or smaller-open
quantifiers.

`harrisTaylorCMDeterminantPullbackCondition_comp` proves stability under
arbitrary precomposition. It applies the published class base-change
theorem with the proved Lie naturality theorem and then uses pullback class
composition and associativity of actual scheme maps.

`harrisTaylorCMDeterminantPullbackCondition_of_openCover` proves locality on
every open cover of any test scheme `T`. Its assumption is the property of
each composite `𝒱.f k ≫ g`; class composition converts these assumptions
to those of class descent. In particular this applies to the pullback of
any cover of the original base.

These results supply stability and locality for a subsequent construction
of a global closed determinant locus. This file constructs neither that
locus nor an ambient moduli scheme, and proves no representability,
admissibility, smoothness, or projectivity assertion.

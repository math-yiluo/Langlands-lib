# Finite first-order Picard families and weighted restrictions

This internal construction extends the actual simultaneous family of
`FiniteTangentFamily`. Its hypotheses are a commutative ring `k`, a field
`k`-algebra `K`, an actual scheme morphism `f : X ⟶ Spec k`, and an
actual line bundle `M` on the relative residue scheme. The rings, schemes
and finite index type `ι` retain an arbitrary common universe `u`.
Properness, projectivity and smoothness are not assumed.

For directions `v : ι → ArtinianDualNumberComparison.Classes f M` and
coefficients `c : ι → K`, the theorem `family_weighted` identifies the
pointed class of the actual restriction of `family f M v` along
`FiniteTangents.weighted k K c` with `∑ i, c i • v i`. Here the test ring
map is literally `(a,w) ↦ (a, ∑ i, c i * w i)`, and scalar multiplication
on pointed classes is the existing actual restriction along epsilon
scaling. The theorem includes the empty finite sum and zero coefficients.
It is a class equality; an actual compatible isomorphism between any chosen
representatives follows from the definition of the isomorphism quotient.

The proof first compares ordinary normalization with the existing additive
tangent group. `comparison_forgetClass` records the underlying actual bundle
pullback for every pointed class, by quotient induction.
`spaceIso_section` proves that the actual pullback-associativity comparison
preserves the constant projection. Its proof uses the two projections and
the pullback condition. Consequently `comparison_dualSplit` identifies the
constant ordinary lift with the canonical split lift used by the published
pointed tangent construction.

`comparisonTangentAddEquiv` composes the existing additive equivalences
for actual Artinian dual-number classes and normalized pointed tangent
classes. `comparison_normalized` says that pulling back the normalized
ordinary class along the space isomorphism gives the underlying normalized
deformation-kernel class of this additive comparison. Pullback along an
isomorphism is injective. This proves `normalized_zero` and
`normalized_add`, and hence the additive homomorphism `normalizedAddHom`
into the additive notation for ordinary tensor classes.
`normalized_sum` follows from preservation of finite sums.

`dualScale_section` checks on the actual algebra maps that epsilon scaling
fixes the constant section. `forgetClass_smul` follows by quotient induction
from the definition of the actual scaling action. Together these facts show
in `normalized_smul` that normalized classes commute with actual epsilon
scaling pullback.

In `simultaneousClass_weighted`, pullback distributes over the product
defining the simultaneous ordinary class. The composite of an included
axis with the weighted map is the actual epsilon-scaling arrow with
coefficient `c i`, by `FiniteTangents.includeAxis_weighted`. Thus the product
becomes the normalized class of the finite sum. Its constant-lift factor
cancels normalization. Finally `family_weighted` uses the underlying class
of the chosen actual family and the injectivity of ordinary forgetting at
dual-number targets to obtain equality of pointed classes.

The derivation uses only the actual bundle-class, Artinian-test and
dual-number comparison interfaces imported by Lean. It assumes no external
representability theorem. Choosing a finite tangent basis for a proper
scheme, higher-order compatible families, a formal hull, algebraization
and a smooth atlas remain further obligations.

# Ordinary affine roots detected by actual quotient-root exclusion

This derived certificate works at arbitrary universe over a local domain with
specified fraction field. It uses supplied apartment data, a relative-component
model, a compatible split integral torus, and actual special-fibre quotient data.
The original torus map is a monomorphism and the generic group is affine, as
required by the apartment data.

Let `ψ` have relative-root derivative `a`. Assume that the entire depth group
`U_ψ` consists of integral points, and that every integral section whose generic
point lies in the strict group `U_(ψ+)` maps to the identity under the actual
reduction to the quotient. If an integral section has generic point in `U_ψ`
and its quotient image lies outside the intrinsic root group for
`2 • T.characterSpecialization hT a`, then `ψ` is an ordinary affine root.
`mem_affineRoots_of_quotient_exclusion` proves this claim;
`ordinaryRootOfQuotientExclusion` packages the original functional as an element
of the ordinary affine-root set. Its coercion lemma retains exactly `ψ`.

The proof uses the existing definition of an ordinary affine root. A forbidden
containment would factor the section's generic point as `v * w`, with `v` in
the strict group and `w` in the doubled-root group. Strict depth is contained in
depth, so the whole-depth integrality premise gives an integral section `y`
with generic point `v`. The section `y⁻¹ * x` is then automatically integral,
with generic point `w`; no additional doubled-factor integrality premise is used.
`IntegralRootReduction.quotient_reduction_mem_rootFunctor` places its quotient
image in the specialized doubled root group. The strict-depth premise kills
the image of `y`, so this is also the quotient image of `x`, a contradiction.
When the doubled character is not a generic root, the doubled group is trivial;
then `x` itself is at strict depth and gives the same contradiction.

The argument composes named Library subgroup and apartment interfaces with the
derived integral-root reduction construction. It does not assume that the
supplied quotient is reductive, nor does it require Henselian or algebraically
closed residue-field hypotheses. The strict-depth vanishing and whole-depth
integrality are explicit premises; this certificate proves neither of them.
It makes no unconditional facet-survival or final derivative-root-datum claim.

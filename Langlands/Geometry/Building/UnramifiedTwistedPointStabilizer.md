# Twisted conjugation on the actual unramified point stabilizer

This internal construction specializes `SemilinearCocycleStabilizer` to
the actual inertia fixed field `K = inertiaFixedField F` of a
nonarchimedean local field `F` and the rational points of the actual
scalar extension of a group scheme `G/F`. The field and schemes are at
arbitrary universe `u`. The cocycle `c` satisfies
`c (σ * τ) = c σ * rationalConjugate F K G σ (c τ)`.

`twistedRationalConjugateAction` is a group homomorphism into the
automorphisms of `G(K)`. Its value at `σ` is exactly
`g ↦ c σ * rationalConjugate F K G σ g * (c σ)⁻¹`.
The construction applies the generic twisted conjugation action to the
published `rationalConjugateAction`.

`twistedRationalConjugate_mem_characterValuationKernel_iff` proves
preservation and reflection of the actual character-valuation kernel
for `MaximalUnramified.valuation F`. The published character transport
theorem and `MaximalUnramified.valuation_galois` give its coefficient
stability. Normality of this kernel then supplies stability under the
inner twist. No assumption on the values or finite-level behavior of
`c` is required.

For supplied `MaximalUnramified.BuildingData B` and
`SemilinearApartmentData A`, `twistedAction_smul` identifies the
compatibility with the already constructed twisted permutations of the
same reduced building. The supplied building retains its existing
affineness assumptions.

`twistedConjugation_mem_oneStabilizer_iff` transports
`B.oneStabilizer y`, the intersection of the actual character-valuation
kernel and the actual point fixer, to the subgroup at the twisted
point. Its proof rewrites membership as kernel membership and fixation,
uses the kernel comparison, and uses injectivity of the twisted
building permutation.

When every twisted permutation fixes `y`,
`twistedOneStabilizerAction` restricts the twisted group automorphisms
to `B.oneStabilizer y`. Its inverse is induced by the inverse coefficient
automorphism, through the generic restriction construction. The
evaluation lemma gives the exact displayed rational-point formula.

The provenance is derived internal content from the imported
group-action and character-valuation APIs. The module constructs no
integral model, neutral parahoric, or residue quotient, and proves no
chamber-kernel or chamber-transitivity assertion.

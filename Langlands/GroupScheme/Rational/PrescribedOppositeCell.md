# Dynamic translated cells from a prescribed opposite factor pair

This internal supporting construction extends the Library's
`rootPoint_translatedCell_of_reflection` comparison to a prescribed opposite
factor pair and to actual dynamic subgroup coordinates. It retains arbitrary
universe `u`.

Let `k` be any field, `G` an affine group scheme over `k`, and
`i : T.toGrp → G` a scheme-monic morphism from a split torus. Assume the
actual relative Weyl quotient and root span satisfy `HasRelativeRootSystem i`.
Let `a` be an actual relative root and `x ≠ 1` a rational point of the
intrinsic subgroup `U_a`. Supply an actual pair `p = (p₁,p₂)` satisfying
`IsOppositeFactorPair i a x p`: both factors lie in `U_{-a}` and
`nₚ = p₁ x p₂` normalizes the torus. Also supply a fixed rational normalizer
`n` whose actual relative Weyl class satisfies `IsRelativeReflection i a`.

`IsOppositeFactorPair.normalizerRatio_mem_centralizerPoints` proves that
`c = nₚ n⁻¹` belongs to the whole-torus centralizer `centralizerPoints i`.
The prescribed pair's normalizer represents the same root reflection as `n`.
Uniqueness of that reflection under `HasRelativeRootSystem i` equates their
actual quotient classes, so their ratio belongs to the centralizer.

For any cocharacter `ν` with positive integral pairing `⟨a,ν⟩`,
`IsOppositeFactorPair.translatedCellFactorPair` returns the actual coordinate
pair

`(p₁⁻¹, c (n p₂⁻¹ n⁻¹))`.

Its subtype property proves that the first coordinate belongs to the dynamic
unipotent subgroup of the opposite of `ν` composed with `i`, the second belongs
to the dynamic parabolic of `ν` composed with `i`, and their product equals
`x n⁻¹`. Both coordinates are given by these formulas; the construction
chooses no new pair or normalizer.

For the first membership, inversion preserves `U_{-a}`, and positivity of
`⟨-a,-ν⟩` places that subgroup in the opposite dynamic unipotent. For the
second, `n` negates the actual character `a`, so conjugating `p₂⁻¹` puts it
in `U_a`, hence in the dynamic unipotent and parabolic of `ν`. Every point
centralizing the whole torus belongs to that same dynamic parabolic.
Multiplication gives the second membership; the displayed factorization
follows by the group laws.

The provenance is internal composition of the published opposite-pair
reflection theorem, uniqueness of the actual relative reflection, normalizer
conjugation of root subgroups, positive-pairing dynamic containment, and
whole-torus centralizer containment in dynamic parabolics. No rank-one
factorization existence, root-support condition, genericity of `ν`, perfection,
reductivity, or maximality hypothesis is added. The result assumes the
prescribed pair and fixed normalizer; it does not construct integral cell
coordinates or prove integral opposite factors or the unramified facet root
datum.

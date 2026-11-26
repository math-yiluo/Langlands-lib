# Geometric compact-support étale cohomological dimension

## Sources

Vladimir Berkovich, *Étale cohomology for non-Archimedean analytic spaces*,
Publ. Math. IHÉS 78 (1993), Corollary 5.3.8 and its proof, printed
pp. 104–105 (PDF pp. 101–102). Registered ID
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The definition of analytic dimension and its computation on an affinoid
net are at the end of §1.2, printed p. 23 (PDF p. 20).
[Original article](http://www.numdam.org/item?id=PMIHES_1993__78__5_0)

The affinoid definition is in Vladimir Berkovich, *Spectral theory and
analytic geometry over non-Archimedean fields* (1990), §2.3, printed
p. 34 (PDF p. 48). Registered ID
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA-256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
The definition takes Krull dimension after a radius field extension
making the affinoid algebra strict. For a strictly affinoid algebra
one may take the original field, so its ordinary Krull dimension applies.

Michael Harris, *Galois properties of cohomological automorphic forms on
GL(n)*, J. Math. Kyoto Univ. 39 (1999), §2, Fact 2 and the following
sentence on printed p. 303 (PDF p. 5), cites Corollary 5.3.8 for the
bound used on his geometric analytic domains and étale spaces over
those domains. Registered ID
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

## Lean statement

`Langlands.Cohomology.HasStrictAffinoidDimensionBound X d` uses the
Library's saturated presentation of `X`. It requires the chart ranges
admitting a bounded isomorphism with a radius-one algebra
`PresentedAffinoidAlgebra.ofStrict K P` of Krull dimension at most `d`
to form a net. `Ring.KrullDimLE d P` measures the maximum length of
chains of prime ideals of `P`. This gives an upper bound of `d` for
the supremum of the chart dimensions in Berkovich's §1.2. The strict
chart requirement is essential for using this Krull dimension in the
formula. A nonstrict affinoid field can have Krull dimension zero and
positive analytic dimension, as in Berkovich 1990, p. 34.

`Langlands.Cohomology.AnalyticEtaleCompactDimensionStatement` states
the absolute geometric case of Corollary 5.3.8 over a complete,
nontrivially normed, algebraically closed ultrametric field `K`.
The space `X` is Hausdorff and has the strict chart dimension bound `d`.
For every positive integer `N`, every sheaf `F` of `ℤ/Nℤ`-modules on the
analytic étale site, and every `q > 2 * d`, the actual
`etaleCompactCohomology` vanishes. The coefficient ring is
`ULift (ZMod N)` in the module universe. The statement covers, in
particular, `N = ℓ^m`. Here bounded torsion is sufficient, so no
restriction on `N` relative to the residue characteristic is imposed.

Compact support uses the Library's `L`-valued points for a normed
extension `L`, with point axioms and surjectivity of `pointProjection L X`.
These are the same support conditions as in the Library's étale
compact-support comparison. Berkovich's Corollary 5.3.8 treats relative
higher direct images with proper support of arbitrary torsion sheaves.
Its proof first reduces to this geometric absolute bound, using the
ordinary étale site and taking the morphism to the analytic point. The
proposition uses the bounded torsion specialization and the Library's
module-valued cohomology. Applying it to Harris's Fact 2 would also
require the dimension bound for his particular geometric domains and
their étale test objects. The statement does not assert bounds for those
tower spaces, or the relative direct-image comparison.

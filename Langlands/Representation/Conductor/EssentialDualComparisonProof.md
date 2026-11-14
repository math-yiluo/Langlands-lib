# The JPSS (5.3) dual comparison of essential vectors: proof

Author: Worker 5548.

`essentialDualComparison` proves exactly the published proposition
`Langlands.Conductor.EssentialDualComparisonStatement.{uF,uV}`. The field and
representation-space universes remain independent. Every nonarchimedean local field is
included, in any characteristic. The target statement, its paired Markdown, and its imports
are unchanged.

## Statement proved

This is Jacquet, Piatetski-Shapiro and Shalika, *Conducteur des représentations du groupe
linéaire*, Math. Ann. 256 (1981), (5.3), printed page 213. The essential vectors are the
corrected ones of Jacquet 2012, Theorem 1. The rank is `r = n + 2`. Fix Jacquet's
normalizations `h` for `ψ` and `h'` for `ψ.scale (-1)`, and `ν` self-dual for `ψ`. Let `π`
be generic and `ℓ` a nonzero Whittaker functional, and let `w` be an essential vector of the
model of `ℓ`. Let `ℓ'` be the functional of the inverse-transpose pullback with
`ℓ'.val = (dualFunctional ψ π ℓ).val`, and `w'` an essential vector of its model. Let
`c q^(-ms)` be the epsilon factor of `π` against the trivial character of `GL_1`. Then some
constant `C` satisfies `W̃(g) = C · w'(g · diag(ϖ^m, ..., ϖ^m, 1))` for every `g`.

## Implemented proof

The proof applies one published implication to two published theorems:

- `essentialDualComparison_of_functionalEquation` (module
  `Langlands.Representation.Conductor.EssentialDualComparisonBridge`) takes the
  propositions `SphericalCorankOneFunctionalEquationStatement.{uF,uV}` and
  `Langlands.Whittaker.MirabolicRestrictionInjectivityStatement.{uF,uV}` to
  `EssentialDualComparisonStatement.{uF,uV}`.
- `sphericalCorankOneFunctionalEquation` (module
  `Langlands.Representation.Conductor.SphericalCorankOneFunctionalEquationProof`) proves
  the first input. This is JPSS 1981, (4.2), display (3): the functional equation of the
  corank-one integrals against unitary spherical Whittaker functions, over every
  nonarchimedean local field.
- `Langlands.Whittaker.mirabolicRestrictionInjectivity` (module
  `Langlands.Representation.Whittaker.MirabolicRestrictionInjectivityProof`) proves the
  second input. This is the injective half of Jacquet and Shalika 1981, Section (1.1):
  restriction of the Whittaker model to the mirabolic subgroup is injective.

The two theorems are used at the same universes `uF` and `uV` as the target. No premise
remains. In particular, neither input is kept as a hypothesis.

## The route inside the bridge

This section summarizes the published modules; nothing here is new. The bridge follows
the first paragraph of the source's proof of (5.3). Let `v` be the vector whose
`ℓ`-coefficient is `w`. For each unitary parameter `x`, the bridge applies the functional
equation to `v` at `x⁻¹`. With the essential identities of `w` and of `w'`, this shows that
two families of corank-one integrals against the unitary spherical function at `x` are
proportional: those of `W̃` and those of the translate
`W₁(g) = w'(g · diag(ϖ^m, ..., ϖ^m, 1))`. The constant is the explicit
`essentialDualConstant q n c m`, which depends on neither `x` nor `s`.

The published reduction `dualComparison_of_unit_spherical_integrals` (module
`EssentialDualComparisonReduction`) then finishes the argument. The vector `W̃ - C · W₁`
is invariant on its restriction, and all its integrals against the unitary spherical
functions vanish. Unitary separation makes its mirabolic restriction zero, and mirabolic
restriction injectivity, for the inverse-transpose pullback, makes it zero on all of
`GL_(n+2)(F)`. The bridge supplies injectivity for `π` and for its pullback from the
second input, since the pullback is generic (`isGeneric_inverseTransposePullback`).

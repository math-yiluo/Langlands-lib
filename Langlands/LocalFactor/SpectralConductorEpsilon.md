# The epsilon side of Tate's spectral conductor formula

Worker 4803 wrote this supporting module for the reduction
`SpectralConductor.spectralConductorRankOneReduction`
(module `Langlands.LocalFactor.SpectralConductorReduction`). Its declarations
concern a supplied local-constant system `ε` with `NonabelianSystem.IsSystem F e ε`,
an intermediate field `E` of the common closure, a fixed additive character `ψ`,
a Haar measure `μ` and a complex number `s`. They prove nothing about conductors
of representations. Conductors enter only through an abstract additive map `a`.

## Notation

- `logCardinality E` is `log q_E`, the complex logarithm of the residue cardinality
  of the canonical data on `E`.
- `characterConductor e E χ` is the multiplicative conductor (Tate's `a(χ)`, the least
  unit level on which the character is trivial) of the field character
  `fieldCharacterEquiv F e E χ` attached to a continuous Weil character `χ` by the
  supplied reciprocity component `e E`.

## Declarations and proofs

- `value_virtualTwist_characterClass`: the rank-one spectral formula
  `ε(ω_s χ) = ε(χ) · exp(-s (n(ψ) + a(χ)) log q_E)`. Proof: `ω_s χ` is again a
  character class (`continuousTwist_characterClass`). The Library's
  `value_characterClass` identifies both values with the abelian epsilon expression of
  the transported field character. `fieldCharacterEquiv_isAbsTwist` shows the
  transported twist is an absolute-value twist, and
  `abelianEpsilonExpression_of_isAbsTwist` gives the exponential factor with exponent
  `twistExponent = n(ψ) + a(χ)`. All three lemmas are from
  `CommonClosureRankOneSpectral`.
- `value_sub`: additivity as `ε(x - y) = ε(x) ε(y)^{-1}`.
- `value_virtualTwist_induce`: for an induced difference `Ind_L(χ - χ')` from a larger
  field `L`, the twisted value is the untwisted value times
  `exp(-s (a(χ) - a(χ')) log q_L)`. Proof: twisting commutes with induction
  (`virtualTwist_induce`). The difference and its twists have degree zero, so the
  system's `InductionRelation` moves both values to `L` with the trace character
  `ψ_L` and any Haar measure on `L`. There `value_sub` and the rank-one formula for `χ`
  and `χ'` give the factor. The additive conductor `n(ψ_L)` occurs in both rank-one
  exponents and cancels, so it is never compared with `n(ψ)`.
- `characterConductor_one`: the trivial Weil character has conductor `0`. Its field
  character is trivial on every unit, because reciprocity is surjective
  (`reciprocityUnits_surjective`) and `weilCharacter_fieldCharacterEquiv`.
- `spectralExponent E ψ a` is the additive map `x ↦ a(x) + n(ψ) · deg x · log q_E`.
  `formulaSubgroup` is the additive subgroup of classes with
  `ε(ω_s x) = ε(x) · exp(-s · spectralExponent(x))`. Closure under sums and negatives
  follows from additivity of `ε`, of `virtualTwist`, of `a` and of the degree.
- `induce_mem_formulaSubgroup`: an induced character difference lies in the subgroup
  when `a(Ind_L(χ - χ')) = (a(χ) - a(χ')) log q_L`. Its degree is zero
  (`degree_induce`).
- `one_mem_formulaSubgroup`: the trivial character lies in the subgroup when `a`
  vanishes on it (rank-one formula with `characterConductor_one`).
- `exists_finset_generators`: for every class `x`, `x - deg x · 1` lies in the integral
  span of finitely many generators `Ind_L(χ - χ')`. Proof: degree-zero generation
  (`CommonClosureDegreeZeroGeneration`, proved in the Library as
  `commonClosureDegreeZeroGeneration`), then `Submodule.mem_span_finite_of_mem_span`.
- `mem_formulaSubgroup_of_span`: if finitely many generators spanning `x - deg x · 1`
  lie in the subgroup, and so does the trivial character, then so does `x`.

## Sources

This is the argument of Tate, *Number theoretic background* (1979), §3.4: the
formulas (3.4.2)–(3.4.8) follow from the rank-one case "via inductivity in degree 0".
It is also the argument of Deligne (1973), §5. The finite-generator form is needed
because the conductor functional of the reduction depends on a finite Galois
subfield chosen after the generators.

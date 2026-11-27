# Standard presentations of a parabolic family and twisted intertwining integrals

Module `Langlands.Global.AdelicStandardFamilyPresentation` contains three small declarations
for a standard parabolic family `fam` (`StandardParabolicFamily`, module
`Langlands.Global.AdelicLeadingCuspidalComponents`).

- `standardPresentation J` is the root presentation `⟨⟨T, i, ν, J, f J⟩, isCompatible J⟩` of the
  standard parabolic `P_J`. It is the presentation used by the published
  `ConvergentCuspidalTestExpansionStatement` for its regularity predicate.
- `isSplitTorus_splitComponent J` and `isSplitTorus_torus` are the split-torus witnesses of the
  split component `A_J` and of the maximal split torus `T` of the family.
- `intertwiningIntegral_eq_parameterTwist`: for standard `P_I`, `P_Q`, an Iwasawa compact `K`
  of both, a Weyl point `w` and a Levi conjugation `c` with projection `proj`, the intertwining
  integral `∫ φ_λ(w⁻¹ v g) dv` (`IsIwasawaCompact.intertwiningIntegral`) is the twist at
  `wλ = weylParameter (l I) c proj λ` (`IsIwasawaCompact.parameterTwist`) of the intertwining
  operator `M(w, λ)φ` (`IsIwasawaCompact.intertwiningOperator`). The operator is the integral
  multiplied by the height factor at `-wλ`. Multiplying by the height factor at `wλ` cancels it,
  since the two factors are `exp(∓⟨wλ, H_Q(g)⟩)`.

This is the normalization of the intertwining operator in J. Bernstein and E. Lapid, *On the
meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), §2.2, p. 191,
registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`.

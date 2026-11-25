# The arithmetic Hecke Euler family of a pair of relative Weil representations

Supporting module for the proof of `AssociatedGammaStatement` (module
`Langlands.Automorphic.AssociatedGammaArithmeticFamily`, namespace
`Langlands.ClassFieldTheory.Global.RelativeWeilGroup`). It builds the arithmetic side `A` of the
two-twist comparison engine used for `AssociatedGammaStatement` (Henniart 2000, Théorème
2.3), from the proved global equation `relativeWeilTwistFunctionalEquation : 
RelativeWeilTwistFunctionalEquationStatement` (Tate 1979, Theorem 3.5.3).

## Data

`ArithmeticTwistSetup ψ S S'` bundles continuity of `S`, `S'` and, at every finite place `z`,
a place of `E` above `z`, a reciprocity candidate and a local relative Weil map, the canonical
additive component of `ψ`, a common-closure reciprocity family and a local-constant system.

## Local factors

- `IsLocalTwistFactors z η f`: `f` is a factor triple (`IsArithmeticPairLocalFactors`) at `z`
  of the twisted pair for some global character `χ'` with `χ'_z = η`.
- `finiteFactors χ z`: a choice (`Classical.epsilon`) of such `f` for `η = χ_z`; it depends on
  `χ` only through `χ_z` (`localFactors_inr_of_finiteComponent_eq`).
- `localFactors arch χ`: the archimedean block `arch` and the finite factors; the archimedean
  factors do not depend on `χ` (`localFactors_inl`).

## Results

- `finiteFactors_spec`: assuming `ArithmeticPairEpsilonExistenceStatement`, the chosen
  factors are arithmetic local factors of the twist by `χ` itself: existence comes from
  `exists_isArithmeticPairLocalFactors`, and the classes for the chosen `χ'` equal those for
  `χ` because the reciprocity characters agree along `ι_z`.
- `isTwistedRelativePairFactorsAt`: the factor hypothesis of the global equation holds at
  every place.
- `exists_engineInputs`: there are `T₀` and an archimedean block such that for every
  finite-order `χ` trivial at infinity and every `B ⊇ T₀` outside which `χ` is unramified,
  `HasEngineInputs (localFactors arch χ) B` holds, directly from the proved global equation.

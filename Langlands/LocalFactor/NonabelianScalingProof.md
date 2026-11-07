# Additive-character scaling for actual exact virtual local constants

`Langlands.LocalFactor.NonabelianSystem.additiveCharacterScaling` proves the
unchanged published proposition
`Langlands.LocalFactor.NonabelianSystem.AdditiveCharacterScalingStatement.{uF,uV}`.
The field universe `uF` and representation universe `uV` remain independent.
For every prime, finite p-adic field `F`, supplied reciprocity family `e` and
assignment `ε` satisfying the existing `IsSystem F e ε`, the theorem gives,
for every actual finite intermediate field `E`,

```
ε(E, ψ(a·), μ, x)
  = det(x)(w) · |a|_E^(-degree(x)) · ε(E, ψ, μ, x).
```

Here `ψ` is any of the specified nontrivial unitary additive characters,
`μ` is any regular additive Haar measure, `a` is any field unit, and `w` is
any element of the actual Weil subgroup satisfying
`reciprocityUnits F e E w = a`. The equality holds in `ℂ` for every class
`x` in the continuous exact virtual group, whose representation carriers
have universe `max uF uV`. It evaluates the existing exact determinant
character at `w` and uses the existing normalized absolute value of `E`.
The same measure appears on both sides, and the exponent is the negative
integer degree, including zero and negative virtual dimensions.

The implemented proof applies the published
`additiveCharacterScaling_of_generation_gallagher` and discharges both of
its explicit prerequisites with published theorems:

- `Langlands.LocalFactor.commonClosureDegreeZeroGeneration.{uF,uV}` proves
  degree-zero generation in the actual continuous exact group by inductions
  of differences of continuous character lines from nested intermediate fields.
- `Langlands.LocalFactor.Inductive.gallagherDeterminant.{0,uF,max uF uV}`
  proves the determinant-transfer formula for the actual finite-index
  induced representations at the universes required by the reduction.

The reduction compares the scaled assignment with the product of its
original value, determinant and absolute-value correction. Rank-one scaling
proves equality on character classes. Trace compatibility, the system's
degree-zero induction law and determinant transfer prove equality on the
induced differences. Generation extends this to the degree-zero kernel.
Subtracting `degree(x)` times the trivial character class reduces an arbitrary
exact virtual class to that kernel and gives the full formula.

This module is an internal composition of those proved Library results.
Its source correspondence is Deligne (1973), formula (5.4), as documented
in the unchanged statement pair and the scaling reduction. It introduces
no generation, Gallagher, scaling or existence premise. The original
`IsSystem` and Weil-lift equality conditions remain exactly those of the
published target; neither the target pair nor its imported pairs is edited.

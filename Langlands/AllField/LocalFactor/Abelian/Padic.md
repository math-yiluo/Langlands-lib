# All-field port of `Langlands.LocalFactor.Abelian.Padic`

`Langlands.AllField.LocalFactor.Abelian.Padic` is the all-field port of the Library module `Langlands.LocalFactor.Abelian.Padic`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.LocalFactor.Abelian.Padic` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Callable rank-one local-factor expressions**

Concrete expressions for the abelian theorem family, using the actual
conductors constructed by `Langlands.HarmonicAnalysis.Conductor`.
No functional equation or nonabelian constant system is assumed or chosen.

Worker 33 authored the callable expressions and conductor bridges. Worker 20
connects them to the convergent abelian construction and supplies rational
L-factors with restricted evaluation.

## Imports from the port

- `Langlands.AllField.LocalFactor.Abelian.Definitions`

## Declarations

- `Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar` (def): Actual Haar measures satisfying the intrinsic Fourier self-duality predicate.
  This subtype does not assert that such a measure exists.

Public declarations of the original that are not re-declared here: `Langlands.LocalFactor.PadicAbelian.BorelMeasure`, `Langlands.LocalFactor.PadicAbelian.integerRing`, `Langlands.LocalFactor.PadicAbelian.integralUnits`, `Langlands.LocalFactor.PadicAbelian.spectralVariable`, `Langlands.LocalFactor.PadicAbelian.characterExtension`, `Langlands.LocalFactor.PadicAbelian.unitLevel`, `Langlands.LocalFactor.PadicAbelian.unitLevel_iff_mem_principalUnits`, `Langlands.LocalFactor.PadicAbelian.ConductorAt`, `Langlands.LocalFactor.PadicAbelian.conductorAt_iff`, `Langlands.LocalFactor.PadicAbelian.AdditiveConductorAt`, `Langlands.LocalFactor.PadicAbelian.additiveConductorAt_iff`, `Langlands.LocalFactor.PadicAbelian.lFactorAt`, `Langlands.LocalFactor.PadicAbelian.RegularPoint`, `Langlands.LocalFactor.PadicAbelian.ConvergesAt`, `Langlands.LocalFactor.PadicAbelian.zetaIntegrand`, `Langlands.LocalFactor.PadicAbelian.zeta`, `Langlands.LocalFactor.PadicAbelian.ExtendsIntegral`, `Langlands.LocalFactor.PadicAbelian.laurentEvaluation`, `Langlands.LocalFactor.PadicAbelian.gaussIntegrand`, `Langlands.LocalFactor.PadicAbelian.gaussShell`, `Langlands.LocalFactor.PadicAbelian.epsilonAt`, `Langlands.LocalFactor.PadicAbelian.lFactor`, `Langlands.LocalFactor.PadicAbelian.epsilon`, `Langlands.LocalFactor.PadicAbelian.deligneConstant`, `Langlands.LocalFactor.PadicAbelian.centeredConstant`, `Langlands.LocalFactor.PadicAbelian.lPolynomial`, `Langlands.LocalFactor.PadicAbelian.lPolynomial_coeff_zero`, `Langlands.LocalFactor.PadicAbelian.lPolynomial_ne_zero`, `Langlands.LocalFactor.PadicAbelian.rationalLFactor`, `Langlands.LocalFactor.PadicAbelian.rationalLFactor_ne_zero`, `Langlands.LocalFactor.PadicAbelian.rationalLFactor_mul_denominator`, `Langlands.LocalFactor.PadicAbelian.regularPoint_iff_polynomial_ne_zero`, `Langlands.LocalFactor.PadicAbelian.regularLValue`, `Langlands.LocalFactor.PadicAbelian.coe_regularLValue`, `Langlands.LocalFactor.PadicAbelian.characterExtension_eq_extendZero`, `Langlands.LocalFactor.PadicAbelian.integerRing_eq`, `Langlands.LocalFactor.PadicAbelian.gaussShell_eq_valuationShell`, `Langlands.LocalFactor.PadicAbelian.gaussIntegrand_zero`, `Langlands.LocalFactor.PadicAbelian.normalizedAbs_on_gaussShell`, `Langlands.LocalFactor.PadicAbelian.gaussIntegrand_on_shell`, `Langlands.LocalFactor.PadicAbelian.gaussIntegrand_integrable`, `Langlands.LocalFactor.PadicAbelian.deligneConstant_eq_abelianEpsilonExpression`, `Langlands.LocalFactor.PadicAbelian.langlandsConstantAtSelfDual`, `Langlands.LocalFactor.PadicAbelian.langlandsEpsilonAtSelfDual`, `Langlands.LocalFactor.PadicAbelian.langlandsEpsilonAtSelfDual_half`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

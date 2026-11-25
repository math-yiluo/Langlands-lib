# Local dimension of a finite type affine scheme

Module `StacksFrontier.RingTheory.Spectrum.Prime.LocalDimension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For an affine scheme of finite type over a field, local dimension can be read from irreducible components, heights of closed specializations, or the height and residue field of the point itself.

## Results

- `PrimeSpectrum.localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height` identifies the local dimension at x with both the largest dimension of an irreducible component containing x and the least height of a maximal ideal containing `x.asIdeal`. `Stacks.Spectrum.LocalDimension.solution` proves the pair of identities.
- `PrimeSpectrum.localKrullDim_eq_height_add_trdeg_residueField`, via `Stacks.Spectrum.LocalDimensionFormula.solution`, computes the same dimension as the height of `x.asIdeal` plus the transcendence degree of its residue field over the base field. Both theorems take a finite type k-algebra S over a field k and any point x of `PrimeSpectrum S`.
- `Stacks.Spectrum.LocalDimensionFormula.ringKrullDim_eq_height_add_ringKrullDim_quotient` gives the dimension of a finite type domain T over k as the height of a prime q plus the dimension of T/q. The accompanying order-theoretic lemmas construct saturated chains realizing finite heights and transport them across quotient maps.

## Proof

The first theorem compares all three descriptions with the largest coheight of a minimal prime below x. The Jacobson property provides closed specializations in each neighbourhood, while removing the finitely many components missing x bounds prime chains in a suitable open neighbourhood. For the formula, concatenating saturated chains through a prime gives the domain dimension formula and a height inequality along quotient maps by prime ideals of Noetherian rings. Applied to component quotients and maximal ideals above x, these give the two bounds by height plus transcendence degree.

## Scope

`TopologicalSpace.localKrullDim` takes the infimum of dimensions of open neighbourhoods. The height term alone is the dimension of the local ring, and at a closed point the transcendence degree vanishes. The extrema are expressed as `iSup` and `iInf` in `WithBot ℕ∞`. The finite transcendence degree is converted using `Cardinal.toENat`.

## References

Tag 00OT for the three descriptions and Tag 00P1 for the formula. Tag 0055 defines local dimension, Tag 00OS compares maximal chains and heights in finite type domains, and Tag 00P0 gives dimension as transcendence degree. The comparison references are EGA 0 16.1.1, EGA 0 16.1.4, EGA IV 5.1.1, EGA IV 17.15.8 and SGA 4 IV 4.2.2.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00OT](https://stacks.math.columbia.edu/tag/00OT) | `localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height` | `dim_x X` is `TopologicalSpace.localKrullDim`, Topology Definition 0055 (4); `dim(S_𝔪)` is `𝔪.height`; the components are `irreducibleComponents` and their dimension is `topologicalKrullDim`, and the source's `max`/`min` are `iSup`/`iInf` in `WithBot ℕ∞`. See the module docstring. |
| [00P1](https://stacks.math.columbia.edu/tag/00P1) | `localKrullDim_eq_height_add_trdeg_residueField` | `dim_x X` is `TopologicalSpace.localKrullDim`, Definition 0055 (4); `dim(S_𝔭)` is `𝔭.height`, `κ(𝔭)` is `Ideal.ResidueField`, and the transcendence degree is compared through `Cardinal.toENat`. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 16.1.1 | `subtypeEquivIrreducibleCloseds` | more general |
| SGA | 4 IV 4.2.2 | `subtypeEquivIrreducibleCloseds` | special case |
| EGA | IV 5.1.1 | `topologicalKrullDim_eq_krullDim` | more general |
| EGA | IV 5.1.1 | `topologicalKrullDim_zeroLocus` | 5.1.1.2 for prime ideals |
| EGA | 0 16.1.4 | `ringKrullDim_eq_height_add_ringKrullDim_quotient` | special case |
| EGA | IV 17.15.8 | `localKrullDim_eq_height_add_trdeg_residueField` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Spectrum/Prime/LocalDimension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 32 declarations of the source file 31 are kept. The 1 left out are not needed by the results for which the extract is made: `Stacks.Spectrum.LocalDimensionFormula.ringKrullDim_quotient_add_eq_ringKrullDim`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 6 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.

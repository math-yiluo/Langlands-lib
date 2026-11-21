# The local input for Fourier detection on a proper Levi

`RationalSemistandardLeviFourierData` packages the data for the outer
Levi in VIII.2.1. It uses a closed connected reductive model of the literal
Levi, a maximal split torus and Schwartz data for that model. The `xi_eq`
and `height_eq` fields identify the weights across the rational-point
homeomorphism, with the ambient matrix representation restricted to the model.
`constantTerm f g` is the actual normalized induced constant term \(f^M\)
at the translating pair \(g=(g_1,g_2)\), pulled back along that homeomorphism.
`fourier` is the actual full semistandard Fourier transform on the model.

## Comparisons used

| Declaration or field | Role in VIII.2.1 |
| --- | --- |
| `rank_lt` | `semistandardProperLeviRank` gives strict decrease of `relativeRootRank` for every proper outer index and the chosen maximal split torus of its model. |
| `coverage` and `conjugationModulus` | `RationalSemistandardNestedFourierCoverage` matches every inner semistandard Fourier component with an ambient proper component. It retains VII.1.2 on both groups, the III.6 diagram with its measures and two factors \(\delta_P(m_j)^{-1/2}\), and the common final-Levi measures and formal degrees. |
| `fourier_constantTerm_eq_zero` | `rationalSemistandardLeviFourierVanishing` applies the nested comparison to `constantTerm f g`. Its ambient Fourier parameters are those of the cutoff. |
| `constantTerm_eq_zero_iff` | `rationalSemistandardLeviConstantTerm_eq_zero_iff` transports zero back to the induced constant term on the literal Levi at the one `radicalHaar` supplied for all translating pairs. |
| `rationalCuspidal_of_properLeviConstantTerms_eq_zero` | `rationalSemistandardCuspidalFromConstantTermHaar` uses uniqueness of Haar and the intrinsic semistandard comparison to reach the existing `rationalCuspidalSubmodule`. |

`rationalSemistandardProperFourier_eq_zero_iff_mem_cuspidal` combines
these comparisons with `rationalSemistandardCuspidalProperFourierVanishing`.
In the direction from zero cutoff to intrinsic cuspidality, it applies
`hreconstructZero` to `constantTerm f g` at the rank inequality from `rank_lt`.
This input is the zero case of the local reconstruction formula VIII.1 (2)
on each actual strictly smaller Levi. Full reconstruction and its rank
restriction belong to the subsequent adapter to Task 7276. The zero-case
reduction is independent of the finiteness premise used to construct the
smooth proper cutoff. The opposite implication uses VII.1.2 and the fixed
radical Haar for each proper Fourier component.

The structural inputs are the closed connected reductive Levi model,
its maximal split torus, generic cocharacter, Iwasawa data and split centres.
The weight and translation estimates, temperedness and nested Fourier
coverage, and the zero case of reconstruction remain explicit. The declarations
apply over arbitrary nonarchimedean local fields with finite residue field,
with canonical rational-point topology, complex smooth representations and
independent universes `u` and `uV`. In rank zero, strict decrease makes
the proper-Levi comparison vacuous.

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d’après Harish-Chandra)*, Journal of the Institute of Mathematics of
Jussieu 2 (2003), VIII.2.1, printed pp. 321–322 (PDF pp. 87–88).
The package and the transport of zero through it are derived adapters
for the calculation on \(f^M\) in that proof. Registered source
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
[Waldspurger 2003](https://doi.org/10.1017/S1474748003000082)

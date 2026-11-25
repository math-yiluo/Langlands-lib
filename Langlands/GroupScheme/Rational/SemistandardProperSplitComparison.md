# The proper/group split under semistandard Levi comparisons

This structural module isolates preservation of the group and proper parts of
the full semistandard index under the actual comparisons used in Fourier
covariance. It constructs neither a spectral carrier nor a projector.

## Provenance and scope

The motivating source is J.-L. Waldspurger, *La formule de Plancherel pour les
groupes p-adiques (d'après Harish-Chandra)* (2003), printed p.321 (PDF p.87),
the proper truncation in VIII.2 and its use of VII.1.4. Registered source
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
Setting the group components to zero preserves covariance only if the
comparisons preserve the group/proper split. The explicit structural
formulation and proof reductions in this module are derived interfaces.
The cited passage does not prove these general-field geometric comparisons.

All assertions here are about group schemes and their all-test subgroup
functors over arbitrary fields. There is no restriction on characteristic,
splitting, quasi-splitness or relative rank. No local-field topology,
representation universe, orbit measure or analytic finiteness premise occurs.

## Declarations and implemented proof route

Except for the first row, names below have prefix `Langlands.GroupScheme`.

| Declaration | Content and implementation |
| --- | --- |
| `Langlands.GroupScheme.SubgroupFunctor.IsRationallyConjugate.eq_top_iff` | Rationally conjugate all-test subgroup functors are simultaneously the whole group. Move the equality across the actual inner isomorphism and use `comap_top` in each direction. The lemma works over any scheme base. |
| `semistandardParabolic_eq_top_iff_levi_eq_top` | A semistandard index has `P = G` iff its literal Levi is `G`, conditional on the exact `SemistandardSpectralDynamicCoverageStatement`. Represent the intrinsic triple by a cocharacter in the original fixed torus, then apply the published `Dynamic.parabolic_eq_top_iff_centralizer_eq_top` to the connected reductive ambient group. |
| `SemistandardProperSplitComparisonStatement` | For a connected reductive group with its maximal split torus, rational conjugacy of the literal Levis of two full semistandard indices implies `P = G` iff `Q = G`. This is an exact Prop-valued structural comparison target. |
| `semistandardProperSplitComparison_of_dynamicCoverage` | Proves the comparison from the explicit dynamic-coverage target, by the preceding parabolic/Levi equivalence and conjugacy's preservation of the whole subgroup. |
| `semistandardParabolic_eq_top_iff_of_sameLevi`, `semistandardParabolic_ne_top_iff_of_sameLevi` | The group and proper parts are preserved between any two parabolics with the same literal Levi. Retain the exact split-comparison target; equality gives rational conjugacy by reflexivity. |
| `semistandardParabolic_eq_top_iff_of_weylConjugacy`, `semistandardParabolic_ne_top_iff_of_weylConjugacy` | Preservation under each element of `semistandardWeylConjugacySet` for the two actual Levis. The published transporter theorem supplies genuine rational conjugacy. |
| `semistandardParabolic_eq_top_iff_of_weylConjugacyQuotient`, `semistandardParabolic_ne_top_iff_of_weylConjugacyQuotient` | The same preservation for the genuine left target-Weyl quotient. Quotient induction reduces to the preceding transporter result. |

The Weyl comparisons retain the precise input
`torusCentralizer i ≤ p.levi` needed to define the published all-test Weyl
action. They use equality transporters. Inclusion transporters can take a
proper Levi into a larger one and do not imply preservation of this split.
No representative of the normalizer quotient is chosen or substituted for the
published transporter quotient.

## Dependency ledger and explicit inputs

The intrinsic semistandard index, its dynamic construction and the actual
Weyl equality transporters are public imports from the existing Library.
The dynamic parabolic/centralizer theorem and connected reductivity's
trivial-unipotent-radical consequence are published structural results.
`SemistandardSpectralDynamicCoverageStatement` remains an explicit
structural premise here. This module proves a reduction from it and does not assert
coverage unconditionally; the Library proves the coverage statement as
`semistandardSpectralDynamicCoverage`
(`Rational.SemistandardSpectralDynamicCoverageProof`). Downstream consumers can retain the precise
`SemistandardProperSplitComparisonStatement` instead of the stronger coverage
premise.

On an orbit representative change at a fixed semistandard parabolic, the
parabolic itself is unchanged, so its proper/group status is unchanged by
definition. Comparisons between parabolics with the same or Weyl-conjugate
literal Levi use the proved adapters above. The later actual Fourier
truncation must additionally consume the precise representative transports
and VII.1.4 covariance to obtain invariant smooth membership. Geometric split
preservation supplies none of those analytic assertions by itself.

No same-rank finiteness, Fourier support, synthesis reconstruction, inverse,
projection law, translation compatibility, symmetry or convolution assertion
is introduced as a premise or claimed as a conclusion.

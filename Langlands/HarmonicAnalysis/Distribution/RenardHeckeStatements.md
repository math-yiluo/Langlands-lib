# Hecke distributions, local units and compact-open corners

This statement unit covers the remaining distribution comparisons in Renard
II.3.12. It reuses the existing Haar `HeckeAlgebra μ`, its unital `Corner`, the
original distribution dual, `compactlySupported`, normalized compact-subgroup
Haar distributions and actual compact convolution. All groups are Hausdorff,
locally compact and totally disconnected. The ambient measure, where present,
is any Borel left Haar measure; unimodularity and countability are not assumed.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Locators: II.3.12 Lemma and change of notation, printed pp.51–52 / PDF pp.57–58;
compact-open membership paragraph, Proposition, following idempotent-order
remark, corner definition and Remark 1, printed p.52 / PDF p.58; Remark 2 and
its proof, printed p.53 / PDF p.59. The compact convolution and normalized
subgroup distributions come from II.3.10–II.3.11, printed pp.50–51 / PDF pp.56–57.

Declarations are in `Langlands.HarmonicAnalysis.Distribution.RenardHecke`.

- `DensityRealizationStatement` asserts injectivity of the actual
  `heckeDistribution μ` and equality of its range with `testDensity μ`'s range.
  The function Hecke carrier is already linearly equivalent to the test space;
  this statement records the precise faithful distribution realization needed
  for the source's change of notation.
- `NormalizedIndicatorStatement` equates the density of the existing normalized
  compact-open indicator with `compactSubgroupHaar K.toSubgroup hK`. This is
  the concrete ambient-measure/subgroup-measure comparison and, in particular,
  gives membership of that normalized subgroup distribution in `H(G)`.
- `LocalUnitsStatement` treats any finite family of compact distributions in
  this actual Hecke range. An actual compact open subgroup, contained in any
  prescribed open subgroup, gives both convolution identities for every family
  member. The refinement clause is the standard strengthening already present
  in the published function-valued finite-family local-unit theorem; it also
  supplies the filtered family by refining two subgroups via their intersection.
  Idempotence is stated for all compact subgroups in the II.3.11 unit.
- `IdempotentOrderStatement` states both directions of the source's reversed
  subgroup-inclusion criterion: both products of `e_K` and `e_L` equal `e_K`
  exactly when `L ≤ K`. This spells out the order from I.1.1 without installing
  an unproved multiplication instance on compact distributions.
- `InversionStatement` asserts the anti-multiplication identity for all compact
  distributions, with compact witnesses constrained to equal their actual
  inversion pushforwards, and fixes every compact-open `e_K`. This is the
  ambient compact-distribution form of the source's inversion identity.
  The existing inversion is complex-linear and involutive. Stability of the
  Hecke density range and its modular-weighted function formula are separately
  stated in `Distribution.RenardUniformDensity.InversionDensityStatement`.
- `CornerStatement` identifies the range of the existing corner inclusion
  followed by the density map with exactly
  `GroupFunctionSpaces.compactDistributionsBoth K.toSubgroup`. The unit of this
  actual unital corner maps to `e_K`. The published `Corner` construction
  already proves equality with the function sandwich `e_K H(G) e_K` and its
  ring and complex-algebra laws; the statement here is its distribution bridge.
- `DoubleCosetBasisStatement` first equates the density of the published
  `Corner.massIndicator K hK μ g` with the literal compact distribution
  `e_K * δ_g * e_K`. The function is the indicator of `KgK` divided by its
  Haar mass, rather than the unnormalized indicator. For any family of
  representatives giving a unique double coset for every group element,
  an actual `Basis` of the compact bi-invariant distribution submodule has
  precisely these normalized convolution values. The representative index
  type lives in the group universe, as does the double-coset quotient itself.

`Statements` is the conjunction of these seven closed `Prop`-valued targets.
They supply statements, not proofs. The exact uniform-density range, the
corrected discrete exceptions, the ideal property and the modular inversion
formula are already in the separate `RenardUniformDensityStatements` unit.

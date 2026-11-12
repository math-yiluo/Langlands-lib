# Rational rank-one Jacquet pattern: geometric input and assembly

Author: Worker 3917.

This module isolates the geometric input of the rank-one Jacquet pattern on the
actual rational-point families as a named proposition. It then proves that this
input, the published length-two proposition and the published support-category
detection proposition together imply the exact host target
`RationalRankOneJacquetModulesStatement.{u, v}` of
[RationalCorollaryTargets](RationalCorollaryTargets.md). The module proves an
implication only. The three inputs remain unproved, so the host target is not
proved here.

## `IsMaximalStandard.ne_univ`

For a finite type of labels `B`, a maximal standard subset `J = univ.erase α` is
different from `univ`, because `α` lies in `univ` but not in `univ.erase α`. The
assembly below uses this to supply the properness premise of the published
rational assembly.

## The geometric input `RationalRankOneGeometricJacquetStatement`

### Scope

The proposition has independent universe parameters `u` and `v`. It quantifies
over every nonarchimedean local field `k : Type u`, including positive
characteristic, and every connected reductive group scheme `G` over `Spec k`,
split or not, with an actual maximal split torus `i : T ⟶ G`. The rational-point
group carries the canonical evaluation topology `pointTopology`. Local
compactness, the nonarchimedean group structure and Hausdorffness are explicit
instance premises. Then come a generic cocharacter `ν`,
`StandardCocharacterStatement.{u}`, `StandardLeviIntersectionStatement.{u}`, a
relative root system `hRoots`, and closedness of every actual unipotent radical
`unipotent i ν I` and every actual Levi subgroup `levi i ν J`. The literal labels
`SimpleRoot i ν` receive the finite enumeration `simpleRelativeRootFintype` and
classical decidable equality.

The Coxeter data are the same as in the host target: a finite relative Weyl
group, the point normalizer and centralizer comparisons `hN`, `hZ`, a Coxeter
matrix `C` on the simple-root labels, an `ActualCoxeterSystem` of the torus point
normalizer modulo the full centralizer, and the premises
`RootLengthComparison`, `PositiveSimpleReflectionComparison`,
`actualLeviWeylIdentification`, `minimalityLengthCriterion` and
`associatedSubsetLaws`. They are retained so that `longestRep actual J` has the
meaning it has in the host target.

### Hypotheses on the datum

- `J` is a maximal standard subset: `IsMaximalStandard J`, that is
  `J = univ.erase α` for some simple-root label `α`.
- `σ` is an actual smooth complex representation of `levi i ν J`, with carrier
  universe `max (u + 1) v`, that satisfies the published `IsCorollaryLeviCuspidal`
  predicate: every proper normalized inside-Levi Jacquet module vanishes, computed
  with the actual restricted decompositions `isSemidirectDecomposition_in_levi`.
  Neither irreducibility nor finite length is assumed.
- `n` is a point of the torus normalizer whose class modulo the full centralizer
  is `longestRep actual J`.
- `hself` is an actual self-normalization witness: for every rational point `x`,
  `x ∈ levi i ν J ↔ n * x * n⁻¹ ∈ levi i ν J`.

### Conclusion

Write `i_J` for the actual normalized induction functor
`normalizedInductionFunctor` and `r_K` for the actual normalized Jacquet functor
`jacquetFunctor`, both built from the semidirect decompositions
`isSemidirectDecomposition_of_standardCocharacterStatement` and the closed
radicals. The conclusion is the conjunction of two assertions.

1. `HasRankOneJacquetMiddleSequence J σ n hself`. This published predicate of
   [RankOneJacquetAssembly](RankOneJacquetAssembly.md) asserts actual
   intertwining maps `f` and `g` forming a short exact sequence
   `0 → Ad(n⁻¹) σ → r_J(i_J σ) → σ → 0`. Here `Ad(n⁻¹) σ` is
   `(conjugationFunctor n⁻¹ _).obj σ`, which acts by `x ↦ σ(n * x * n⁻¹)`.
2. For every standard subset `K` with `K ≠ univ` and `K ≠ J`, the object
   `r_K(i_J σ)` is a zero object.

These are object-level assertions about actual smooth representations, not
equalities in a Grothendieck group.

### Source correspondence and provenance

This is a derived statement. It records, for the actual normalized functors, the
Jacquet-module computation that Aubert's proof of Corollaire 1.10(b) cites. In
Aubert, *Dualité dans le groupe de Grothendieck de la catégorie des
représentations lisses de longueur finie d'un groupe réductif p-adique*, Trans.
Amer. Math. Soc. 347 (1995), printed p. 2183, the proof states
`r_{L_J}(ρ₊) = σ`, `r_{L_J}(ρ₋) = Ad(w_J⁻¹)(σ)` with a reference to [Cas, 7.1], and
`r_{L_K}(ρ±) = 0` for `K ⊊ S`, `K ≠ J`. The underlying assertion about the
induced representation is Casselman, *Introduction to the theory of admissible
representations of p-adic reductive groups*, draft of 1 May 1995, §7.1, printed
p. 67. For a maximal proper parabolic `P` with `P = P̄` (the self-dual case),
Lemma 7.1.1(a) gives the exact sequence
`0 → (w⁻¹ σ) δ_P^{1/2} → I_N → σ δ_P^{1/2} → 0` for `I = i_P^G σ`, where
`w = (w_ℓ w_{ℓ,Θ})⁻¹`; the same paragraph records that `P̄` is the only
associate of `P` (by Casselman's 1.2.3). Casselman's proof refers to his 6.3.5,
the geometric lemma.

The following differences from these sources are deliberate.

- The functors here are the normalized ones, so the factors `δ_P^{1/2}` of
  Casselman's unnormalized Jacquet module do not appear.
- Self-duality `P = P̄` is expressed by the witness `hself`: the chosen lift `n`
  of `longestRep actual J` normalizes `levi i ν J`. The exact representative, the
  direction of conjugation and the inverse pullback follow the published host
  target and `HasRankOneJacquetMiddleSequence`; no new convention is introduced.
- Casselman assumes `σ` irreducible and absolutely cuspidal. The present
  proposition only assumes `IsCorollaryLeviCuspidal`. The geometric lemma holds
  for every smooth representation, and cuspidality alone removes the terms
  other than those of the identity and of `w`. Every proper `K ≠ J` has no
  surviving term: a surviving term needs `w J = K` for a Weyl element `w`, and
  the only standard associate of a self-associated maximal `J` is `J` itself.
  The host target applies the proposition only to irreducible `σ`.
- Reducibility of the induced representation is not assumed; the computation
  does not need it.

## The assembly

`RationalRankOneJacquetModulesAssemblyStatement` names the implication

```
RationalRankOneLengthTwoStatement.{u, v} →
  RationalSupportCategoryIrreducibleJacquetDetectionStatement.{u, v} →
    RationalRankOneGeometricJacquetStatement.{u, v} →
      RationalRankOneJacquetModulesStatement.{u, v}
```

and `rationalRankOneJacquetModulesAssembly` proves it as
`rationalRankOneJacquetModules_of_lengthTwo_detection_geometry`. That proof
introduces exactly the binders of the host target: the field, group, torus,
topology instances, cocharacter, structural statements, closed families, Coxeter
data, a maximal standard `J`, a finite-length `σ` with irreducibility,
cuspidality and reducibility of `i_J σ`, a lift `n` with
`QuotientGroup.mk n = longestRep actual J`, and a self-normalization witness
`hself`. It then proceeds in three steps.

1. `RationalRankOneLengthTwoStatement` applied to the same data gives actual
   finite-length objects `A`, `B` with `HasTwoConstituents (i_J σ) A B`.
2. `RationalRankOneGeometricJacquetStatement` applied to the same data, the same
   `n`, `hn` and `hself`, gives the middle sequence at `J` and the vanishing of
   `r_K(i_J σ)` for every other proper `K`.
3. The published `rankOneJacquetConstituentsOfRationalSupportDetection` of
   [RationalRankOneJacquetAssembly](RationalRankOneJacquetAssembly.md), applied to
   the detection proposition, `IsMaximalStandard.ne_univ`, the irreducibility and
   cuspidality of `σ`, the same `n` and `hself`, and the outputs of steps 1 and 2,
   returns an ordered pair `(ρ₊, ρ₋)` of actual finite-length objects with
   `HasTwoConstituents (i_J σ) ρ₊ ρ₋` and `RankOneJacquetPattern`. This is the
   witness the host target asks for.

Every lift `n` and every witness `hself` supplied by the host target is passed
unchanged, so the object isomorphisms `r_J ρ₊ ≅ σ` and
`r_J ρ₋ ≅ Ad(n⁻¹) σ` hold for that lift. No finite-length, exactness,
classification or self-association premise is added beyond the three named
propositions.

`rationalRankOneJacquetModules_of_lengthTwo_extraction_geometry` gives the same
conclusion with the detection proposition replaced by the published
`RationalCuspidalJacquetFactorExtractionStatement.{u, v}`. It composes the
assembly with the published
`rationalSupportCategoryIrreducibleJacquetDetection_of_cuspidalFactors` of
[RationalIrreducibleJacquetFactorDetection](RationalIrreducibleJacquetFactorDetection.md).

## Dependencies

The implication uses these published declarations:
`rankOneJacquetConstituentsOfRationalSupportDetection` and, through it,
`rankOneJacquetConstituentsOfSupportDetection`, `rootAssociation_one`,
`rootAssociation_ne_univ`, `isCorollaryLeviCuspidal_iff_isLeviCuspidal` and
`standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`
(the latter through `BruhatTits.dynamicUnipotentCompactOpenContainment`), as
documented in [RationalRankOneJacquetAssembly](RationalRankOneJacquetAssembly.md)
and [RankOneJacquetSupportDeduction](RankOneJacquetSupportDeduction.md). The
extraction variant also uses
`rationalSupportCategoryIrreducibleJacquetDetection_of_cuspidalFactors`.

The geometric lemma enters only through the unproved premise
`RationalRankOneGeometricJacquetStatement`. A cuspidal-support theorem (Renard
VI.5.4 in the form of support-category detection) enters only through the
unproved premise `RationalSupportCategoryIrreducibleJacquetDetectionStatement` or
the unproved extraction premise. Length two enters only through the unproved
premise `RationalRankOneLengthTwoStatement`. No proved instance of Langlands
classification, character independence, adjointness, the geometric lemma or a
cuspidal-support theorem is invoked.

## What remains

To prove the host target unconditionally one must prove
`RationalRankOneLengthTwoStatement` (its own proof task),
`RationalSupportCategoryIrreducibleJacquetDetectionStatement` or the extraction
proposition, and `RationalRankOneGeometricJacquetStatement`. An empty simple-root
type has no maximal standard subset, so the geometric proposition and the host
target are then vacuous; no nonemptiness premise is added.

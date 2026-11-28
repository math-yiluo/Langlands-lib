# Finite length of actual supercuspidal induction: proof

Module `Langlands.Representation.Aubert.General.RationalSupercuspidalInductionFiniteLengthProof`,
namespace `Langlands.Aubert.General.RationalPointFamily`.

The theorem `rationalSupercuspidalInductionFiniteLength` proves exactly the
published proposition
`RationalSupercuspidalInductionFiniteLengthStatement.{u, uV}`
([statement](RationalSupercuspidalInductionFiniteLengthStatement.md)), the
finite-length assertion of Renard, Théorème VI.5.4, on the actual standard
rational-point families. The theorem has no hypotheses. Its universe
parameters are `u` (field and group) and `uV` (input carrier); they are
independent. The statement's binder list is unchanged: every nonarchimedean
local field `k : Type u`, every connected reductive `G` with maximal split
torus `i` and generic cocharacter `ν`, the three ambient topological instances
on `pointTopology`, `hStandard`, `hInter`, `hRoots`, `hU`, `hM`, every standard
index `I` (including `Finset.univ`), and every irreducible
`σ : SmoothRep.{0, u, uV} ℂ (levi i ν I)` satisfying the published
`IsLeviCuspidal`. The conclusion is finite length of the actual full-parabolic
normalized induction `(normalizedInductionFunctor (h I) (hU I)).obj σ`, with
carrier `max u uV`. The statement pair and all the pairs it imports are
unchanged. Compilation reports the axioms `propext`, `Classical.choice` and
`Quot.sound` only.

## The Lean proof

The proof is one term:

```
rationalSupercuspidalInductionFiniteLengthFromExtractionInputs
  (rationalCuspidalExtractionInputs_of_specialVertexInputs
    (CuspidalSupport.rationalSpecialVertexCompactInputs_of_jointBasis
      BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence))
```

Read from the inside out, it applies four published theorems.

1. **Joint special compact basis.**
   `Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence`
   (module `Langlands.BruhatTits.SpecialCompact.JointBasisProof`) proves
   `JointSpecialCompactBasisExistenceStatement.{u}` without hypotheses: for
   every connected reductive group over a nonarchimedean local field in
   universe `u`, with a maximal split torus and a generic cocharacter, one
   special vertex of one apartment has the special compact properties, the
   Iwasawa and Cartan decompositions and the simultaneous standard basis
   (Renard V.5.1–V.5.2). Its building input is the Library's proof
   `bruhatTitsAvailability` of a valid Bruhat–Tits assignment.
2. **Special-vertex inputs.**
   `Langlands.CuspidalSupport.rationalSpecialVertexCompactInputs_of_jointBasis`
   (module `RationalCuspidalInertiaDecompositionReduction`) turns step 1 into
   `RationalSpecialVertexCompactInputsStatement.{u}`. It keeps the special
   vertex, the special compact properties and the simultaneous basis. It
   obtains the finite Cartan covering of the same compact subgroup from the
   Renard Cartan comparison of step 1 and the proved
   `rationalPositiveCartanCover`.
3. **Cuspidal extraction inputs.**
   `rationalCuspidalExtractionInputs_of_specialVertexInputs` (module
   `RationalCuspidalExtractionFromSpecialVertex`) proves
   `RationalCuspidalExtractionInputsStatement.{u, uV}`. That statement is a
   conjunction for the actual standard families:
   - (G) for an actual point Coxeter system with the root-length comparison,
     every actual induced Jacquet object `r_J i_I σ` has a finite filtration
     whose grades are actual normalized geometric terms. This is the
     unconditional `exists_pointInducedJacquetGeometricFiltration` (module
     `RationalInducedJacquetGeometricFiltration`), the actual geometric lemma
     for these families.
   - (E) inside every actual standard Levi `levi i ν J`, no irreducible
     `IsLeviCuspidal` representation is a subquotient of a proper inner
     normalized induction. This is
     `pointLeviStandardInductionCuspidalExclusion_of_specialVertexInputs`,
     a form of Renard, Lemme VI.5.2. It uses first adjointness, the
     transport of `IsLeviCuspidal` to cuspidality of the standard Levi scheme
     (`rationalLeviCuspidalityTransport`), both directions of Renard VI.2.1
     (`rationalCuspidalCompactRestriction` with the special vertex of step 2
     for that Levi scheme, and `rationalCompactRestrictionCuspidal`) and
     projectivity of compact representations (Renard IV.1.6).
4. **Finite length.**
   `rationalSupercuspidalInductionFiniteLengthFromExtractionInputs` (module
   `RationalSupercuspidalInductionExtractionInputsProof`) proves the
   implication from `RationalCuspidalExtractionInputsStatement.{u, uV}` to
   `RationalSupercuspidalInductionFiniteLengthStatement.{u, uV}`. Its proof
   has three parts.
   - *Detection.* The published `rationalCuspidalJacquetFactorExtraction_of_inputs`
     and `rationalSupportCategoryIrreducibleJacquetDetection_of_cuspidalFactors`
     give: every irreducible subquotient of `i_I σ` has a nonzero normalized
     Jacquet module along some standard `J` associated to `I` by an actual
     normalizer point (`rootAssociation`). This replaces Corollaire VI.2.1
     with Proposition VI.5.3 (ii) in Renard's proof.
   - *Associated Jacquet lengths.*
     `rationalAssociatedCuspidalJacquetFiniteLength_of_extractionInputs` uses
     (G) alone. Each grade of the filtration of `r_J i_I σ` is zero when the
     source intersection is proper, because `σ` is cuspidal, and is a
     conjugate of the irreducible `σ` when it is full. So each grade has
     length at most one and `r_J i_I σ` has finite length. This is the
     finite-length part of Proposition VI.5.3 (iii).
   - *Length bound.* The published
     `rationalSupercuspidalInductionFiniteLengthFromInputs` (module
     `RationalSupercuspidalInductionInputsProof`) lifts `σ` to carrier
     `max (u + 1) uV`. It supplies the point normalizer and centralizer
     comparisons by `rationalWeylComparison`. It then applies the
     exact-family length bound `exactFamilyLengthBound` to the finitely many
     associated normalized Jacquet functors, which are exact by
     `jacquetFunctor_map_isShortExact`. Finally it descends to carrier `uV`
     by `normalizedInduction_universeLift_hasFiniteLength_iff`.

The carrier universes match. The target is taken at `.{u, uV}`, step 4 at
`.{u, uV}` and step 3 at `.{u, uV}`. Steps 1 and 2 are statements about
groups only, at the field universe `u`.

## Structural hypotheses

The structural hypotheses are those already in the statement, and nothing
else is assumed:

- `hStandard : StandardCocharacterStatement.{u}`,
- `hInter : StandardLeviIntersectionStatement.{u}`,
- `hRoots : HasRelativeRootSystem i`,
- the closedness families `hU` and `hM`, and
- `LocallyCompactSpace`, `NonarchimedeanGroup` and `T2Space` on
  `RationalPoint k G.X` with `pointTopology`.

The proof passes each binder unchanged to
`RationalCuspidalExtractionInputsStatement`. Each of the four theorems above
is either closed or an implication whose antecedent is supplied by the
previous step. The proof uses no
representation-theoretic proposition as a premise: cuspidal embedding,
Jacquet detection, the geometric lemma, transitivity, admissibility and
finite length are not assumed. The geometric filtration, the exclusion, the
detection and the exactness of the Jacquet functors are proved in the
published modules named above.

## Normalization and cuspidality conventions

**Normalization.** Every functor in the proof is one of the Library's actual
normalized functors: the full-parabolic normalized induction, twisted by
`HaarModulus.closedHalfCharacter` of the radical, the matching normalized
Jacquet functor, and their inner versions in the standard Levis. The proof
does not use Renard's twist `δ_P^(-1/2)` with his inverse modular convention
(VI.1.2, printed pp.135–136 / PDF pp.141–142), and it does not identify that
twist with the Library character. The character facts that the chain needs
are proved inside the Library for these actual characters:

- the first adjointness in (E), `hom_eq_zero_of_isCuspidalFor_of_induction`,
  applies `FirstAdjointness.equiv`, which needs unimodularity of the inner
  radical. The published `isUnimodularModulus_standardUnipotent_in_levi`
  proves this from `isUnimodularModulus_of_isLimitOfCompactSubgroups` and the
  compact-limit property
  `standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`,
  which uses `hStandard`;
- the geometric filtration (G) cancels the Haar corrections of its terms by
  the published `geometricEpsilon_mul_eq_one`;
- exactness of the Jacquet functors uses the same compact-limit property.

Unimodularity and character identities are not premises.

**Cuspidality.** The input predicate is the statement's proper-standard
`IsLeviCuspidal`: the normalized Jacquet module of `σ` vanishes along each
inner standard parabolic `(parabolic i ν (leviIndex I K)).subgroupOf (levi i ν I)`
for `K ≠ Finset.univ`. The proof never needs Renard's definition by all
proper parabolics (VI.2.1, printed p.137 / PDF p.143). Only the
proper-standard form is used:

- in (G) and the associated Jacquet lengths, through the published
  equivalence `isCorollaryLeviCuspidal_iff_isLeviCuspidal`;
- in (E), through `rationalLeviCuspidalityTransport`, which identifies
  `IsLeviCuspidal` with `IsCuspidal`, the proper-standard predicate of the
  standard Levi scheme's own family. The Library states VI.2.1 for that
  predicate.

So the proof needs no comparison between all proper parabolics and proper
standard ones.

## Relation to the source

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`;
Théorème VI.5.4 and its proof, printed pp.173–174 / PDF pp.179–180.

Renard first conjugates to standard parabolics. He attaches to an
irreducible subquotient `π₀` of `i_P^G ρ` a standard `Q = LU` with `r_Q π₀`
supercuspidal and nonzero (Corollaire VI.2.1). By Proposition VI.5.3 (ii),
`L` is conjugate to `M`. He then bounds the length by the additive function
`l'(τ) = Σ_{L ∼ M} l(r_Q τ)`, which is additive because the `r_Q` are exact,
and computes `l'(i_P ρ) = l(M)` by VI.5.3 (iii). The implemented proof has the
same three ingredients: detection along associated standard indices, exact
Jacquet functors, and finite length of each `r_J i_I σ`. It differs in two
ways:

- detection comes from cuspidal factor extraction, which uses the
  geometric filtration and the exclusion (E). Renard proves VI.5.2 from the
  VI.3.5 decomposition. The proof of (E) uses compact restriction to the
  norm kernel at one special vertex instead.
- for each associated `J`, only finiteness of the length of `r_J i_I σ` is
  proved. The proof does not count Weyl cosets.

Only finite length is concluded. The bound `l(M)`, the equivalences of the
Theorem and the bound on `dim Hom` are outside the statement and are not
proved here.

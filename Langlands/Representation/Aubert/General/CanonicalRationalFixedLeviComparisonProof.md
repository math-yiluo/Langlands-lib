# Proof of the canonical fixed-Levi comparison

This module proves the published proposition
`Langlands.Aubert.General.RationalPointFamily.CanonicalRationalFixedLeviComparisonStatement`
(module `CanonicalRationalComplexTargets`) at universes `u`, `v`:

`theorem canonicalRationalFixedLeviComparison :
  CanonicalRationalFixedLeviComparisonStatement.{u, v}`.

The target is the equality `D̃_{L_I}(r_{L_I}(E)) = r_{L_I}(E)` of Aubert's
1996 erratum, Remarques (1), printed p. 4690, just before display (∗∗). It is
stated as a natural isomorphism `D̃_{L_I} ∘ r_I ≅ r_I` on the full actual
support category of every standard subset `I`. Here `D̃_{L_I}` is the
full-support terminal functor of the actual Levi and `r_I` the actual
normalized Jacquet functor. The statement covers the canonical topology,
maximal split torus, generic cocharacter and every linear order on the actual
simple roots, for every connected reductive group over every nonarchimedean
local field. The statement module's Markdown describes the statement, its
meaning and its provenance. This file describes only the Lean proof.

The theorem proves the whole proposition. The proposition has no hypothesis:
it has no dynamic finite-length binder and no structural premise, since all
structural data are fixed to published canonical values. The theorem is
therefore unconditional and adds no hypothesis.

Authors: Worker 29, with Worker 3640 (Task 3640, block (vii)). Submitted by
Worker 444 (Task 6881), with the Lean unchanged.

## Proof

The proof is a single term:

```
canonicalRationalFixedLeviComparison_of_rational.{u, v}
  rationalFixedLeviComparison.{u, v}
```

1. `rationalFixedLeviComparison : RationalFixedLeviComparisonStatement.{u, v}`
   (module `RationalFixedLeviComparisonProof`) is the published proof of the
   existing rational-point target (module `RationalTerminalJacquet`). That
   target already fixes the topology on the rational points to
   `pointTopology`, and quantifies all structural premises: the local
   compactness, nonarchimedean-group and Hausdorff instances of that
   topology, the cocharacter, order and intersection statements, the relative
   root system, the normalizer and centralizer comparisons, the closedness
   families of the unipotent and Levi subgroups and the restricted
   compact-limit family. It has no other hypothesis.
2. `canonicalRationalFixedLeviComparison_of_rational`
   (module `CanonicalRationalComplexTargetBridgesProof`, the second component
   of `canonicalRationalComplexTargetBridges`, the published proof of
   Task 6425, `d7477c1e-06c2-43ec-9035-3eb6b594058b`) proves
   `RationalFixedLeviComparisonStatement.{u, v} →
   CanonicalRationalFixedLeviComparisonStatement.{u, v}`. It specializes the
   existing target to the canonical instances
   `rationalPoint_locallyCompactSpace`,
   `Plancherel.rationalPoints_nonarchimedeanGroup` and `rationalPoint_t2Space`
   and to the canonical structural data: `standardCocharacter`, `standardParabolicOrder`, `standardLeviIntersection`,
   `relativeRootSystem k G hG T i hi`, `canonicalPointNormalizerComparison`,
   `canonicalPointCentralizerComparison`, `canonicalStandardUnipotent_isClosed`,
   `canonicalStandardLevi_isClosed` and
   `canonicalStandardLeviUnipotent_isLimitOfCompactSubgroups`.

The universe arguments are passed explicitly, so both declarations are used
at exactly the universes of the conclusion.

All modules named are in `Langlands/Representation/Aubert/General/`.

## Dependency status

Every module this proof imports is in the Library (checked at Library commit
`72480b70c88adff84a438bd7029d64ee3977469c`). Against that Library, in Lean
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, the module compiles with
zero errors and zero warnings. The theorem uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

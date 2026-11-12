# Epsilon-factor inheritance for the assembled correspondence

Author: Worker 4804.

`Langlands.Correspondence.assemblyEpsilonInheritance.{uF, uP, uA}` proves
exactly the published proposition
`Langlands.Correspondence.AssemblyEpsilonInheritanceStatement.{uF, uP, uA} F`
(module `Langlands.Correspondence.AssemblyTheorems`). Its outer telescope is
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)`. The field universe `uF`, the
parameter universe `uP` and the automorphic carrier universe `uA` are
independent. The theorem has no hypotheses. The Lean service reports only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

The target says: for every supercuspidal map `c0`, full map `c` and rank-one
reciprocity candidate `e`, if `c0` is a supercuspidal correspondence, `c` is an
assembly of `c0` and `e` is geometrically normalized, then `c` is compatible
with all pair epsilon factors for some local-constant system with base
component `e` (Henniart 2002, Theorem 1.5(iii), epsilon part).

## Proof

The proof is a single term. It applies the published reduction
`assemblyEpsilonInheritance_of_classification_of_segmentHeadL F hC hL`
(module `Langlands.Correspondence.AssemblyEpsilonClassificationReduction`).
That reduction has exactly two premises, both now proved in the Library:

- `hC : Classification.SquareIntegrableLanglandsClassification.{uF, uA} F
  F.canonicalTopologicalData`. It is the published theorem
  `Classification.squareIntegrableLanglandsClassification.{uF, uA}` (module
  `Langlands.Representation.Classification.SquareIntegrableLanglandsClassificationProof`),
  applied to `F` and `T = F.canonicalTopologicalData`.
- `hL : RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA}`, the
  L-factor formula for pairs of segment heads (Henniart 2002, §2.6, first
  display). It is
  `RankinSelberg.segmentHeadLFactor_of_squareIntegrable.{uF, uA, uA}`
  (module `Langlands.Representation.RankinSelberg.SegmentHeadLFactorReduction`)
  applied twice to the published theorem `RankinSelberg.squareIntegrableLFactor`
  (JPSS 1983, Theorem (8.2); module
  `Langlands.Representation.RankinSelberg.SquareIntegrableLFactorProof`).
  The reduction asks for `SquareIntegrableLFactorStatement` at two universe
  orders, `{uF, uV, uW, max uF uV, max uF uW}` and
  `{uF, uW, uV, max uF uW, max uF uV}`. Here `uV = uW = uA`, so both are
  `{uF, uA, uA, max uF uA, max uF uA}`. `squareIntegrableLFactor` has
  arbitrary independent universes, so it supplies both.

## What the imported reduction does

The following is recorded in the paired Markdown of the published modules; it
is not reproved here.
`assemblyEpsilonInheritance_of_classification_of_segmentHeadL` discharges all
other premises of `assemblyEpsilonInheritance_of_segmentHeads` (module
`Langlands.Correspondence.SegmentEpsilonInheritance`) with proved theorems:

- multisegment datum matching, from the proved datum existence
  `multisegmentHeadDatumExistence` and the classification `hC`, by
  `multisegmentHeadDatumMatching_of_existence_and_classification`;
- the segment-head gamma formula `RankinSelberg.segmentHeadGammaFactor`;
- the block-pair gamma law `blockPairGamma F` (Henniart 2002, §2.4), from the
  proved pair-block Euler formula `LocalFactor.wdEulerPairBlock`;
- the pair-block Euler formula `LocalFactor.wdEulerPairBlock` itself.

`assemblyEpsilonInheritance_of_segmentHeads` derives segment-pair epsilon
compatibility from the segment-head L and gamma formulas, and then the
assembled epsilon inheritance from datum matching.

## Provenance

This module is an internal composition of published Library theorems. It adds
no definition, statement or literature claim. The target's source is
Henniart 2002, §1.5, Theorem (iii), printed p.590, as recorded in the target's
Markdown (`Correspondence/AssemblyTheorems.md`). The implemented route follows
the Library's reductions above rather than a particular printed proof.

## Validation

The module compiles in the project Lean service with no errors or warnings.
There is no `sorry`, no `admit` and no new axiom.

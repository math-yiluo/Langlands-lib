# Proof of the normalized-exponent standard reduction

The theorem
`Langlands.Aubert.General.RepresentedParabolic.normalizedTemperedStandardReduction`
proves the published proposition
`Langlands.Aubert.General.RepresentedParabolic.NormalizedTemperedStandardReductionStatement.{u, v}`
with no hypotheses. Its type is that proposition, with the same level
parameters `u` and `v`.

## Proof

The proof applies the published conditional theorem
`normalizedTemperedStandardReduction_of_dynamic_structural_statements`
from `NormalizedTemperedStandardReductionFromDynamics`. That theorem derives
the target from four global structural statements. Each of them is now proved
in the Library, in namespace `Langlands.GroupScheme`:

- `parabolicDynamic : ParabolicDynamicStatement.{u}`, from
  `Langlands.GroupScheme.Absolute.ParabolicDynamicProof`;
- `dynamicGeometricUnipotentRadical : DynamicGeometricUnipotentRadicalStatement.{u}`,
  from `Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof`;
- `smoothMaximalSplitTorusConjugacy : SmoothMaximalSplitTorusConjugacyStatement.{u}`,
  from `Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof`;
- `relativeRootSystem : RelativeRootSystemStatement.{u}`, from
  `Langlands.GroupScheme.Rational.RelativeRootSystemProof`.

The Lean proof is the single term that applies the conditional theorem to
these four proofs. It adds no lemma, hypothesis or axiom. The inspected
axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Scope

The conclusion is the unchanged Library proposition. It keeps the fixed
actual maximal split torus, generic cocharacter and minimal parabolic, the
all-test subgroup-functor equalities with simultaneous cocharacter
realization, admissibility on the right-hand side, and every compatible
presentation, radical and exponent test. It keeps all nonarchimedean local
fields of the current interface, nonsplit connected reductive groups, and the
independent representation-carrier universe `v`.

The proposition uses the derived normalized temperedness predicate. This
proof does not compare it with the raw-logarithm convention of Renard V.3.20.
That source comparison, and the later temperedness consequences listed in the
statement's Markdown, remain separate units.

# Existence of actual common-closure local-constant systems

Lean module: `Langlands.LocalFactor.NonabelianSystemExistsProof`.

## Statement proved

`Langlands.LocalFactor.NonabelianSystem.exists_system` proves the published proposition
`Langlands.LocalFactor.NonabelianSystem.Exists.{uF, uV} F e` (module
`Langlands.LocalFactor.NonabelianSystem`). It does so for every prime `p`, every
`F : PadicField.{uF} p`, every independent representation universe `uV` and every
supplied `e : CommonClosure.ReciprocityFamily F`. It uses no extra hypotheses. The
target keeps its own premise `NormalizedReciprocity F e`, and the theorem does not
assume it. Under that premise the target asks for one actual unit-valued
`Assignment.{uF, uV} F`, defined on every finite intermediate field of the common
algebraic closure. That one assignment must satisfy all four laws of `IsSystem F e`:

- additivity on the continuous exact virtual group;
- positive real Haar scaling by the actual integer virtual degree;
- degree-zero induction for all nested extensions and all Haar measures, using the
  actual trace additive character;
- rank-one agreement with the concrete abelian epsilon expression through `e`.

The theorem does not change the target's Lean/Markdown pair or any pair it imports.

## Implemented proof

The Lean proof is one term built from two published Library results:

1. `Langlands.LocalFactor.NonabelianBrauer.exists_of_kernelCompatibilityStatement`
   (module `Langlands.LocalFactor.NonabelianBrauerSystem`) states that the universally
   quantified Brauer-kernel compatibility proposition
   `NonabelianBrauer.KernelCompatibilityStatement.{uF, uV}` implies
   `NonabelianSystem.Exists.{uF, uV} F e` for each `F` and `e`, with both universes
   unchanged. That module does the real construction. Under the normalized-reciprocity
   premise, it builds the assignment on the actual Brauer presentation of the
   continuous exact virtual groups. It defines the assignment by descent of the
   abelian epsilon-ratio evaluation, which is possible because the evaluation vanishes
   on the presentation kernel. It then proves all four `IsSystem` laws for this one
   assignment.
2. `Langlands.LocalFactor.NonabelianBrauer.kernelCompatibilityStatement`
   (module `Langlands.LocalFactor.NonabelianBrauerKernelProof`) proves
   `KernelCompatibilityStatement.{uF, uV}` with both universes free and no
   hypotheses. This is the arithmetic input from Deligne's 1973 paper (Lemma 4.7 and
   the global argument of §4.12): the actual abelian epsilon-ratio evaluation
   vanishes on the kernel of the actual Brauer presentation of the continuous exact
   degree-zero group.

Applying (1) to `F`, `e` and the theorem (2) gives the target, so the declaration is

```lean
NonabelianBrauer.exists_of_kernelCompatibilityStatement F e
  NonabelianBrauer.kernelCompatibilityStatement.{uF, uV}
```

The proof therefore supplies none of the following as a hypothesis: an assignment, a
Brauer decomposition, compatible descent, a generation result, or nonvanishing of the
abelian expression. All of these are internal to the published proofs of (1) and (2).

# Proof of the totally complex reduction of the exact-stabilizer prime branch

Module `Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerPrimeBranchReductionTCProof`.

## Result

`proposition48ExactStabilizerPrimeBranchReductionTC :
Proposition48ExactStabilizerPrimeBranchReductionTCStatement.{uF, uV}`, the exact
totally complex target of module
`HarrisProposition48ExactStabilizerPrimeBranchReductionStatement` (unchanged),
for arbitrary universes `uF`, `uV`. No hypothesis is added, and no axiom beyond
`propext`, `Classical.choice` and `Quot.sound` is used.

## Proof

The proof introduces the twelve interfaces (interface 7 in its totally complex
form `WeakInductionConjugateInverseSelfDualTCStatement`) and the eight premises of
`Proposition48ExactStabilizerPrimeBranchTCStatement`, and applies
`proposition48ExactStabilizerPrimeBranch_of_inputs` from
`HarrisProposition48ExactStabilizerPrimeBranchReductionProof`, whose Markdown
describes that argument step by step. The inputs it receives are:

- `h7 hRig`, the totally complex self-duality input applied to the premise
  `CuspidalSpectralRigidityTCStatement`; its conclusion is the same as that of the
  general form, so it is the hypothesis `hcsd`;
- `CyclicRegularInductionTCStatement` (B2) and
  `CyclicWeakInductionSupercuspidalTCStatement` (B4) of the target, unchanged.
  The common argument applies them only at the base field `Q.E`, which is a CM
  field, so the instance `[NumberField.IsTotallyComplex Q.E]` is Mathlib's
  `IsCMField.isTotallyComplex`; no total complexity of the step field `D` is
  needed;
- restricted B7, the bridge and interfaces 1–6 and 8–12, which are the same as in
  the general reduction.

The unrestricted forms of rigidity, B2 and B4 are not used. Harris's Theorem 1.2,
`Proposition48IsobaricInvarianceTCStatement` and `CyclicRegularOrbitLiftTCStatement`
are introduced and not used.

## Source

Harris (1998), *The local Langlands conjecture for GL(n) over a p-adic field,
n < p*, Invent. Math. 134, Proposition 4.8, proof of the prime-orbit case, printed
p.203 (registered source `harris-1998-local-langlands`; arXiv source
`math_9611226v1.tex`, lines 1646–1664), in the form described in
`HarrisProposition48ExactStabilizerPrimeBranchReductionProof.md`.

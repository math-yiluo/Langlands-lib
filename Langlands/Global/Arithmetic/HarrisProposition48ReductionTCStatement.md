# Harris's Proposition 4.8 from its named inputs, over totally complex fields

Author: Worker 0. Statement contribution to Task 0
(`69dd20b3-6a77-44aa-b779-32391843c8dd`), revision 1, as decided in the
operator's answer `d9c91a7e0fcb5cabbc936380004a4ae7` (option b1) to request
`99dd5c974ab65af5a036022f960632d5`, which asked for
`Proposition48ReductionTCStatement` in the convention of the operator's answer
`81ed24709e7050068786116ca6613260` (Option A).

**Scope.** The module
`Langlands.Global.Arithmetic.HarrisProposition48ReductionTCStatement` defines four
propositions in the namespace `Langlands.Global.Harris` and proves nothing. The
principal one, `Proposition48ReductionTCStatement.{uF, uV}`, is the published
`Proposition48ReductionStatement.{uF, uV}` (module
`Langlands.Global.Arithmetic.HarrisProposition48ReductionStatement`) with its
global automorphic inputs replaced by totally complex forms. The conclusion,
`Proposition48Statement.{uF, 0, 0, 0, uV}`, is unchanged, and so are the
universes.

| Input | In the published reduction | In `Proposition48ReductionTCStatement` |
|---|---|---|
| 1–4 | `Proposition48AuxiliaryRankOneStatement`, `…ParityNormalizationStatement`, `…ParityUntwistStatement`, `Proposition48MackeyStepStatement` | unchanged |
| 5 | `Proposition48PrimeBranchStatement` | `Proposition48PrimeBranchTCStatement` (this module) |
| 6 | `Proposition48SingletonBranchStatement` | `Proposition48SingletonBranchTCStatement` (this module) |
| 7, 8 | `Harris1998Theorem12CuspidalStatement`, `HarrisSupercuspidalLocalComparisonStatement` | unchanged |
| 9 | `CuspidalSpectralRigidityStatement` | `CuspidalSpectralRigidityTCStatement` |
| 10 | `Proposition48IsobaricInvarianceStatement` | `Proposition48IsobaricInvarianceTCStatement` (this module) |
| 11–14 | `CyclicRegularInductionStatement`, `CyclicRegularOrbitLiftStatement`, `CyclicStableDescentStatement`, `CyclicWeakInductionSupercuspidalStatement` | their `…TCStatement` forms |

The forms of inputs 9 and 11–14 add `[NumberField.IsTotallyComplex F]` after
`[NumberField F]`; they are defined in
`Langlands.Automorphic.Unramified.CuspidalSpectralRigidityTCStatement` and
`Langlands.Automorphic.Unramified.CyclicTransferInputsTCStatement`, with their own
Markdown. Inputs 1–4 contain no global automorphic statement, and inputs 7 and 8
are already stated only for CM fields; they stay as published, at the same
universes.

## 1. Why inputs 5, 6 and 10 are restated too

The operator's answer named the totally complex forms of inputs 9 and 11–14 and
of the reduction. Three further inputs have to change with them, because they
take inputs 9–14 as hypotheses:

- input 5, the prime branch, assumes inputs 7, 8, 9, 10, 11, 12 and 14;
- input 6, the singleton branch, assumes inputs 7, 9, 10 and 13;
- input 10, isobaric invariance, assumes input 9.

The intended proof of the reduction discharges these hypotheses with the separately
supplied inputs 7–14. If only inputs 9 and 11–14 were restricted, the published
inputs 5, 6 and 10 could not be applied to their totally complex forms, and the
reduction would still need the unrestricted inputs. So each of inputs 5, 6 and 10
is restated with the totally complex forms as hypotheses; the rest of each body is
copied verbatim:

- `Proposition48IsobaricInvarianceTCStatement.{uV}`: the hypothesis
  `CuspidalSpectralRigidityStatement.{0, uV}` becomes
  `CuspidalSpectralRigidityTCStatement.{0, uV}`, and, since rigidity is now
  available only over totally complex fields, the number field `K` gets
  `[NumberField.IsTotallyComplex K]` after `[NumberField K]` (the field `F` of this
  statement is only an `F`-algebra base and is not a number field here).
- `Proposition48PrimeBranchTCStatement.{uF, uV}`: the hypotheses 9, 10, 11, 12 and
  14 become their totally complex forms (10 as above); 7 and 8 and the body (the
  problem `Q`, the prime cyclic step `D`, the Mackey children and the conclusion
  `Q.HasSolution`) are unchanged.
- `Proposition48SingletonBranchTCStatement.{uF, uV}`: the hypotheses 9, 10 and 13
  become their totally complex forms; 7 and the body are unchanged.

The operator is informed of this addition.

## 2. The statement

`Proposition48ReductionTCStatement.{uF, uV}` says: the conjunction of the fourteen
inputs of the table, in the published order and at the published universes
(inputs 7–14 at number-field universe `0` and carrier universe `uV`), implies
`Proposition48Statement.{uF, 0, 0, 0, uV}`, Harris's Proposition 4.8: for every
datum of that statement (over CM fields `E`, `E'` and a finite extension `L` of
`E`), there is a solution with the proposition's four-part output: weak
automorphic induction of the given character, regular algebraicity, conjugate
self-duality and supercuspidality at the specified auxiliary place.
The meaning of every input and of the conclusion is explained in
`HarrisProposition48ReductionStatement.md` and the Markdown files of the inputs.

## 3. Relation to the published statements

A private development check of Worker 0 compiled:

- each of inputs 9 and 11–14 implies its totally complex form (forget the
  instance);
- inputs 9 and 10 together imply `Proposition48IsobaricInvarianceTCStatement`;
- `Proposition48PrimeBranchTCStatement` implies `Proposition48PrimeBranchStatement`,
  and `Proposition48SingletonBranchTCStatement` implies
  `Proposition48SingletonBranchStatement`: the published hypotheses imply the
  totally complex ones, and the conclusions agree.

No implication between the two reductions is claimed in either direction: the
totally complex reduction has weaker inputs 9–14 but stronger inputs 5, 6 and 10.

## 4. Why the totally complex forms are stated, and the expected proof

The goal of Task 0 is local. On the Library's route to the local correspondence
(route note `notes/henniart/llc-proof-route.md`), Proposition 4.8 is hypothesis 1
of `Langlands.Henniart.CandidateExistenceTCReductionStatement`, and its unrestricted
inputs 9 and 11–14 rest on global results whose proofs involve the real places:
the poles of pair L-functions (`CuspidalPairPoleStatement`) for rigidity, and the
archimedean places of the trace-formula comparison for cyclic base change. Harris's
Proposition 4.8
concerns CM fields: in a `Proposition48Problem` the fields `E` and `E'` are CM
(`[IsCMField E]`, `[IsCMField E']`) and `L` is a finite extension of `E`. A CM field
is totally complex (Mathlib `NumberField.IsCMField.isTotallyComplex`), and every
finite extension of a totally complex field is totally complex
(`NumberField.isTotallyComplex_of_algebra`). So every number field at which the
proof applies inputs 9–14 — the fields of the problem, the intermediate fields of
`L/E` and the prime cyclic steps between them — is totally complex, and the
restriction loses nothing.

Expected proof. In the reduction itself, inputs 7–14 are only passed to inputs 5
and 6, which take exactly their totally complex forms. So the intended proof of
the published reduction (strong induction on `Proposition48Problem.inductionDegree`,
described in `HarrisProposition48ReductionStatement.md`) proves this statement with
the hypotheses renamed. The applications at particular number fields happen inside
proofs of inputs 5, 6 and 10; their totally complex forms obtain the instances at
those fields from the two Mathlib lemmas above. The published reduction and its
inputs have no Lean proof yet; they belong to Task 6413, whose executors are asked
to stage proofs of these forms as supporting candidates, following the operator's
answers.

## 5. Sources and provenance

Provenance: *derived*. This is a derived organization of Harris's proof restricted
to totally complex fields, which are the only fields that proof uses; it is not
stated as such in the source. The source correspondence of each input and of the
conclusion is inherited unchanged from the published Markdown
(`HarrisProposition48ReductionStatement.md`,
`HarrisProposition48PrimeBranchStatement.md`,
`HarrisProposition48SingletonBranchStatement.md`,
`HarrisProposition48IsobaricInvarianceStatement.md`).

- `harris-1998-local-langlands` (Harris): M. Harris, *The local Langlands
  conjecture for GL(n) over a p-adic field, n < p*, Invent. Math. 134 (1998),
  177–210, Proposition 4.8 and its proof, printed pp.201–203 (PDF 25–27); the
  isobaric invariance step, printed p.202 (PDF 26), final paragraph; Lemma 1.6,
  printed pp.188–189 (PDF 12–13), for the singleton branch.

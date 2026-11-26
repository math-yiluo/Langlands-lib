# Proof of the exact-stabilizer prime branch of Proposition 4.8

Module `Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerPrimeBranchProof`.

## Result

`proposition48ExactStabilizerPrimeBranch :
Proposition48ExactStabilizerPrimeBranchStatement.{uF, uV}`, the exact target of
module `HarrisProposition48ExactStabilizerBranchStatement` (unchanged), for
arbitrary independent universes `uF` (local fields of `Proposition48Problem`)
and `uV` (carriers). No hypothesis is added, and no axiom beyond `propext`,
`Classical.choice` and `Quot.sound` is used.

The target is an implication: its own premises — Harris's Theorem 1.2
(`Harris1998Theorem12CuspidalStatement`), rigidity
(`CuspidalSpectralRigidityStatement`), isobaric invariance
(`Proposition48IsobaricInvarianceStatement`), B2
(`CyclicRegularInductionStatement`), B3 (`CyclicRegularOrbitLiftStatement`), B4
(`CyclicWeakInductionSupercuspidalStatement`), restricted B7
(`RestrictedCyclicWeakBaseChangeComplexPlaceStatement`), the archimedean bridge
(`CuspidalComplexParameterBridgeTCStatement`), and the branch hypotheses
(exact-stabilizer validity, a prime cyclic step `D` with `[D : E]` Mackey
classes, `HasDistinctMackeyComponents` and the children's solutions) — remain
premises of the theorem, exactly as stated. This module proves none of them.

## Proof

The proof is a single application of
`proposition48ExactStabilizerPrimeBranchReduction`
(module `HarrisProposition48ExactStabilizerPrimeBranchReductionProof`), which
proves `Proposition48ExactStabilizerPrimeBranchReductionStatement`: the twelve
interfaces listed in `HarrisProposition48ExactStabilizerPrimeBranchReductionStatement.md`
imply `Proposition48ExactStabilizerPrimeBranchStatement`. Each interface is
discharged by its proof in the Library, at the universes the reduction
requires:

| # | Interface | Proof | Module |
|---|---|---|---|
| 1 | `Proposition48MackeyFibreStatement.{uF}` | `proposition48MackeyFibre` | `HarrisProposition48MackeyFibreProof` |
| 2 | `Proposition48MackeyConstituentGaloisConjugateStatement.{uF, uV}` | `proposition48MackeyConstituentGaloisConjugate` | `HarrisProposition48MackeyGaloisProof` |
| 3 | `Proposition48MackeyChildTransportStatement.{uF, uV}` | `proposition48MackeyChildTransport` | `HarrisProposition48MackeyChildTransportProof` |
| 4 | `Proposition48PrimeInducedParameterStagesStatement.{uF}` | `proposition48PrimeInducedParameterStages` | `HarrisProposition48PrimeInducedParameterStagesProof` |
| 5 | `Proposition48PrimeInductionStagesStatement.{uF, uV}` | `proposition48PrimeInductionStages` | `HarrisProposition48PrimeInductionStagesProof` |
| 6 | `Proposition48InducedParameterRegularAlgebraicStatement.{uF}` | `proposition48InducedParameterRegularAlgebraic` | `HarrisProposition48InducedParameterRegularAlgebraicProof` |
| 7 | `WeakInductionConjugateInverseSelfDualStatement.{uV, 0, 0}` | `weakInductionConjugateInverseSelfDual` | `HarrisWeakInductionConjugateSelfDualProof` |
| 8 | `ArithmeticComapUnitaryCentralCharacterStatement.{0, 0}` | `Langlands.Automorphic.arithmeticComapUnitaryCentralCharacter` | `Langlands.Automorphic.ArithmeticComapUnitaryCentralCharacterProof` |
| 9 | `ArithmeticComapSupercuspidalComponentStatement.{0, 0, uV}` | `Langlands.Automorphic.arithmeticComapSupercuspidalComponent` | `Langlands.Automorphic.ArithmeticComapSupercuspidalComponentProof` |
| 10 | `ConjugateSelfDualUnitaryCentralCharacterStatement.{0}` | `conjugateSelfDualUnitaryCentralCharacter` | `HarrisConjugateSelfDualUnitaryCentralCharacterProof` |
| 11 | `ConjugateSelfDualSupercuspidalConjPlaceStatement.{0, uV}` | `conjugateSelfDualSupercuspidalConjPlace` | `HarrisConjugateSelfDualSupercuspidalConjPlaceProof` |
| 12 | `SplitPlaceNeConjPlaceStatement.{0}` | `splitPlaceNeConjPlace` | `HarrisSplitPlaceNeConjPlaceProof` |

Unless stated otherwise, the declarations are in `Langlands.Global.Harris` and
the modules in `Langlands.Global.Arithmetic`. The number fields of
`Proposition48Problem` lie in `Type`, so the field universes of interfaces 7–12
are `0`, as in the reduction statement.

The resulting term has the type of the target: the reduction's conclusion is
`Proposition48ExactStabilizerPrimeBranchStatement.{uF, uV}` itself, so its
premises (Theorem 1.2, rigidity, isobaric invariance, B2, B3, B4, restricted B7,
the bridge) and the branch hypotheses pass through unchanged. How these are
used is described in `HarrisProposition48ExactStabilizerPrimeBranchReductionProof.md`:
rigidity enters only through interface 7, and Theorem 1.2, isobaric invariance
and B3 are not used by that argument. The induction argument itself is not
repeated here.

## Source

Harris (1998), *The local Langlands conjecture for GL(n) over a p-adic field,
n < p*, Invent. Math. 134, Proposition 4.8, proof of the prime-orbit case, printed
p.203 (registered source `harris-1998-local-langlands`; arXiv source
`math_9611226v1.tex`, lines 1646–1664), with the convention that solutions carry
the complex-place parameters of the representation induced from the character
`ξ`, and with the distinctness of the Galois conjugates of the constituent
supplied by `HasDistinctMackeyComponents`; see
`HarrisProposition48ExactStabilizerBranchStatement.md` and
`HarrisProposition48ExactStabilizerPrimeBranchReductionStatement.md`.

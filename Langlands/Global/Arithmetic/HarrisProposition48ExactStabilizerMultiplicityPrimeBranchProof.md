# Proof of the exact-stabilizer prime branch of Proposition 4.8 with multiplicity

Module `Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerMultiplicityPrimeBranchProof`.

## Result

`proposition48ExactStabilizerMultiplicityPrimeBranch :
Proposition48ExactStabilizerMultiplicityPrimeBranchStatement.{uF, uV}`, the exact
target of module `HarrisProposition48MultiplicityStatement` (unchanged), for
arbitrary universes `uF`, `uV`. No hypothesis is added, and no axiom beyond
`propext`, `Classical.choice` and `Quot.sound` is used.

The statement is the exact-stabilizer prime branch
`Proposition48ExactStabilizerPrimeBranchStatement` of the induction for Harris
(1998), Proposition 4.8, with Harris's Theorem 1.2 with multiplicity in Henniart's
form (`Harris1998Theorem12CuspidalMultiplicityStatement`) in place of
`Harris1998Theorem12CuspidalStatement` and with the additional hypothesis
`Q.IsSpaced`. Its conclusion is `Q.HasParameterSolution` for the original inducing
character `Q.ξ`.

## Proof

The proof introduces the eight premises of the statement: Theorem 1.2 with
multiplicity, `CuspidalSpectralRigidityStatement` (`hRig`),
`Proposition48IsobaricInvarianceStatement`, B2 (`CyclicRegularInductionStatement`),
B3 (`CyclicRegularOrbitLiftStatement`), B4
(`CyclicWeakInductionSupercuspidalStatement`), restricted B7
(`RestrictedCyclicWeakBaseChangeComplexPlaceStatement`) and the bridge
(`CuspidalComplexParameterBridgeTCStatement`). It then introduces the problem `Q`,
the step field `D` and the six hypotheses of the branch: exact-stabilizer validity
`Q.IsAuxiliaryExactStabilizerValid`, `Q.IsSpaced`, the prime step
`Q.IsPrimeCyclicStep D`, the orbit cardinality
`Nat.card (Q.MackeyIndex D) = Module.finrank Q.E D`,
`Q.HasDistinctMackeyComponents D`, and the untwisted children, one for each
`a : Q.L ≃ₐ[Q.E] Q.L`.

It concludes by `proposition48ExactStabilizerPrimeBranch_of_inputs` (module
`HarrisProposition48ExactStabilizerPrimeBranchReductionProof`), the prime-orbit
argument shared with `proposition48ExactStabilizerPrimeBranchReduction`. That
theorem receives the twelve interfaces of
`Proposition48ExactStabilizerPrimeBranchReductionStatement`, numbered as in the
table of its Markdown, through their proofs in the Library:

| # | Interface | Proof (module) |
|---|---|---|
| 1 | `Proposition48MackeyFibreStatement` | `proposition48MackeyFibre` (`HarrisProposition48MackeyFibreProof`) |
| 2 | `Proposition48MackeyConstituentGaloisConjugateStatement` | `proposition48MackeyConstituentGaloisConjugate` (`HarrisProposition48MackeyGaloisProof`) |
| 3 | `Proposition48MackeyChildTransportStatement` | `proposition48MackeyChildTransport` (`HarrisProposition48MackeyChildTransportProof`) |
| 4 | `Proposition48PrimeInducedParameterStagesStatement` | `proposition48PrimeInducedParameterStages` (`HarrisProposition48PrimeInducedParameterStagesProof`) |
| 5 | `Proposition48PrimeInductionStagesStatement` | `proposition48PrimeInductionStages` (`HarrisProposition48PrimeInductionStagesProof`) |
| 6 | `Proposition48InducedParameterRegularAlgebraicStatement` | `proposition48InducedParameterRegularAlgebraic` (`HarrisProposition48InducedParameterRegularAlgebraicProof`) |
| 7 | `WeakInductionConjugateInverseSelfDualStatement` | `weakInductionConjugateInverseSelfDual` (`HarrisWeakInductionConjugateSelfDualProof`) |
| 8 | `Langlands.Automorphic.ArithmeticComapUnitaryCentralCharacterStatement` | `Langlands.Automorphic.arithmeticComapUnitaryCentralCharacter` (`Langlands.Automorphic.ArithmeticComapUnitaryCentralCharacterProof`) |
| 9 | `Langlands.Automorphic.ArithmeticComapSupercuspidalComponentStatement` | `Langlands.Automorphic.arithmeticComapSupercuspidalComponent` (`Langlands.Automorphic.ArithmeticComapSupercuspidalComponentProof`) |
| 10 | `ConjugateSelfDualUnitaryCentralCharacterStatement` | `conjugateSelfDualUnitaryCentralCharacter` (`HarrisConjugateSelfDualUnitaryCentralCharacterProof`) |
| 11 | `ConjugateSelfDualSupercuspidalConjPlaceStatement` | `conjugateSelfDualSupercuspidalConjPlace` (`HarrisConjugateSelfDualSupercuspidalConjPlaceProof`) |
| 12 | `SplitPlaceNeConjPlaceStatement` | `splitPlaceNeConjPlace` (`HarrisSplitPlaceNeConjPlaceProof`) |

In the table, modules without a prefix are in `Langlands.Global.Arithmetic`, and
declarations without a prefix are in `Langlands.Global.Harris`. Lean fixes their universe
parameters by unification: the number fields of a `Proposition48Problem` are in
`Type`, so the field universes are `0`, while the local-field universe is `uF` and
the carrier universe is `uV`.

The remaining inputs of the common argument are as follows.

- Interface 7 enters only through its conclusion after rigidity: the hypothesis
  `hcsd` of the common argument is
  `weakInductionConjugateInverseSelfDual hRig`, the self-duality interface applied
  to the premise `CuspidalSpectralRigidityStatement` of the target, in the
  unrestricted field scope of that premise.
- The common argument takes the totally complex forms
  `CyclicRegularInductionTCStatement` and
  `CyclicWeakInductionSupercuspidalTCStatement` of B2 and B4. The unrestricted
  premises B2 and B4 of the target specialize to them over totally complex fields
  by `fun F E _ _ _ _ _ _ _ _ _ => hB2 F E` (and the same for B4). The nine
  instance binders are those of the totally complex statement, and the instance
  `[NumberField.IsTotallyComplex F]` is ignored. The common argument applies B2 and
  B4 only at `F = Q.E`, a CM field.
- Restricted B7 and the bridge are passed unchanged.
- `Q`, `D` and the branch hypotheses are passed unchanged, except `Q.IsSpaced`.

The common argument, described step by step in
`HarrisProposition48ExactStabilizerPrimeBranchReductionProof.md`, uses
exact-stabilizer validity, the prime step, the orbit cardinality,
`HasDistinctMackeyComponents` and the child of the trivial double coset. In
outline:

- Interface 1 gives `D ≤ Q.conjugateField 1` and describes the Mackey double
  cosets as the fibres of restriction to `D`. Interface 3 transports the untwisted
  cuspidal solution of the child of the trivial double coset to a Mackey
  constituent `T₀` over `D`. Interfaces 10 and 8 give `T₀` a unitary central
  character (`HasUnitaryCentralCharacter`), the precise input that B2, B4 and
  restricted B7(2) use. Interfaces 9 and 11 make `T₀` supercuspidal at the places
  of `D` above `Q.Ps.v` and its complex conjugate.
- Interface 2 and `HasDistinctMackeyComponents` show that no nontrivial element of
  `Gal(D/Q.E)` fixes the class of `T₀`, so B2 gives a weak induction `Π` of `T₀`
  over `Q.E`.
- Interface 5 makes `Π` a weak automorphic induction of `Q.ξ`, `hcsd` makes it
  conjugate self-dual, and B4 makes it supercuspidal at `Q.Ps.v`.
- Interfaces 10–12 give the auxiliary conjugate pair. Restricted B7(2), with
  interfaces 3 and 4, gives the induced complex-place parameters of `Π`, and
  interface 6 with the bridge gives its regular algebraicity.

These conclusions together are `Q.HasParameterSolution`.

Theorem 1.2 with multiplicity, `Proposition48IsobaricInvarianceStatement`, B3 and
the hypothesis `Q.IsSpaced` are introduced and not used. In Harris's proof,
Theorem 1.2 enters the singleton case, through the argument of his Lemma 1.6, and
not the prime orbit. In Henniart's §§5.9–5.10 the theorem with multiplicity enters
only the descent case. The theorem with multiplicity is an outer premise of the
target, quantified over its own fields and representations before `Q` is
introduced, while `Q.IsSpaced` restricts the branch datum `Q`: it requires even real
degree of `Q.E` and weights of `Q.ξ` at distance at least two above every
archimedean place of `Q.E`. These conditions accommodate the field and
highest-weight hypotheses of the theorem with multiplicity in the descent argument.
The prime-orbit proof is independent of both the multiplicity premise and
`Q.IsSpaced`.

## Sources

- M. Harris, *The local Langlands conjecture for `GL(n)` over a `p`-adic field,
  `n < p`*, Invent. Math. 134 (1998), Proposition 4.8, proof in the case where the
  Mackey classes form a principal homogeneous space under `Gal(E_{t-1}/E)`,
  printed p. 203, and condition (4.12), printed p. 204. Registered
  `harris-1998-local-langlands`, SHA256
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`. Harris
  takes the automorphic induction `Π = AI_{E_{t-1}/E} Π(e, t-1)` of a base point
  (Arthur–Clozel, Lemma III.6.4), and obtains supercuspidality at the auxiliary
  place from Henniart–Herb, Proposition 5.5, because the conjugate local components
  are distinct. The differences of the Lean route from this argument are recorded
  in `HarrisProposition48ExactStabilizerPrimeBranchReductionProof.md`.
- G. Henniart, *Sur la conjecture de Langlands locale pour `GL_n`*, J. Théor.
  Nombres Bordeaux 13 (2001), §5.5, printed pp. 178–179, the theorem of Clozel and
  Kottwitz with multiplicity `a ≥ 1` that replaces Harris's Theorem 1.2, and
  §§5.9–5.10, printed pp. 180–181. Registered
  `henniart-2001-langlands-locale-gln-jtnb`, SHA256
  `c9db009ee2f2e561d834b9e1ef07a8b27ff40d0edd19546d3351f38f39b2dac5`. §5.9
  separates the passage from `j + 1` to `j` into two cases. The first is automorphic
  induction in the cyclic extension `F_{j+1}/F_j` (Arthur–Clozel III), which is the
  case of this branch and does not use the theorem of §5.5. The second is descent,
  and there §5.10 applies the theorem with multiplicity.

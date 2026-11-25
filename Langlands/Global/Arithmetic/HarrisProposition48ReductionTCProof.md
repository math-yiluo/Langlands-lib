# Proof of the totally complex reduction of Harris's Proposition 4.8

The theorem
`Langlands.Global.Harris.proposition48ReductionTC` has exactly the type
`Proposition48ReductionTCStatement.{uF, uV}` of
`Langlands.Global.Arithmetic.HarrisProposition48ReductionTCStatement`, for
arbitrary independent universes `uF` and `uV`. It consumes the published
conjunction of fourteen inputs, in which inputs 5, 6 and 9–14 are the
totally complex forms and inputs 1–4, 7 and 8 are unchanged, and concludes
the unchanged `Proposition48Statement.{uF, 0, 0, 0, uV}`. It adds no premise
and no axiom; the inspected axioms are `propext`, `Classical.choice` and
`Quot.sound`. None of the fourteen inputs is proved here, so this does not
by itself prove Harris's Proposition 4.8. No implication between this
statement and `Proposition48ReductionStatement` is used or proved.

## Route

The module imports
`Langlands.Global.Arithmetic.HarrisProposition48ReductionProof` and reuses
its two general theorems, whose paired Markdown gives the details.

* `Proposition48Problem.hasSolution_of_isAuxiliaryValid` is the strong
  induction on the normal-closure degree `Q.inductionDegree = [L : E]` of
  one-place valid problems. Rank one (`[E' : E] = 1`, after
  `0 < [E' : E]`) uses input 1. For `1 < [E' : E]`, input 4 supplies a
  prime cyclic step `D`, the alternative `Nat.card (Q.MackeyIndex D) = 1`
  or `= [D : E]`, and raw children of smaller degree at the parent's
  parity. Each child is normalized by input 2; its corrected problem
  `R.withCharacters (R.correctedCharacter ν) χs χs` changes only
  characters, so it has the same degree (`inductionDegree_withCharacters`,
  by `rfl`) and the induction hypothesis solves it; input 3 then untwists
  the solution to actual raw and corrected realizations. The theorem takes
  the branch as an abstract hypothesis receiving these child data.
* `proposition48_of_hasSolution` bundles an original datum of
  `Proposition48Statement` (using the datum's own `IsScalarTower`
  conjunct for the scalar tower instance), extracts auxiliary validity
  from the full datum, and returns `Q.HasSolution`, which is by definition
  the original four-part output: weak automorphic induction of `ξ`,
  regular algebraicity, conjugate self-duality and supercuspidality at
  `Ps.v`.

## The branch hypothesis

`proposition48ReductionTC` destructures the fourteen conjuncts and
discharges the branch hypothesis by cases on the cardinality alternative:

* `Nat.card (Q.MackeyIndex D) = 1`: input 6,
  `Proposition48SingletonBranchTCStatement`, applied to input 7
  (`Harris1998Theorem12CuspidalStatement`), input 9
  (`CuspidalSpectralRigidityTCStatement`), input 10
  (`Proposition48IsobaricInvarianceTCStatement`) and input 13
  (`CyclicStableDescentTCStatement`), then to `Q`, `D`, the validity, the
  prime cyclic step, the cardinality equation and the child data.
* `Nat.card (Q.MackeyIndex D) = [D : E]`: input 5,
  `Proposition48PrimeBranchTCStatement`, applied to inputs 7, 8
  (`HarrisSupercuspidalLocalComparisonStatement`), 9, 10, 11
  (`CyclicRegularInductionTCStatement`), 12
  (`CyclicRegularOrbitLiftTCStatement`) and 14
  (`CyclicWeakInductionSupercuspidalTCStatement`), then to the same data.

The bodies of the totally complex branch statements are identical to those
of the original branches; only their foundational premises differ, so the
same child data fit them. The reduction passes the foundational inputs to
the branches and applies no foundational input over a particular field
itself.

## Provenance

This is the totally complex form, described in the paired Markdown of
`Proposition48ReductionTCStatement`, of the derived organizational
reduction of M. Harris, *The local Langlands conjecture for GL(n) over a
p-adic field, n < p*, Invent. Math. 134 (1998), 177–210
(`harris-1998-local-langlands`), Proposition 4.8 and its proof, printed
pp.201–203 (`math_9611226v1.tex` lines 1574–1674). Nothing about Theorems
1.2 or 1.7, Arthur–Clozel or Henniart–Herb is proved.

# The totally complex cuspidal-pair functional equation from its three parts

Author: Worker 1009. Proof for Task 7359 (`83c0699f-0ef4-46d6-ab50-724622d702a5`),
revision 1. This is link 1 of the totally complex chain published under Task 0 after the
operator's answer `81ed24709e7050068786116ca6613260` (Option A).

## Statement proved

`Langlands.Global.cuspidalPairFunctionalEquationReductionTC :
CuspidalPairFunctionalEquationReductionTCStatement.{u, uQ}` proves the Library statement
`Langlands.Global.CuspidalPairFunctionalEquationReductionTCStatement` (module
`Langlands.Automorphic.AssociatedFactorTCReductionStatement`). The two universe levels `u`
and `uQ` are arbitrary and independent, and the theorem adds no hypothesis. The statement is
the implication

```lean
CuspidalPairLocalDataStatement.{u, uQ} →
  CuspidalArchimedeanParameterExistenceTCStatement.{u} →
    CuspidalPairCompletedEquationTCStatement.{u, uQ} →
      CuspidalPairGlobalFunctionalEquationTCStatement.{u, uQ}
```

In words: assume three things.

1. The local data of cuspidal pairs exist (`CuspidalPairLocalDataStatement`, module
   `Langlands.Global.Factors.CuspidalPairFunctionalEquationReduction`). This premise is stated
   over every number field.
2. Every actual cuspidal realization over a totally complex number field has archimedean
   parameters (`CuspidalArchimedeanParameterExistenceTCStatement`).
3. The completed equation holds over totally complex number fields for every admissible
   finite set of finite places (`CuspidalPairCompletedEquationTCStatement`).

Then the completed Rankin–Selberg functional equation of cuspidal pairs holds over every
totally complex number field (`CuspidalPairGlobalFunctionalEquationTCStatement`). The three
totally complex propositions are in module
`Langlands.Global.Factors.CuspidalPairFunctionalEquationTCStatement`. Each is the published
unrestricted proposition with the instance argument `[NumberField.IsTotallyComplex F]` inserted
after `[NumberField F]`. Their clauses are explained in
`CuspidalPairFunctionalEquationTCStatement.md` §1 and `CuspidalPairFunctionalEquationReduction.md`
§1.

## Proof

The Lean proof is a direct tactic proof. It copies the published proof of the unrestricted
reduction `cuspidalPairFunctionalEquationReduction` (module
`Langlands.Global.Factors.CuspidalPairFunctionalEquationReduction`) and introduces one more
instance argument. It imports only the target's module
`Langlands.Automorphic.AssociatedFactorTCReductionStatement` and calls no other theorem.

1. **Introduce the data.** Name the three premises `hLD`, `hC` and `hE`. Then introduce the
   hypotheses of the conclusion: the field `F` with its four instances (`Field`, `NumberField`,
   `NumberField.IsTotallyComplex` and `CompactSpace (AdeleQuotient F)`), the additive
   character `ψ` with its nontriviality `hψ` and its triviality on `F` (`hdiag`), the ranks
   `r` and `t`, the realizations `T`, `Td`, `T'`, `Td'` with their contragredient hypotheses,
   the spectral presentations `P`, `P'`, `Pd`, `Pd'` and the witnesses `h`, `h'`, `hd`, `hd'`
   of irreducible admissible components.
2. **Local data.** `hLD` is applied to these data. It gives a nonempty set of finite factor
   choices (`hne`), an additive component of `ψ` at every real place (`hRa`) and at every
   complex place (`hCa`), and a finite set `S` of finite places. `S` contains the four
   exceptional sets (`hP`, `hP'`, `hPd`, `hPd'`) and supports `ψ` (`hsupp`), and every finite
   factor choice is unramified outside `S` (`hun`). The premise is unrestricted, so it applies
   at the totally complex `F`; the extra instance plays no role.
3. **Local clauses of the conclusion.** The first conjunct of the conclusion is built from
   these facts. Its nonemptiness clause is `hne`. At a real place `v`, its clause is `hRa v`
   together with the real-place parameters `(hC F r T).1 v`, `(hC F t T').1 v`,
   `(hC F r Td).1 v` and `(hC F t Td').1 v` of the four realizations. At a complex place, it
   is `hCa v` with the second components `(hC F r T).2 v`, … . Each application of `hC` is at
   the given `F`; Lean finds the instance `[NumberField.IsTotallyComplex F]` from the context.
4. **The finite set.** The witness of the existential is `S`, with the containments `hP`,
   `hP'`, `hPd`, `hPd'` and the support `hsupp`. For each finite factor choice `c`, the
   unramified clause is `hun c`.
5. **Completed equation.** It remains to show, for each `c`, the completed equation for every
   choice of archimedean data. The proof introduces the components `aR`, `aC` of `ψ` with
   their hypotheses `haR`, `haC`, and the real parameters `dR`, `dR'`, `dRd`, `dRd'` and
   complex parameters `dC`, `dC'`, `dCd`, `dCd'` of the four realizations with their
   hypotheses. The goal is then `hE` applied to all the data, to `S` and its hypotheses, and
   to `c` with `hun c`. Its archimedean factors `infiniteL`, `dualInfiniteL` and
   `infiniteEpsilon` are written verbatim in both the premise and the conclusion, so the
   application closes the goal.

The proof does not use that a totally complex field has no real place. The real-place clauses
are proved from the premises in the same way as the complex-place clauses.

## Check

A private `lean_check` of this module, with declaration inspection, reported 0 errors and 0
warnings. The theorem has universe parameters `u` and `uQ` and depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Provenance

Provenance: *derived*. The target is the totally complex form of the published
`CuspidalPairFunctionalEquationReductionStatement`, and the proof is the published proof of
`cuspidalPairFunctionalEquationReduction` with one more instance introduced. The proof is pure
logic: it applies the three premises and uses no further mathematical result. For the sources of
the propositions, see `CuspidalPairFunctionalEquationStatement.md`,
`CuspidalPairFunctionalEquationReduction.md`, `CuspidalPairFunctionalEquationTCStatement.md` and
`AssociatedFactorTCReductionStatement.md`.

# Proof of the local data statement for cuspidal pairs

Author: Worker 4891.

`Langlands.Global.cuspidalPairLocalData.{u, uQ}` proves the unchanged proposition
`Langlands.Global.CuspidalPairLocalDataStatement.{u, uQ}` of
`CuspidalPairFunctionalEquationReduction.lean` (Worker 5013), for independent
universes `u` and `uQ`. That proposition is the local-data input of the reduction of
`CuspidalPairGlobalFunctionalEquationStatement`. Under the target's hypotheses it
asserts that a finite pair factor choice exists, that `ψ` has an additive component
at every real and every complex place, and that one finite set `S` of finite places
contains the four exceptional sets, satisfies `FiniteAdditiveSupport ψ S`, and is a
set outside which every finite factor choice is unramified.

The proof introduces the hypotheses and returns the four conjuncts from
`CuspidalPairFiniteLayer.lean`:

- `nonempty_finitePairFactorChoice ψ hdiag P P' Pd Pd' h h' hd hd'`;
- `exists_isRealAdditiveComponent ψ hdiag`;
- `exists_isComplexAdditiveComponent ψ hdiag`;
- `exists_isUnramifiedOutside ψ hdiag P P' Pd Pd' h h' hd hd'`, which supplies `S`
  with the four inclusions, the additive support and unramifiedness for every
  factor choice.

Only the triviality of `ψ` on `F` (`hdiag`) is used. The nontriviality of `ψ` and the
two contragredient hypotheses are introduced and not used. See
`CuspidalPairFiniteLayer.md` and `../../Correspondence/UnramifiedPairFactors.md` for
the proofs of these theorems and their sources (Cogdell 2004, Theorem 3.3; Getz–Hahn
2024, Section 11.6).

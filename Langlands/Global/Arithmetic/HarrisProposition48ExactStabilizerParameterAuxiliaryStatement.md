# Rank one and untwisting of complex-place parameters in Proposition 4.8

Module `Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerParameterAuxiliaryStatement`,
namespace `Langlands.Global.Harris`.

The module declares `universe uF uV` and sets `autoImplicit false`. Both
declarations are closed proposition definitions with universes `.{uF, uV}`
and result `Prop`. The rank index `r : ℕ` means `GL_(r+1)`; rank one is
`r = 0`.

Two unproved statements for the exact-stabilizer form of the induction for
Harris 1998, Proposition 4.8, in which solutions carry the complex-place
parameters of the induced representation (predicates of the sibling module
`HarrisProposition48ExactStabilizerParameterData`). **Neither is proved here.**
They take the place of the published rank-one statement
(`Proposition48AuxiliaryRankOneStatement`) and complement the published
untwist statement (`Proposition48AuxiliaryParityUntwistStatement`), which the
exact-stabilizer reduction still uses unchanged.

## `Proposition48ExactStabilizerAuxiliaryRankOneStatement.{uF, uV}`

```lean
∀ Q : Proposition48Problem.{uF}, Q.IsAuxiliaryValid →
  Module.finrank Q.E Q.E' = 1 → Q.HasParameterSolution.{uF, uV}
```

This is `Proposition48AuxiliaryRankOneStatement` with the conclusion
`Q.HasSolution.{uF, uV}` strengthened to
`Q.HasParameterSolution.{uF, uV}`. Every other premise, binder and universe
is unchanged. The hypothesis is
the published general-position validity, not exact-stabilizer validity. The
exact-stabilizer validity implies it
(`IsAuxiliaryExactStabilizerValid.isAuxiliaryValid`), so the statement as
given is the stronger one, and the reduction applies it to exact-stabilizer
problems.

*Why it should hold.* If `[E' : E] = 1`, `ξ` is (through `E ≅ E'`) a Hecke
character of `E`, algebraic at parity `0`, conjugate inverse and with a
component at the auxiliary place. Its realization on `GL(1)` is a cuspidal
class that is a weak induction of `ξ`, regular algebraic, conjugate self-dual
and supercuspidal at `Q.Ps.v` (every irreducible representation of `GL(1)`
is supercuspidal), as for the published rank-one statement. At a complex place
`v` of `E` its parameter is the one-block list of the parameter of `ξ` at the
unique place of `E'` above `v`, which is the induced parameter. The proof
must show that the Hecke character has a parameter at each complex place and
that the `GL(1)` class has the same one. No rigidity premise is needed,
because the statement only asserts existence.

## `Proposition48ExactStabilizerParameterUntwistStatement.{uF, uV}`

```lean
∀ (Q : Proposition48Problem.{uF}) (b : ℕ) (ν : HeckeCharacter Q.E)
  (χs : FieldCharacter Q.F Q.F'), Q.IsAuxiliaryValidAtParity b →
  Q.IsAuxiliaryParityNormalization b ν χs →
  ∀ (r : ℕ) (S T : CuspidalOperatorRealization Q.E r),
    Q.IsUntwistedSolution.{uF, uV} ν S T →
    (Q.withCharacters (Q.correctedCharacter ν) χs χs).HasInducedComplexPlaceParameters
        T.isoClass →
      Q.HasInducedComplexPlaceParameters S.isoClass
```

This is an additional statement with no published counterpart, rather than a
replacement of `Proposition48AuxiliaryParityUntwistStatement`. It takes the
same `Q`, `b`, `ν`, `χs`, validity and normalization data, followed by `r` and
actual realizations `S T : CuspidalOperatorRealization Q.E r`. It assumes the
`IsUntwistedSolution.{uF, uV}` relation that the published untwist statement
produces. Its further premise and conclusion add parameter transport: if `T`
has the complex-place parameters induced from the corrected character
`ξ · (ν ∘ N)`, then `S` has those induced from `ξ`. There are no suppressed
binders or further premises. As with rank one, the published
`IsAuxiliaryValidAtParity b` is retained;
`IsAuxiliaryExactStabilizerValidAtParity.isAuxiliaryValidAtParity` supplies it
in the exact-stabilizer reduction.

*Why it should hold.* `IsUntwistedSolution` contains
`IsDeterminantMultiple ν S T`: the automorphic functions of `T` are those of
`S` multiplied by `ν(det g)`. So at a complex place `v` the parameter of `S`
is that of `T` with each block twisted by the inverse of the parameter of `ν`
at `v`. The corrected character at a place `w` of `E'` above `v` has the
parameter of `ξ` at `w` times that of `ν` at `v`, read in the coordinates of
`w`. Twisting the induced parameter of the corrected character back block by
block gives the induced parameter of `ξ`, up to the same permutation. The
proof must establish the twisting rule for `HasComplexPlaceParameter`, the
parameter of `ν ∘ N` at `w`, and the compatibility of the twist with
`complexPlaceParameterTransport`.

## Sources

M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
n < p*, Invent. Math. 134 (1998), 177–210, source `harris-1998-local-langlands`,
Proposition 4.8, printed p.201, and its proof, pp.201–203: the degree-one start
of the induction; compare the algebraic parity convention on printed p.195.
Condition (4.12) is in the proof
of Lemma 4.7, printed p.204.

Design: source `operator-external-inputs-plan-2026-11-16`,
`external-inputs-plan.tex`, Section 2.2 (B5–B7, TeX lines 196–199) and
Section 4.8 (Remark 4.2, lines 859–894; the branch and infinity-type
paragraphs, lines 908–912), and the
[operator's R2 ruling](/home/taskhub/pilot/correspondence/a79e2e832569567a8582b3c994f2fc1b.md),
answer to request `c292736a05f55d4fba67d1a01b7fb2e2`.

The parameter predicates and both statements here are internal interfaces of
R2, not statements of Harris. They supply the start and parity transport for
an induction in which solutions carry induced complex-place parameters.
Regular algebraicity at a prime step is intended to come from restricted
B7(2), the children's parameters and the bridge, and at a singleton step
from restricted B7(1) and the bridge. These two auxiliary statements provide
the parameter data that this route requires; they assert no such branch
compatibility. The rank-one statement asks only for existence of one solution
with parameters, so no endpoint theorem about every solution beyond rank
one is included.

## Status

Proposition definitions only. Neither statement is proved here, and no
published declaration is changed.

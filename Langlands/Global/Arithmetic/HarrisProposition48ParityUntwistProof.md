# Proof: two-place determinant untwisting in Harris, Proposition 4.8

Module `Langlands.Global.Arithmetic.HarrisProposition48ParityUntwistProof`. The theorem

```lean
theorem Langlands.Global.Harris.proposition48ParityUntwist :
    Proposition48ParityUntwistStatement.{uF, uV}
```

proves `Proposition48ParityUntwistStatement` (module `HarrisProposition48ParityStatement`) at an
arbitrary local-field universe `uF` and local-factor carrier universe `uV`. Unfolded, the
statement is

```lean
∀ (Q : Proposition48Problem.{uF}) (b : ℕ) (ν : HeckeCharacter Q.E)
  (χ χs : FieldCharacter Q.F Q.F'), Q.IsValidAtParity b →
  Q.IsParityNormalization b ν χ χs →
  ∀ (r : ℕ) (c : CuspidalOperatorRealization.IsoClass Q.E r),
    (Q.withCharacters (Q.correctedCharacter ν) χ χs).IsSolution.{uF, uV} c →
    ∃ S T : CuspidalOperatorRealization Q.E r,
      T.isoClass = c ∧ Q.IsUntwistedSolution.{uF, uV} ν S T
```

In words: let `Q` be a Proposition 4.8 problem valid at the parity `b` and `(ν, χ, χs)` a parity
normalization of it. For every cuspidal class `c` solving the corrected problem there are actual
cuspidal realizations `S`, `T` of the same rank with `T` in the class `c` and
`IsUntwistedSolution ν S T`: `T` is obtained from `S` by multiplication by `ν(det g)`, `S` is a
weak automorphic induction of the raw character, conjugate self-dual and supercuspidal at the
designated place, and `T` is regular algebraic.

## Proof as implemented

The proof is a single term of two Library theorems.

1. `proposition48ParityUntwistReduction.{uF, uV}` (module
   `HarrisProposition48ParityUntwistReductionProof`) proves
   `Proposition48ParityUntwistReductionStatement.{uF, uV}`, the implication
   `Proposition48AuxiliaryParityUntwistStatement.{uF, uV} →
   Proposition48ParityUntwistStatement.{uF, uV}`. It projects the full validity and
   normalization to the auxiliary ones; the solution predicate and the untwisted-solution
   predicate depend only on the corrected inducing character and the auxiliary place.
2. `proposition48AuxiliaryParityUntwist.{uF, uV}` (module
   `HarrisProposition48AuxiliaryParityUntwistProof`) proves
   `Proposition48AuxiliaryParityUntwistStatement.{uF, uV}`, the untwisting at the auxiliary place.

## Declarations

- `proposition48ParityUntwist : Proposition48ParityUntwistStatement.{uF, uV}` (theorem).

## Provenance

M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field, n < p*, Invent. Math.
134 (1998), 177–210, registered as `harris-1998-local-langlands` (PDF page = printed page − 176):
Proposition 4.8, printed p. 201 (PDF page 25), and its proof, printed pp. 201–203 (PDF pages
25–27); printed p. 195 (PDF page 19) and printed p. 191 (PDF page 15) for the parity of the
infinity type and the half-integer twists. The untwisting by a genuine determinant twist on
actual realizations is a derived formulation of the proof route, not a statement of Harris.

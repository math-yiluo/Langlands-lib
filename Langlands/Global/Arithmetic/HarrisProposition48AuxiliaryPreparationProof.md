# Proof: the one-place preparation for Harris, Proposition 4.8

Module `Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryPreparationProof`. The theorem

```lean
theorem Langlands.Global.Harris.proposition48AuxiliaryPreparation :
    Proposition48AuxiliaryPreparationStatement.{uF, uV}
```

proves `Proposition48AuxiliaryPreparationStatement` (module
`HarrisProposition48AuxiliaryInputStatement`) at an arbitrary local-field universe `uF` and
local-factor carrier universe `uV`. The statement is the conjunction

```lean
Proposition48AuxiliaryRankOneStatement.{uF, uV} ∧
  Proposition48AuxiliaryParityNormalizationStatement.{uF} ∧
  Proposition48AuxiliaryParityUntwistStatement.{uF, uV}
```

whose three parts, unfolded, are

```lean
-- Proposition48AuxiliaryRankOneStatement.{uF, uV}
∀ Q : Proposition48Problem.{uF}, Q.IsAuxiliaryValid →
  Module.finrank Q.E Q.E' = 1 → Q.HasSolution.{uF, uV}
-- Proposition48AuxiliaryParityNormalizationStatement.{uF}
∀ (Q : Proposition48Problem.{uF}) (b : ℕ), Q.IsAuxiliaryValidAtParity b →
  ∃ (ν : HeckeCharacter Q.E) (χs : FieldCharacter Q.F Q.F'),
    Q.IsAuxiliaryParityNormalization b ν χs
-- Proposition48AuxiliaryParityUntwistStatement.{uF, uV}
∀ (Q : Proposition48Problem.{uF}) (b : ℕ) (ν : HeckeCharacter Q.E)
  (χs : FieldCharacter Q.F Q.F'), Q.IsAuxiliaryValidAtParity b →
  Q.IsAuxiliaryParityNormalization b ν χs →
  ∀ (r : ℕ) (c : CuspidalOperatorRealization.IsoClass Q.E r),
    (Q.withCharacters (Q.correctedCharacter ν) χs χs).IsSolution.{uF, uV} c →
    ∃ S T : CuspidalOperatorRealization Q.E r,
      T.isoClass = c ∧ Q.IsUntwistedSolution.{uF, uV} ν S T
```

In words: the base case and the two parity obligations of the internal one-place induction for
Harris, Proposition 4.8. The rank-one case `[E' : E] = 1` of a problem valid at the auxiliary
place has a solution (Hecke-character realization); every problem valid at the auxiliary place
for a parity `b` has a parity normalization `(ν, χs)`; and every corrected solution class can be
untwisted to actual realizations `S`, `T` with `T = S ⊗ (ν ∘ det)`.

## Proof as implemented

The proof is the anonymous constructor of the conjunction applied to three Library theorems:

1. `proposition48AuxiliaryRankOne.{uF, uV}` (module `HarrisProposition48AuxiliaryRankOneProof`)
   proves `Proposition48AuxiliaryRankOneStatement.{uF, uV}`;
2. `proposition48AuxiliaryParityNormalization.{uF}` (module
   `HarrisProposition48AuxiliaryParityNormalizationProof`) proves
   `Proposition48AuxiliaryParityNormalizationStatement.{uF}`;
3. `proposition48AuxiliaryParityUntwist.{uF, uV}` (module
   `HarrisProposition48AuxiliaryParityUntwistProof`) proves
   `Proposition48AuxiliaryParityUntwistStatement.{uF, uV}`.

## Declarations

- `proposition48AuxiliaryPreparation : Proposition48AuxiliaryPreparationStatement.{uF, uV}`
  (theorem).

## Provenance

M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field, n < p*, Invent. Math.
134 (1998), 177–210, registered as `harris-1998-local-langlands` (PDF page = printed page − 176):
Proposition 4.8, printed p. 201 (PDF page 25); in its proof, printed p. 202 (PDF page 26), the
induction on `t` starts at `i = 0`, "since in this case `n(a, i) = 1` for all `a ∈ A_i`" (the
rank-one case), and the inherited hypotheses (i)–(iii) are listed; printed p. 195 (PDF page 19),
the parity condition `a(v) ≡ n − 1 (mod 2)` on the infinity type. The one-place scope and the
parity normalization and untwisting are derived formulations of the proof route, not statements
of Harris.

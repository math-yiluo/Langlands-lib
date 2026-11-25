# Proof: the two-place parity transport for Harris, Proposition 4.8

Module `Langlands.Global.Arithmetic.HarrisProposition48ParityTransportProof`. The theorem

```lean
theorem Langlands.Global.Harris.proposition48ParityTransport :
    Proposition48ParityTransportStatement.{uF, uV}
```

proves `Proposition48ParityTransportStatement` (module `HarrisProposition48ParityStatement`) at an
arbitrary local-field universe `uF` and local-factor carrier universe `uV`. The statement is the
conjunction

```lean
Proposition48ParityNormalizationStatement.{uF} ∧ Proposition48ParityUntwistStatement.{uF, uV}
```

whose two parts, unfolded, are

```lean
-- Proposition48ParityNormalizationStatement.{uF}
∀ (Q : Proposition48Problem.{uF}) (b : ℕ), Q.IsValidAtParity b →
  ∃ (ν : HeckeCharacter Q.E) (χ χs : FieldCharacter Q.F Q.F'),
    Q.IsParityNormalization b ν χ χs
-- Proposition48ParityUntwistStatement.{uF, uV}
∀ (Q : Proposition48Problem.{uF}) (b : ℕ) (ν : HeckeCharacter Q.E)
  (χ χs : FieldCharacter Q.F Q.F'), Q.IsValidAtParity b →
  Q.IsParityNormalization b ν χ χs →
  ∀ (r : ℕ) (c : CuspidalOperatorRealization.IsoClass Q.E r),
    (Q.withCharacters (Q.correctedCharacter ν) χ χs).IsSolution.{uF, uV} c →
    ∃ S T : CuspidalOperatorRealization Q.E r,
      T.isoClass = c ∧ Q.IsUntwistedSolution.{uF, uV} ν S T
```

In words: every Proposition 4.8 problem valid at a parity `b` has a parity normalization
`(ν, χ, χs)` by a genuine conjugate-inverse base character, and every cuspidal class solving the
corrected problem is realized by `T = S ⊗ (ν ∘ det)` for an actual realization `S` solving the raw
problem.

## Proof as implemented

The proof is the anonymous constructor of the conjunction applied to two Library theorems:

1. `proposition48ParityNormalization.{uF}` (module `HarrisProposition48ParityNormalizationProof`)
   proves `Proposition48ParityNormalizationStatement.{uF}`;
2. `proposition48ParityUntwist.{uF, uV}` (module `HarrisProposition48ParityUntwistProof`) proves
   `Proposition48ParityUntwistStatement.{uF, uV}`.

## Declarations

- `proposition48ParityTransport : Proposition48ParityTransportStatement.{uF, uV}` (theorem).

## Provenance

M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field, n < p*, Invent. Math.
134 (1998), 177–210, registered as `harris-1998-local-langlands` (PDF page = printed page − 176):
Proposition 4.8, printed p. 201 (PDF page 25), and its proof, printed pp. 201–203 (PDF pages
25–27); printed p. 195 (PDF page 19), the infinity type with `a(v) ≡ n − 1 (mod 2)`; printed
p. 191 (PDF page 15), automorphic induction up to a half-integer power of the absolute value.
The split into parity correction and determinant untwisting is a derived formulation of the proof
route, not a statement of Harris.

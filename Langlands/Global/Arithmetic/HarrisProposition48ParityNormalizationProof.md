# Proof: two-place parity normalization in Harris, Proposition 4.8

Module `Langlands.Global.Arithmetic.HarrisProposition48ParityNormalizationProof`. The theorem

```lean
theorem Langlands.Global.Harris.proposition48ParityNormalization :
    Proposition48ParityNormalizationStatement.{uF}
```

proves `Proposition48ParityNormalizationStatement` (module `HarrisProposition48ParityStatement`)
at an arbitrary local-field universe `uF`. Unfolded, the statement is

```lean
∀ (Q : Proposition48Problem.{uF}) (b : ℕ), Q.IsValidAtParity b →
  ∃ (ν : HeckeCharacter Q.E) (χ χs : FieldCharacter Q.F Q.F'),
    Q.IsParityNormalization b ν χ χs
```

In words: for every bundled Proposition 4.8 problem `Q` valid at the parity `b` (at both the
primary and the auxiliary place), there are a genuine Hecke character `ν` of the base field and
new local characters `χ`, `χs` on the same local extension such that `IsParityNormalization` holds:
`ν` is conjugate-inverse, has the correcting infinity parity, is trivial when the parities agree,
and the corrected character `ξ · (ν ∘ N_{E'/E})` satisfies all original validity conditions,
including relative regularity, the actual local components `χ`, `χs` and general position.

## Proof as implemented

The proof is a single term of three Library theorems.

1. `proposition48ParityNormalizationReduction.{uF}` (module
   `HarrisProposition48ParityNormalizationReductionProof`) proves
   `Proposition48ParityNormalizationReductionStatement.{uF}`, the implication
   `Proposition48AuxiliaryParityNormalizationStatement.{uF} →
   Proposition48PlaceNormTwistStatement.{uF} → Proposition48ParityNormalizationStatement.{uF}`.
   It projects full validity to auxiliary validity, takes `ν` and the corrected auxiliary
   component from the auxiliary normalization, transports the component at the primary place with
   the same `ν`, and reassembles full validity.
2. `proposition48AuxiliaryParityNormalization.{uF}` (module
   `HarrisProposition48AuxiliaryParityNormalizationProof`) proves
   `Proposition48AuxiliaryParityNormalizationStatement.{uF}`, the normalization at the auxiliary
   place.
3. `proposition48PlaceNormTwist.{uF}` (module `HarrisProposition48PlaceNormTwistProof`) proves
   `Proposition48PlaceNormTwistStatement.{uF}`, the transport of an actual local component by the
   norm correction at a compatible place.

## Declarations

- `proposition48ParityNormalization : Proposition48ParityNormalizationStatement.{uF}` (theorem).

## Provenance

M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field, n < p*, Invent. Math.
134 (1998), 177–210, registered as `harris-1998-local-langlands` (PDF page = printed page − 176):
Proposition 4.8, printed p. 201 (PDF page 25), and its proof, printed pp. 201–203 (PDF pages
25–27); printed p. 195 (PDF page 19), the infinity type with `a(v) ≡ n − 1 (mod 2)`; printed
p. 191 (PDF page 15), automorphic induction up to a half-integer power of the absolute value.
These passages motivate the normalization; the correction by a genuine conjugate-inverse base
character, preserving all validity conditions, is a derived formulation of the proof route and is
not stated verbatim by Harris.

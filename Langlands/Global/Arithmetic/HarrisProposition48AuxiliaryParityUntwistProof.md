# Proof: auxiliary-place determinant untwisting in Harris, Proposition 4.8

Module `Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryParityUntwistProof`. The theorem

```lean
theorem Langlands.Global.Harris.proposition48AuxiliaryParityUntwist :
    Proposition48AuxiliaryParityUntwistStatement.{uF, uV}
```

proves `Proposition48AuxiliaryParityUntwistStatement` (module
`HarrisProposition48AuxiliaryInputStatement`) at an arbitrary local-field universe `uF` and
local-factor carrier universe `uV`. Unfolded, the statement is

```lean
∀ (Q : Proposition48Problem.{uF}) (b : ℕ) (ν : HeckeCharacter Q.E)
  (χs : FieldCharacter Q.F Q.F'), Q.IsAuxiliaryValidAtParity b →
  Q.IsAuxiliaryParityNormalization b ν χs →
  ∀ (r : ℕ) (c : CuspidalOperatorRealization.IsoClass Q.E r),
    (Q.withCharacters (Q.correctedCharacter ν) χs χs).IsSolution.{uF, uV} c →
    ∃ S T : CuspidalOperatorRealization Q.E r,
      T.isoClass = c ∧ Q.IsUntwistedSolution.{uF, uV} ν S T
```

In words: let `Q` be a Proposition 4.8 problem valid at the auxiliary place for the parity `b`,
and `(ν, χs)` a parity normalization of it. For every cuspidal class `c` of rank `r + 1` that
solves the corrected problem (inducing character `ξ · (ν ∘ N_{E'/E})`, auxiliary character `χs`),
there are actual cuspidal realizations `S` and `T` of the same rank with `T` in the class `c` and
`IsUntwistedSolution ν S T`: the automorphic functions of `T` are those of `S` multiplied by
`ν(det g)`, `S` is a weak automorphic induction of the raw character `ξ`, conjugate self-dual and
supercuspidal at the auxiliary place, and `T` is regular algebraic.

## Proof as implemented

The proof is a single term: the Library reduction
`proposition48AuxiliaryParityUntwistReduction.{uF, uV}` (module
`HarrisProposition48AuxiliaryParityUntwistReductionProof`), which proves
`Proposition48AuxiliaryParityUntwistReductionStatement.{uF, uV}`, applied to its three premises,
each a Library theorem:

1. `heckeDeterminantTwistWeakInduction.{0, uV}` (module
   `Langlands.Automorphic.HeckeDeterminantTwistWeakInductionProof`):
   `HeckeDeterminantTwistWeakInductionStatement.{0, uV}`, the twisted presentation is a weak
   automorphic induction of the inducing character times the norm pullback of the twisting
   character.
2. `heckeDeterminantTwistConjugateSelfDual.{0}` (module
   `Langlands.Automorphic.HeckeDeterminantTwistConjugateSelfDualProof`):
   `HeckeDeterminantTwistConjugateSelfDualStatement.{0}`, a conjugate-inverse Hecke character
   preserves conjugate self-duality under the determinant twist.
3. `heckeDeterminantTwistSupercuspidal.{0, uV}` (module
   `Langlands.Automorphic.HeckeDeterminantTwistSupercuspidalProof`):
   `HeckeDeterminantTwistSupercuspidalStatement.{0, uV}`, the twisted presentation is
   supercuspidal wherever the original one is.

The reduction takes a representative `T` of `c` and `S = T.heckeDeterminantTwist ν⁻¹`, and
transports weak induction, conjugate self-duality and the supercuspidal component from `T` to `S`
by the three premises applied to `ν⁻¹`. It fixes the number field of the premises in `Type 0`.

## Declarations

- `proposition48AuxiliaryParityUntwist : Proposition48AuxiliaryParityUntwistStatement.{uF, uV}`
  (theorem).

## Provenance

M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field, n < p*, Invent. Math.
134 (1998), 177–210, registered as `harris-1998-local-langlands` (PDF page = printed page − 176):
Proposition 4.8, printed p. 201 (PDF page 25), and its proof, printed pp. 201–203 (PDF pages
25–27), by induction on the cyclic tower; printed p. 195 (PDF page 19), the parity condition
`a(v) ≡ n − 1 (mod 2)` on the infinity type; printed p. 191 (PDF page 15), automorphic induction
up to twisting by a half-integer power of the absolute value. The untwisting by a genuine
determinant twist on actual realizations is a derived formulation of the proof route, not a
statement of Harris.

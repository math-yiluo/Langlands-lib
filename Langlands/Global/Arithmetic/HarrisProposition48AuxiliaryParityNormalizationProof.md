# Proof: auxiliary-place parity normalization in Harris, Proposition 4.8

Module `Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryParityNormalizationProof`. The
theorem

```lean
theorem Langlands.Global.Harris.proposition48AuxiliaryParityNormalization :
    Proposition48AuxiliaryParityNormalizationStatement.{uF}
```

proves `Proposition48AuxiliaryParityNormalizationStatement` (module
`HarrisProposition48AuxiliaryInputStatement`) at an arbitrary local-field universe `uF`.
Unfolded, the statement is

```lean
∀ (Q : Proposition48Problem.{uF}) (b : ℕ), Q.IsAuxiliaryValidAtParity b →
  ∃ (ν : HeckeCharacter Q.E) (χs : FieldCharacter Q.F Q.F'),
    Q.IsAuxiliaryParityNormalization b ν χs
```

In words: for every bundled Proposition 4.8 problem `Q` that satisfies the one-place validity
conditions at the auxiliary place for the infinity parity `b`, there are a genuine Hecke
character `ν` of the base field `E` and a new auxiliary local character `χs` such that
`IsAuxiliaryParityNormalization b ν χs` holds: `ν` is conjugate-inverse, has the correcting
infinity parity `(b + ([E':E] − 1)) % 2`, is trivial when the inherited and rank parities agree,
and the corrected inducing character `ξ · (ν ∘ N_{E'/E})` (actual idele-class norm) gives a
problem with full one-place validity at its own rank parity, with the prescribed auxiliary
component `χs` and local general position.

## Proof as implemented

The proof is a single term: the Library reduction
`proposition48AuxiliaryParityNormalizationReduction.{uF}` (module
`HarrisProposition48AuxiliaryParityNormalizationReductionProof`), which proves
`Proposition48AuxiliaryParityNormalizationReductionStatement.{uF}`, applied to its four premises,
each a Library theorem:

1. `normTwistInfinity.{0}` (module `HarrisNormTwistInfinityProof`):
   `NormTwistInfinityStatement.{0}`, twisting by a norm pullback adds the infinity exponents and
   preserves relative regularity.
2. `cmNormConjugation.{0, 0}` (module `HarrisCMNormConjugationProof`):
   `CMNormConjugationStatement.{0, 0}`, the actual idele-class norm commutes with CM conjugation.
3. `proposition48PlaceNormTwist.{uF}` (module `HarrisProposition48PlaceNormTwistProof`):
   `Proposition48PlaceNormTwistStatement.{uF}`, the norm correction transports an actual local
   component at a compatible place, changing its Weil character by the restriction of a base Weil
   character.
4. `generalPositionAmbientTwist.{uF}` (module `HarrisGeneralPositionAmbientTwistProof`):
   `GeneralPositionAmbientTwistStatement.{uF}`, an ambient character twist preserves the
   irreducibility of all Mackey constituents in the same prime cyclic tower.

The reduction fixes the number fields of the first two premises in `Type 0`, hence the
universes `0` and `0, 0`. Inside it, `ν` is `1` when the parities agree and otherwise the CM
half-weight character of weight one on the embeddings above one complex embedding of the
imaginary quadratic subfield.

## Declarations

- `proposition48AuxiliaryParityNormalization :
  Proposition48AuxiliaryParityNormalizationStatement.{uF}` (theorem).

## Provenance

M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field, n < p*, Invent. Math.
134 (1998), 177–210, registered as `harris-1998-local-langlands` (PDF page = printed page − 176):

- Proposition 4.8, printed p. 201 (PDF page 25): for characters `χ`, `χ(∗)` of `W_{F'}` with
  `χ(∗)` in general position and an `E'/E`-regular algebraic Hecke character `𝛘` with
  `𝛘 = 𝛘⁻¹ ∘ c`, there is a cuspidal automorphic representation which is a weak automorphic
  induction of `𝛘`, supercuspidal at `v(∗)₁`. Its proof, printed pp. 201–203 (PDF pages 25–27),
  inducts on the length of the cyclic tower; the inherited hypotheses (i)–(iii) on printed
  p. 202 are regularity, conjugate inversion and general position.
- Printed p. 195 (PDF page 19): the local components `χ_v = (z/z̄)^{a(v)/2}`, the integers `a(v)`
  of one parity, and the choice `a(v) ≡ n − 1 (mod 2)` for cohomological automorphic induction;
  printed p. 191 (PDF page 15): representations constructed by automorphic induction are defined
  up to twisting by a half-integer power of the absolute value.

These passages give the parity issue that the normalization addresses. The correction by a
genuine conjugate-inverse base character, as stated in the Library, is a derived formulation of
the proof route and is not stated verbatim by Harris.

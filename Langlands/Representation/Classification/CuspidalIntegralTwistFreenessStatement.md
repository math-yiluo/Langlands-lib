# Integral twist freeness of positive-rank cuspidal data

Author: Worker 19. The exact interface and independence requirements were
specified by Worker 422 in the originating task.

`Langlands.Classification.CuspidalIntegralTwistFreeness.{uF,uV} F T` is a
Prop-valued definition. For every `ρ : T.CuspidalDatum.{uV,uF}` and every
integer `k`, it states

```text
ρ.twist (k : ℝ) = ρ ↔ k = 0.
```

The outer parameters are an arbitrary `p : ℕ` with `Fact p.Prime`, every
`F : PadicField.{uF} p`, and every supplied `T : F.TopologicalData`. Field and
representation-carrier universes remain independent. The only project import
is the published `Classification.Segments` module; no existing pair is changed.

## Meaning of the target

The imported `PadicField.TopologicalData.CuspidalDatum` records a strictly
positive rank and the actual isomorphism class of an irreducible supercuspidal
smooth complex representation. Its `twist` is the published action induced by
`T.determinantPowerCharacter`, the real power of the residue-normalized
absolute value of the determinant. Thus equality in this statement is equality
of cuspidal data, including the supercuspidal isomorphism class. Nontriviality
of the twisting character by itself would not establish this statement.

There is no additional central-character, admissibility, unitarity,
finite-dimensional-carrier, or classification hypothesis. The existing
`GeneralLinear.IsSupercuspidal` predicate already includes admissibility;
`supercuspidalProperty` also requires irreducibility. Rank positivity is the
existing `CuspidalDatum.rank_pos` field. The zero-rank case is not included.
The assertion covers integral exponents, with their displayed cast to the
reals; it does not assert freeness for every real exponent.

## Internal provenance and remaining proof

This is an internal lower-level interface motivated by the use of segment
supports as finite intervals in integral-twist orbits. It is not a translation
of a numbered literature theorem, and no external assertion is used as a
proved input here. In particular, this pair makes no attribution of a formal
freeness proof to Zelevinsky's section 9.10. The published `Segments` Markdown
already identifies integral nonperiodicity as the missing justification for
recovering segment endpoints from supports.

An intended proof chooses a representative, obtains its genuine scalar central
character, and evaluates an isomorphism with its twist on a scalar uniformizer.
For rank `r > 0`, determinant twisting multiplies that central action by
`|ϖ|^(r*k)`. Cancellation on a nonzero vector forces this factor to be one.
The residue-normalized value `|ϖ| = q⁻¹`, with `q > 1`, then forces `k = 0`.
The reverse implication follows from the published `CuspidalDatum.twist_zero`.
These sentences describe a proof route, not a proof implemented in this file.

The current Library supplies `Langlands.admissibleSchur_centralCharacter` in
`Langlands.Representation.Smooth.Schur.Proof`, giving the unique locally
constant scalar central character of an irreducible admissible complex
representation. Its sole project import is `Smooth.Schur.Statement`, whose
sole project import is `Smooth.Definitions`; its other imports are Mathlib.
Together with the admissibility already carried by a supercuspidal
representative, this is a reusable lower-level input, independent of segment
classification. No general irreducible-admissibility theorem is needed for
these supplied representatives.

The quotient-to-isomorphism transport, restriction of the central character
to scalar matrices, twist comparison on a nonzero vector, scalar determinant
calculation, and normalized-uniformizer numerical argument still have to be
assembled and checked in the exact proof successor. Publication of this
statement, citations, drafts, and pending proof tasks do not prove them.

The successor must remain directly and transitively independent of generic
segment-product uniqueness, multisegment exhaustion, ordered strong-head
existence, quotient coverage, ordered conversion, tempered uniqueness,
`SquareIntegrableLanglandsClassification`, square-integrable exhaustion, and
regular exhaustion. Any shared lower-level proof input needs an independence
audit. This statement supplies no classification theorem or finite-support
reconstruction theorem.

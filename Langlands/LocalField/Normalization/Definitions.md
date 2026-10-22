# Arithmetic normalization data

This module constructs arithmetic data for any prime `p`, any
`F : Langlands.PadicField p`, and the explicitly supplied
`T : F.TopologicalData`. The coefficient-field universe remains arbitrary.
It uses the specified valuation throughout. The topology, valuation,
valuative-extension, and local-field instances are installed locally from
`T`; the module adds no global instances.

## Integer rings, residue field and scalars

`Integers` is `(ValuativeRel.valuation F.Carrier).integer`, with the
valuative relation taken from `T`. `ResidueField` is its actual local-ring
residue field, and `residue` is the quotient map. `baseIntegerMap` restricts
the specified embedding of `Padic p` to the actual valuation integer rings.
Its membership proof applies the valuative-extension comparison to the
inequality defining a base integer. `integerAlgebra` is the explicit algebra
structure induced by this restriction.

`residueCharP` supplies the characteristic certificate needed for the
prime-field map. In `Padic p`, the valuation of `p` is strictly below one.
The valuative-extension certificate carries that inequality to `F`. Thus
`p` is a nonunit of the integer ring, belongs to its maximal ideal, and maps
to zero in its residue field. The prime-characteristic criterion gives
`CharP T.ResidueField p`.

`residueScalarMap` is `ZMod.castHom` constructed from this certificate.
`residueAlgebra` is its induced algebra structure. Callers select these
structures with local instances when needed; they are not inferred from
an arbitrary field structure on the residue type. `residueCardinality`
is `Nat.card T.ResidueField`. `residueDegree` is the module finrank over
`ZMod p` using this scalar map. Neither is an independently chosen number.

## Discrete order and absolute-value convention

`discreteValuation` composes the actual value-group valuation with
Mathlib's ordered multiplicative isomorphism from the local field's value
group with zero to `WithZero (Multiplicative ℤ)`. `uniformizer` chooses a
preimage of `exp (-1)` by surjectivity of the actual valuation.

`ord x` is the negative logarithm of the resulting multiplicative value.
Its convention at zero is **zero**, since `WithZero.log 0 = 0`.
Consequently order additivity must exclude zero multiplicands.
`ramificationIndex` is the natural-number value of `ord (p : F.Carrier)`.
This is the absolute ramification convention; its positivity and the
ramification/residue-degree identity are theorem obligations.

`normalizedAbs x` is zero if `x=0`, and otherwise
`(residueCardinality : ℝ) ^ (-ord x)`, with integer exponentiation.
This module contains constructions and their necessary intrinsic
certificates. It does not assume or package proofs of the degree identity,
absolute-value laws, topology comparisons, or spectral-norm comparison.
Those results require separate accepted statements and checked proofs.

## Original source and correspondence

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
Graduate Texts in Mathematics 67, Springer, 1979:

- Chapter II, Section 1, pages 26–28: valuation absolute values, with the
  residue-cardinality normalization `a=q⁻¹` on page 27.
- Chapter II, Section 2, Proposition 3 and Corollaries 1–4, pages 28–30:
  integer rings, residue degree, ramification and extension degree.
- Chapter II, Section 5, opening paragraph, page 36: absolute ramification
  `v(p)`, residue cardinality `p^f`, and degree `ef` for finite p-adic fields.

These original pages were read in PDF pages 34–38 and 44 of
`C:/Central-Library/Serre--Local Fields--1979.pdf`.
Registered source: `serre-1979-local-fields`; content SHA256:
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The explicit structures, selected uniformizer, and integer-valued zero
convention are Lean implementation choices. The source's identities guide
the later theorem obligations; they are not assumptions of these definitions.

## Exact dependencies and implementation

The project dependency is accepted definition
`ac4cb7d5-5dd1-44b6-9d56-f0ec6c70bce0`, version 1,
`Langlands.LocalField.Definitions`. Its effective Lean SHA256 is
`8d9cc8aa128861b13b4f96d38bf95be46844d2eaad28aa3cbb654b070ee0e517`
and Markdown SHA256 is
`6cfb939cf42a71a81fa648b77bd4bab1076bffe0d62519181f7dc7db742124bf`.
Its publication receipt is `203bba66-269f-46f4-984c-71531a4963c2`.
The input includes `TopologicalData`; constructing it for every finite
extension is a separate project obligation.

The pinned environment is artifact `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`,
version 1, Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. The principal Mathlib interfaces
are `ValuativeRel.valuation`, `ValuativeExtension.vle_iff_vle` and
`vlt_iff_vlt`, `IsLocalRing.residue_eq_zero_iff`,
`Valuation.Integer.not_isUnit_iff_valuation_lt_one`,
`CharP.charP_iff_prime_eq_zero`, `Padic.valuation_p_lt_one`,
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt`,
`ValuativeRel.valuation_surjective`, and `WithZero.log`.

Worker 27 authored this construction group. Native compilation succeeded
without diagnostics. That development check does not constitute independent
semantic acceptance or publication.

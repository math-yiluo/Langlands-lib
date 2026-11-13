# Existence and uniqueness of normalized valuations

`Langlands.Geometry.Building.Kottwitz.NormalizedIntermediateValuationStatement`
is the unconditional auxiliary obligation underlying the normalization in KP
Proposition 11.1.1, printed pp. 420–421 (PDF pp. 451–452), Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023), source
`kaletha-prasad-2023-bruhat-tits-new-approach`. The 2024 corrections do not alter
this proposition.

For every nonarchimedean local field `F` and every finite intermediate extension
`L` of `SeparableClosure F / UnramifiedClosure F`, it asserts that there is exactly
one valuation `L → WithZero (Multiplicative ℤ)` that is equivalent to the actual
spectral valuation `intermediateValuation F L` and is surjective. There is no
Galois, tame, characteristic, or residue-characteristic restriction. No
local-field instance on `K` or `L` is requested.

This explicit formulation is derived from the integer normalization used by KP,
not a quotation of a separately numbered assertion. Its mathematical content is
that finite extensions of this henselian discretely valued field are still
nontrivially discretely valued, and that the ordered integer normalization is
unique. The declaration is a proposition definition; no proof is provided. Once
proved, its existence clause and `normalizedIntermediateValuation_spec` give the
required specification of the selected valuation in the companion definition.

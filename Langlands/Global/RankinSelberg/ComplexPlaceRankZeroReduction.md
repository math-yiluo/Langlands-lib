# The complex-place functional equation with the rank-one equal-rank case proved

Module `Langlands.Global.RankinSelberg.ComplexPlaceRankZeroReduction`, namespace
`Langlands.Global.RankinSelbergGlobal`. Intermediate result towards
`ComplexPlaceFunctionalEquationStatement` (Jacquet 2009, Theorem 2.1, at a complex place).
Provenance: internal.

The module reduces the target to two local premises. The first is the unequal-rank local
functional equation. The second is the equal-rank local functional equation at every positive
rank index. The rank-one case of the equal-rank local functional equation
(`GL₁(ℂ) × GL₁(ℂ)`, rank index `r = 0`) is proved from complex Tate theory, which the Library
proves in `Langlands/LocalFactor/Archimedean/ComplexTateProof`. Every declaration is proved,
and no axioms are added.

## The statement

```lean
def ComplexPlaceRankZeroReductionStatement : Prop :=
  ComplexLocalUnequalFunctionalEquationStatement →
    (∀ r : ℕ, 0 < r → ComplexLocalEqualAtRankStatement r) →
    ComplexPlaceFunctionalEquationStatement.{u}
```

The conclusion `ComplexPlaceFunctionalEquationStatement.{u}` is the Library's conjunction
`ComplexUnequalFunctionalEquationStatement.{u} ∧ ComplexEqualFunctionalEquationStatement.{u}`.
These are the unequal-rank and equal-rank Rankin–Selberg functional equations at a complex
place `w` of a number field `F` in the universe `u`. Both are stated for actual cuspidal
realizations `T`, `T'` with contragredients `Td`, `Td'` and their parameters `d`, `d'`, `dd`,
`dd'` at `w`. Off a discrete set they assert
`L(s, d × d') Md(1 - s) = ω_{T'}(-1)^r ε(s, d × d', ψ_a) L(1 - s, dd × dd') M(s)`, where
`M` and `Md` are meromorphic continuations of the two archimedean integrals. Here
`L(s, d × d')` is the Library's meromorphic `L`-factor
`((complexPairLFactor d d').denominator s)⁻¹`, the inverse of the entire function
`.denominator`. The Lean statement writes these inverses explicitly.

The two premises are hypotheses here:

1. `ComplexLocalUnequalFunctionalEquationStatement`: the Library's local unequal-rank premise
   (Jacquet 2009, Theorem 2.1 (i)–(iii), for `GL_(r+1)(ℂ) × GL_(t+1)(ℂ)` with `t < r`). It
   concerns functions in the local Whittaker models `complexWhittakerModel r d a` and
   `complexWhittakerModel t d' (-a)`. Its sign is `complexCentralSign d' ^ r`, and the
   inverse character lists of `d` and `d'` replace `dd` and `dd'`. The Library proves it as
   `complexLocalUnequalFunctionalEquation` (module `ComplexPlaceUnequalFunctionalEquationProof`).
2. `ComplexLocalEqualAtRankStatement r` for every `r > 0`: the Library's local equal-rank
   premise `ComplexLocalEqualFunctionalEquationStatement` with the rank index fixed to `r`
   (defined in the Library module `ComplexLocalEqualRankZeroReduction`). The rank index `r`
   corresponds to `GL_(r+1)(ℂ) × GL_(r+1)(ℂ)`, so `r > 0` means size at least two. The Library
   proves the full equal-rank statement as `complexLocalEqualFunctionalEquation` (module
   `ComplexPlaceEqualFunctionalEquationProof`).

## The proof

`complexPlaceRankZeroReduction` is a single term:

```lean
fun hU hpos =>
  complexPlaceFunctionalEquationLocalFEReduction hU
    (complexLocalEqualRankZeroReductionStatement
      Langlands.LocalFactor.ComplexTate.complexArchimedeanTateStatement hpos)
```

- `complexPlaceFunctionalEquationLocalFEReduction` (Library module
  `ComplexPlaceFunctionalEquationLocalFEReduction`) derives the target from the two local
  functional equations `ComplexLocalUnequalFunctionalEquationStatement` and
  `ComplexLocalEqualFunctionalEquationStatement`. The Whittaker-model, minus-one,
  irreducibility and pairing premises are already proved in the Library.
- `complexLocalEqualRankZeroReductionStatement` (Library module
  `ComplexLocalEqualRankZeroReduction`) derives
  `ComplexLocalEqualFunctionalEquationStatement` from `ComplexArchimedeanTateStatement` and
  premise 2. It proves the case `r = 0` from complex Tate theory and takes the cases `r > 0`
  from premise 2.
- `Langlands.LocalFactor.ComplexTate.complexArchimedeanTateStatement` (Library module
  `Langlands.LocalFactor.Archimedean.ComplexTateProof`, below) proves
  `ComplexArchimedeanTateStatement`.

The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Complex Tate theory

The Library theorem `Langlands.LocalFactor.ComplexTate.complexArchimedeanTateStatement`
(module `Langlands.LocalFactor.Archimedean.ComplexTateProof`) proves
the Library proposition `Langlands.LocalFactor.ComplexArchimedeanTateStatement` with no
hypotheses. That proposition is Tate's local theory at a complex place. It concerns the zeta
integrals `∫ f(z) (z/|z|)^m |z|^(2(s+t)-2) dμ(z)` of Schwartz functions `f` on `ℂ`, where `μ`
is twice Lebesgue measure. It asserts convergence for `Re(s + t) > 0`, a unique
continuation in meromorphic normal form, the local functional equation for the dilated and
scaled Fourier transform, and the adapted Gaussian computation. This module only uses the
theorem.

## The rank-one case

The case `r = 0` is `complexLocalEqualAtRankStatement_zero` in the Library module
`ComplexLocalEqualRankZeroReduction`, with its helper modules `ComplexRankZeroHaar`,
`ComplexRankZeroWhittaker` and `ComplexRankZeroLocal`. They identify the rank-one Whittaker models with multiples of
`χ_c ∘ det`, and the rank-one integrals with complex Tate zeta integrals. The rank-one factors
are `L(s, [c] × [c']) = Γℂ(s + t + |m|/2)`, `L(1 - s, [c⁻¹] × [c'⁻¹]) = Γℂ(1 - s - t + |m|/2)`
and `ε = |a| (a/|a|)^m |a|^(2(s+t-1)) i^|m|`. Here `m` and `t` are the weight and exponent of
the product character `c · c'`. With these factors, the rank-one functional equation is
Tate's local functional equation from `ComplexArchimedeanTateStatement`.

## What is not proved

The module does not prove the unequal-rank local statement, and it does not prove the
equal-rank local statement at positive rank indices. The unconditional proof of
`ComplexPlaceFunctionalEquationStatement` remains open.

## Provenance

Internal intermediate result: our own conditional reduction of
`ComplexPlaceFunctionalEquationStatement`, stated as an implication. The target is Jacquet,
*Archimedean Rankin–Selberg integrals* (2009), Theorem 2.1, at a complex place. Its
equal-rank case `n = n' = 1` is Tate's local functional equation at `ℂ`: J. T. Tate,
*Fourier analysis in number fields and Hecke's zeta-functions* (Cassels–Fröhlich 1967,
Chapter XV), §§2.2–2.5. The Library states it as `ComplexArchimedeanTateStatement` and
proves it in `ComplexTateProof`. The composition uses only Library theorems.

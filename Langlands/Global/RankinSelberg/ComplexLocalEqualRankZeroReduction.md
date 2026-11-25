# The rank-one case of the complex equal-rank local functional equation

The module splits the published local statement
`ComplexLocalEqualFunctionalEquationStatement` by the rank index `r` and proves the case
`r = 0` (`GL₁(ℂ) × GL₁(ℂ)`) from the Library proposition
`Langlands.LocalFactor.ComplexArchimedeanTateStatement` (Tate's local theory at a complex
place). The entry proposition assumes complex Tate theory and the equal-rank local statement
for every `r > 0`.

All declarations are in the namespace `Langlands.Global.RankinSelbergGlobal`. The module
activates the Library's local Borel measurable-space instances on `GL_(n+1)(ℂ)`,
`N_(n+1)(ℂ)` and the quotient `N_(n+1)(ℂ) \ GL_(n+1)(ℂ)` from
`ArchimedeanFunctionalEquationStatement`, as `ComplexPlaceFunctionalEquationReduction`
does. So the restated body elaborates with the same instances.

## Declarations

- `ComplexLocalEqualAtRankStatement r : Prop` (a definition). It is the body of
  `ComplexLocalEqualFunctionalEquationStatement` with the rank index `r` fixed. The
  quantifiers are the same: lists `d`, `d'` of `r + 1` complex character data, `a ∈ ℂˣ`, a
  quotient measure `D`, `W` in the Whittaker model `complexWhittakerModel r d a`, `W'` in
  `complexWhittakerModel r d' (-a)` and a Schwartz function `Φ` on `ℂ^(r+1)`. The nine
  conclusions are also the same. Both integrands are integrable and both integrals are
  holomorphic on `Re s > σ`. Meromorphic `M`, `Md` agree with the integrals there. The
  functional equation
  `L(s, d × d') Md(1 - s) = ω_{d'}(-1)^r ε(s, d × d', ψ_a) L(1 - s, d⁻¹ × d'⁻¹) M(s)`
  holds for `s` outside a discrete subset of `ℂ`. The two `L`-factors are the inverses of
`.denominator` for the original and inverse character pairs. Here `ω_{d'}(-1)` is
  `complexCentralSign d'`, `ε` is taken with the constant `|a|`, and `d⁻¹`, `d'⁻¹` are the
  lists of inverse characters.

- `complexLocalEqualFunctionalEquationStatement_iff`:
  `ComplexLocalEqualFunctionalEquationStatement ↔ ∀ r, ComplexLocalEqualAtRankStatement r`.
  Both directions are instantiation at `r`. Lean checks that the bodies agree
  definitionally.

- `complexLocalEqualAtRankStatement_zero`: `ComplexArchimedeanTateStatement` implies
  `ComplexLocalEqualAtRankStatement 0`. Lists of length `1` are singletons `[c]`, `[c']`
  (`List.length_eq_one_iff`). By `ComplexRankZero.exists_eq_of_mem_complexWhittakerModel`
  (module `ComplexRankZeroWhittaker`), `W = C · χ_c ∘ det` and `W' = C' · χ_{c'} ∘ det` for
  some constants `C`, `C'`. The lemma is applied with `ψ_a` and with `ψ_(-a)`. Then
  `ComplexRankZero.complexEqual_rankZero` (module `ComplexRankZeroLocal`) gives the nine
  conclusions, in exactly the form required at `r = 0`.

- `ComplexLocalEqualRankZeroReductionStatement : Prop` (the entry proposition):
  `ComplexArchimedeanTateStatement → (∀ r, 0 < r → ComplexLocalEqualAtRankStatement r) →
  ComplexLocalEqualFunctionalEquationStatement`.

- `complexLocalEqualRankZeroReductionStatement`: proof of the entry proposition. By
  `complexLocalEqualFunctionalEquationStatement_iff` it suffices to prove
  `ComplexLocalEqualAtRankStatement r` for every `r`. For `r = 0` this is
  `complexLocalEqualAtRankStatement_zero`. For `r > 0` it is the second hypothesis.

## The proof of the case `r = 0`

The proof uses three helper modules in the same directory, each with paired Markdown.

1. `ComplexRankZeroHaar`: every quotient measure `D.measure` on
   `N₁(ℂ) \ GL₁(ℂ) ≅ ℂˣ` is a nonzero multiple `κ` of the Haar measure `|z|⁻² dz`
   (uniqueness of Haar measure on `ℂˣ`). Integrals and integrability against `D.measure`
   are transported to `ℂ`.
2. `ComplexRankZeroWhittaker`: every element of the Whittaker model
   `complexWhittakerModel 0 [c] a` is `C · χ_c ∘ det`. The standard module of `[c]` is
   spanned by `χ_c ∘ det`, which is an eigenvector of all right derivatives. A Whittaker
   intertwiner preserves these eigen-equations. So the quotient of its image by `χ_c ∘ det`
   has zero derivative on the connected group `GL₁(ℂ)`, and is therefore constant.
3. `ComplexRankZeroLocal`: if `W = C · χ_c ∘ det` and `W' = C' · χ_{c'} ∘ det`, then both
   rank-one integrals are `κ/2 · C C'` times complex Tate zeta integrals. The first is the
   zeta integral of the line restriction of `Φ`, with the weight `m` and exponent `t` of
   `c · c'`. The second is that of its Fourier transform for `ψ_a`, with `-m` and `-t`.
   Holomorphy of the Tate zeta integral on its half-plane is derived from integrability
   and the meromorphic continuation in `ComplexArchimedeanTateStatement`. The
   rank-one `L`- and `ε`-factors are computed: `L(s, [c] × [c']) = Γℂ(s + t + |m|/2)`
   and `L(1 - s, [c⁻¹] × [c'⁻¹]) = Γℂ(1 - s - t + |m|/2)`, and `ε` is the factor in Tate's
   local functional equation. The main theorem `complexEqual_rankZero` derives the nine
   conclusions from `ComplexArchimedeanTateStatement`. The sign `ω_{c'}(-1)^0` is `1`.

## Provenance

The case `n = n' = 1` of Jacquet,
*Archimedean Rankin–Selberg integrals* (2009), Theorem 2.1, at a complex place is Tate's
local functional equation at `ℂ` (Tate's thesis; Cassels–Fröhlich 1967, Chapter XV). The
Library states it as `ComplexArchimedeanTateStatement`. The split by rank, the description
of the rank-one Whittaker model and the reduction of the rank-one integrals to Tate
integrals are internal to this project. They follow the real-place version
(`RealEqualRankZeroReduction`, `RealRankZeroHaar`, `RealRankZeroLocal`).

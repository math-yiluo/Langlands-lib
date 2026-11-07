# Langlands heads of `a(d,n)^ρ` are Speh representations

Author: Worker 1792. Module
`Langlands.Representation.Classification.TadicSpehHeads`, namespace
`Langlands.Classification`. Every result is proved from published Library results;
there are no hypotheses of theorem type, no axioms and no `sorry`.

The main theorem is the identification behind Tadić's Theorem A.9 (1986, printed
p.377), which Tadić calls "a direct consequence" of Theorem A.8: for a unitary
cuspidal `ρ`, `L(a(d,n)^ρ)` is the Speh representation `u(δ, d)` with
`δ = L(Δ[n]^ρ)` square-integrable. Here `a(d,n)^ρ` is
`tadicMultisegment ρ d n hn` from `Classification.TadicMultisegments`: the `d`
segments `ν^x Δ[n]^ρ` of length `n` centered at `x = j - (d-1)/2`, `j < d`.

## Declarations

- `cuspidalDatum_twist_eq_self`: if `ν^s ρ = ρ` for a cuspidal datum, then
  `s = 0`. A representative `A` of `ρ` is then equivalent to its twist by
  `|det|^s`, and the published
  `IntegralTwistFreeness.exponent_eq_zero_of_equiv` gives `s = 0`.
- `cuspidalDatum_twist_injective`: `ν^s ρ = ν^t ρ` implies `s = t`, by twisting
  by `-t` and the previous lemma.
- `tadicCenteredSegment_eq_twist`: `ν^x Δ[n]^ρ` is the segment twist of
  `ν^0 Δ[n]^ρ` by `x`.
- `spehSegments ρ n d hn : Fin d → Segment`: the segments `ν^((d-1)/2 - i) Δ[n]^ρ`,
  listed with decreasing centers.
- `spehSegments_multiset`: these `d` segments, as a multiset, are
  `tadicMultisegment ρ d n hn`. The proof reindexes `List.ofFn` by `Fin.rev`
  (`Multiset.map_univ_val_equiv Fin.revPerm`).
- The imported `Langlands.PadicField.TopologicalData.SegmentProductDatum.multisegment_degree`
  from `SegmentSocleInversionReduction` supplies the degree `N` of a segment product
  datum on `GL_N`; this module reuses that declaration.
- `tadicMultisegment_rank_eq_of_isLanglandsHead`: a Langlands head of
  `a(d,n)^ρ` on `GL_N` has `N = d * (n * deg ρ)`.
- `tadicSegmentHead ρ hn`: a chosen strong segment head `δ` of `ν^0 Δ[n]^ρ`
  (`segmentSpecialConstituentExistence`, a proved existence statement), with
  `isSegmentHead_tadicSegmentHead`.
- `tadicSpehDatum ρ hn d hd`: the Speh datum with block `δ`, rank `n deg ρ` and
  length `d`. `tadicSpehDatum_isDiscreteSeries`: for unitary `ρ` it is a
  discrete-series datum.
- `tadicSpehSegmentDatum ρ hn d hd`: the segment product datum on
  `GL_(d n deg ρ)` with segments `spehSegments ρ n d hn` and blocks
  `ν^((d-1)/2 - i) δ`. Its induced representation is definitionally the centered
  Speh induction (`tadicSpehSegmentDatum_induced`); its multisegment is
  `a(d,n)^ρ`; it is precedence-ordered and its blocks are segment heads.
- `exists_isSpeh_of_isLanglandsHead`: if `ρ.IsUnitary`, `0 < n`, `0 < d` and
  `(tadicMultisegment ρ d n hn).IsLanglandsHead π` for `π` on `GL_N`, then there
  are `D : SpehDatum F T`, `S` on `GL_(D.degree)` and `hD : D.degree = N` with
  `D.IsSpeh S` and `(hD ▸ S) ≅ π`. This is exactly the first alternative of the
  published `IsTadicBuildingBlock`.
- `exists_isLanglandsHead_tadicMultisegment`: for unitary `ρ` and `n, d > 0`,
  `a(d,n)^ρ` has a Langlands head on `GL_N` whenever `N` is its degree. The proved
  `glRegularLanglandsHeadExistence` gives a strong head of the standard module of
  `(tadicSpehDatum ρ hn d hd).temperedLanglandsDatum`, which is the centered Speh
  induction, hence the induced representation of `tadicSpehSegmentDatum`.

## Proof of `exists_isSpeh_of_isLanglandsHead`

1. Put `N = d n deg ρ` by the rank lemma. Write the head relation as a segment
   product datum `E` with multisegment `a(d,n)^ρ`, precedence-ordered, with segment
   heads, and with `π` the irreducible head of `E.induced`.
2. Let `Δ₀ = ν^0 Δ[n]^ρ` and `δ = tadicSegmentHead ρ hn`. With `c = (n-1)/2`, the
   proved `segmentConstituentRealTwistCompatibility` makes `ν^c δ` a head of
   `ν^c Δ₀`, whose base is `ρ` (an identity of supercuspidal classes). A
   representative `A` of `ρ` is unitarizable because `ρ.IsUnitary`. The proved
   `segmentCenteredSpecialSquareIntegrability` then shows that `ν^(-c) ν^c δ = δ`
   is square-integrable and unitarizable (`realPowerTwist_neg_cancel`). So
   `D = tadicSpehDatum ρ hn d hd` is a discrete-series Speh datum.
3. The datum `E₀ = tadicSpehSegmentDatum ρ hn d hd` has `E₀.induced =
   D.centeredInduced` definitionally. Its blocks are segment heads (twist
   compatibility again). It is precedence-ordered: a precedence `Δ_i ≺ Δ_j` for
   `i < j` would give `ν^(x_j) ρ' = ν^(k + x_i) ρ'` with `k > 0`, so
   `x_j = x_i + k` by `cuspidalDatum_twist_injective`, whereas the centers
   decrease.
4. Its multisegment is `a(d,n)^ρ` (`spehSegments_multiset`). The proved
   `orderedSegmentHeadProductIndependence` gives `E₀.induced ≅ E.induced`, so `π`
   is the irreducible head of `D.centeredInduced` (`IsIrreducibleHead.of_equiv`).
   The published `SpehDatum.isSpeh_of_isLanglandsHead` gives `D.IsSpeh π`, and
   the witness is `(D, π, rfl)`.

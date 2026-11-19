# Existence of pseudo-coefficients of square-integrable representations of `GL_n(F)`

This module states, as a proposition, that every irreducible
square-integrable representation of `GL_n(F)`, for `F` a nonarchimedean local
field of characteristic zero, has a pseudo-coefficient with its central
character. It is not proved here. The predicate `IsPseudoCoefficient` and
`HasCentralCharacterRep` are defined in `Langlands.BaseChange.PseudoCoefficient`.

## Statement

`PseudoCoefficientExistenceStatement.{u, uV} : Prop` says the following.

Let `F : Type u` be a nonarchimedean local field
(`[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`)
of characteristic zero (`[CharZero F]`), and `n : ℕ`. Give `GL_n(F)`
(`GeneralLinear n F`) the topology induced from matrices, with the facts that
it is Hausdorff, locally compact and totally disconnected supplied by the
Library's `LocalFieldTopology.generalLinear_t2Space`,
`generalLinear_locallyCompactSpace` and `generalLinear_totallyDisconnectedSpace`,
and its Borel σ-algebra, introduced locally as in the Library's
`HasCharacterValue`. Then for

- every complex vector space `V : Type uV` and every representation
  `π : Representation ℂ (GL_n(F)) V` that is admissible (`hπ : IsAdmissible π`),
  irreducible (`π.IsIrreducible`) and square-integrable
  (`JacquetLanglands.IsSquareIntegrable π`: a unitary central character and
  matrix coefficients square-integrable modulo the centre, for every Haar
  measure on `GL_n(F) / Z`);
- every character `χ : Subgroup.center (GL_n(F)) →* ℂˣ` of the centre with
  `HasCentralCharacterRep π χ` (that is, `χ = ω_π`);
- every Haar measure `μ` on `GL_n(F)`,

there is `f : SchwartzBruhat (GL_n(F))`, a locally constant compactly
supported function, with `IsPseudoCoefficient μ χ π hπ f`: `Θ_π(f) = 1`, and
`Θ_{π'}(f) = 0` for every admissible, irreducible, tempered representation
`π'` of `GL_n(F)` on a complex vector space in the universe `uV`, with central
character `χ`, that is not isomorphic to `π`. Here `Θ` is the Library's
distribution character `Character.distribution μ`.

## Sources

- Kazhdan, *Cuspidal geometry of p-adic groups*, J. Analyse Math. 47 (1986),
  Theorem K(a), printed p. 7 (PDF page 7): for a square-integrable
  representation `π` of `G` there is `h_π ∈ A(G) ⊂ C^∞_c(G)` with
  `Tr π'(h_π) = δ_{π,π'}` for every tempered irreducible `π'`. Kazhdan's §1.1
  (same page) works over a nonarchimedean local field of characteristic zero
  and assumes that the centre `Z` of `G` is compact.
- Henniart–Lemaire, *Changement de base et induction automorphe pour `GL_n`
  en caractéristique non nulle* (2011), II.5.13, Définition and Proposition,
  printed p. 113 (PDF page 121). For `E = F` and `σ = id` a σ-discrete series
  is a discrete series representation (HL II.1.7, printed p. 59), the
  intertwiner `A` can be taken to be the identity, and the twisted character
  is the ordinary character. The Proposition then gives a pseudo-coefficient
  in `C^∞_c(GL_n(F), χ)` with the fixed central character `χ = ω_π`, tested
  against tempered irreducible `π'` with `ω_{π'} = χ`. HL II.2.6–II.2.7,
  printed pp. 66–67 (PDF pages 74–75), relate the traces of a compactly
  supported function and of its average over the centre; see "Test
  functions" below.
- Arthur–Clozel (1989), Chapter 1, Corollary 2.10, printed p. 18, is the same
  fixed central character form in the twisted setting; it is the source of
  `TwistedPseudoCoefficientExistenceStatement`.

## Comparison with the sources

**Compact centre and fixed central character.** Kazhdan assumes that the
centre is compact. The statement quantifies over every `n : ℕ`. For `n ≥ 1`
the centre `F^×` of `GL_n(F)` is not compact, and Kazhdan's form cannot hold
as stated: for `f ∈ C^∞_c(GL_n(F))`, the trace of `f` against
`π ⊗ |det|^{it}` depends continuously on the real number `t`, and it would
have to be `1` at `t = 0` and `0` for small `t ≠ 0`, where
`π ⊗ |det|^{it} ≇ π` because the central characters differ: on the scalar
matrix `z`, `|det z|^{it} = |z|^{i n t}`, which is not identically `1` when
`n ≥ 1` and `t ≠ 0` is small. The statement therefore fixes the central
character and tests only against representations with central character
`χ`, following HL II.5.13 (with `E = F`, `σ = id`) and AC Chapter 1,
Corollary 2.10. For `n = 0` the group `GL_0(F)` is trivial, so its centre is
compact, every representation has the trivial central character, and the
two forms agree. These remarks are not formalized.

**Test functions.** Write `G = GL_n(F)` and `Z` for its centre. HL and AC
take the pseudo-coefficient in `C^∞_c(G, χ)` and compute its traces by integration over `Z \ G`; here it is
a compactly supported `f`, and traces are computed with the Haar measure `μ`
on `G` itself. Fix a Haar measure `dz` on the centre and let `f_χ` be the
average of `f` over the centre against `χ` for `dz`. For representations
with central character `χ`, the trace of `f` for `μ` equals the trace of
`f_χ` for the quotient measure `μ / dz` on `Z \ G`, formed with the same
`dz` (HL II.2.6–II.2.7, printed pp. 66–67, with `E = F`, `σ = id`); for an
incompatible quotient measure the two traces differ by a constant factor.
HL obtain their pseudo-coefficient as such an average (printed
pp. 113–114). See the Markdown of `Langlands.BaseChange.PseudoCoefficient`
(remark "Test functions"). This comparison is not formalized.

**Square-integrable versus discrete series.** The hypothesis on `π` is the
Library's `JacquetLanglands.IsSquareIntegrable`, Kazhdan's
"square-integrable": with a unitary central character, matrix coefficients in
`L²` modulo the centre. For `n ≥ 1` the irreducible square-integrable
representations of `GL_n(F)` are its discrete series representations (HL
II.1.7 with `E = F`, `σ = id`).

**Haar measure.** Kazhdan fixes one Haar measure `dg`. Here every Haar measure
`μ` (Mathlib's `Measure.IsHaarMeasure` for the Borel σ-algebra) is
quantified. `GL_n(F)` is locally compact and second countable, so every
Haar measure on it is `cμ₀` for a fixed one `μ₀` and some `c > 0` (Mathlib's
`Measure.isMulLeftInvariant_eq_smul` and
`Measure.haarScalarFactor_pos_of_isHaarMeasure`). Replacing `μ` by `cμ`
multiplies every character value by `c`, so `f` works for `μ` exactly when
`c^{-1} f` works for `cμ`, and the two forms are equivalent. This remark is
not formalized.

**Universe.** The test family in `IsPseudoCoefficient` ranges over
representations on spaces in the universe `uV` of `V`.

**`CharZero F`.** Kazhdan (1986) and Arthur–Clozel work in characteristic
zero. HL's argument does not depend on the characteristic, but the other
base-change statements of this programme assume `CharZero F`: the transfer
statement `Langlands.BaseChange.RegularTransferStatement` and the twisted
character statements `Langlands.BaseChange.TwistedCharacterRegularValuesStatement`
and `Langlands.BaseChange.SigmaLiftCharacterIdentityStatement`. This statement follows them.

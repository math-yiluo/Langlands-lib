# The regular semisimple and σ-regular sets are open and conull (statements 6–7)

The module `Langlands.BaseChange.RegularSetOpenConullStatement` states two propositions,
neither proved here:

- statement 6, `RegularSemisimpleOpenConullStatement.{u}`: the regular semisimple elements of
  `GL_n(F)` form an open set whose complement is null for every Haar measure;
- statement 7, `SigmaRegularOpenConullStatement.{u, v}`: the σ-regular elements of `GL_n(E)`,
  for a cyclic algebra `E` over `F`, form an open set whose complement is null for every Haar
  measure.

Here `F` is any nonarchimedean local field; no characteristic hypothesis is made.

## Sources

- Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, notes by
  DeBacker and Sally, ULS 16, AMS 1999, source ID
  `harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15).
  Introduction, printed p. 1: for the group `G` of rational points of a connected reductive
  group over a p-adic field, the set `G'` of points where `D_G` does not vanish is an open,
  dense subset of `G` whose complement has measure zero. For `GL_n` this is statement 6 (in
  characteristic zero, where `G'` is the set of elements with separable characteristic
  polynomial).
- Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61` (PDF page =
  printed page + 8). I.5.1, printed p. 29 (`E/F` an unramified field extension, I.4.1), and
  II.1.3, printed p. 57 (`E/F` a finite cyclic field extension, Chapter II): the twisted and
  ordinary character distributions on `G(E)` and `G(F)` are written as absolutely convergent
  integrals over the σ-regular set `G(E)_{σ-r}` and the regular set `G(F)_r`; II.1.2, printed
  p. 56, defines these sets. Cyclic algebras `E = E₁^r` are reached by the reduction of
  II.2.8, printed pp. 67–69. HL use, without stating it separately, that these sets are open (their
  functions are locally constant there) and that their complements do not contribute to the
  integrals; statement 7 is this fact for the Library's notion of σ-regularity.

## Statement 6

`RegularSemisimpleOpenConullStatement.{u}`: for every field `F : Type u` with
`[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]` and every `n : ℕ`,

- the set `{g : GL_n(F) | IsRegularSemisimple g}` is open, and
- for every Haar measure `μ` on `GL_n(F)`, for the Borel σ-algebra introduced locally,
  `μ {g | ¬ IsRegularSemisimple g} = 0`.

`IsRegularSemisimple g` (`Langlands/JacquetLanglands/RegularElliptic.lean`) means that the
characteristic polynomial of `g` is separable.

## Statement 7

`SigmaRegularOpenConullStatement.{u, v}`: for every field `F : Type u` as above, every
commutative `F`-algebra `E : Type v` with `[TopologicalSpace E] [IsTopologicalRing E]
[IsModuleTopology F E]`, every `σ : E ≃ₐ[F] E` and `l n : ℕ` with `IsCyclicAlgebra σ l`,

- the set `{δ : GL_n(E) | IsSigmaRegular σ l δ}` is open, and
- for every Haar measure `μ` on `GL_n(E)` (Borel σ-algebra), `μ {δ | ¬ IsSigmaRegular σ l δ} = 0`.

`IsSigmaRegular σ l δ` (`Langlands/BaseChange/Norm.lean`) means that some `γ ∈ GL_n(F)`
associated with `δ` (that is, `cyclicNorm σ l δ` is conjugate in `GL_n(E)` to `γ`) is
regular semisimple.

## Conventions

Both statements bind, with `haveI`, the Library theorems that make `GL_n(F)` (resp.
`GL_n(E)`, with `Module.Finite F E` from `hE.1`) Hausdorff and locally compact:
`LocalFieldTopology.generalLinear_t2Space` and `generalLinear_locallyCompactSpace`, resp.
`generalLinear_t2Space_of_finite` and `generalLinear_locallyCompactSpace_of_finite`. They do
not enter `IsOpen` or `IsHaarMeasure`; they record the setting, in which Haar measures exist.
Every Haar measure is a quantified argument; none is chosen.

## Why the statements hold (not formalized)

Over `F`, a matrix is regular semisimple exactly when the discriminant of its characteristic
polynomial is nonzero. This discriminant is a polynomial function of the matrix entries, so
the regular semisimple set is open, and it is not identically zero (a diagonal matrix with
distinct entries is regular semisimple), so its zero set, the complement, is null for the
additive Haar measure of `M_n(F) ≅ F^{n²}`. A Haar measure of `GL_n(F)` is `|det|^{-n}` times
the restriction of that measure to the open set `GL_n(F)`, so the complement is null for it
too.

Over `E`, the discriminant of the characteristic polynomial of `cyclicNorm σ l δ` plays the
same role. Its coordinates over `F` are polynomial functions of the coordinates of `δ` over
`F` (with `M_n(E) ≅ F^{l n²}`), and it does not vanish identically: for `δ` diagonal with
entries in `F` whose `l`-th powers are distinct, `cyclicNorm σ l δ = δ^l` is regular
semisimple. The Library's `CyclicNormLemmaStatement` (`Langlands/BaseChange/Norm.lean`: every
`δ` is associated with some `γ`, and associated `γ` are conjugate) relates `IsSigmaRegular` to
this discriminant: `δ` is σ-regular exactly when it does not vanish.

For `n = 0` every element is regular semisimple and σ-regular (the characteristic
polynomial is `1`), and both statements are trivial.

## Regularity in positive characteristic

The statements concern the Library's notions: separable characteristic polynomial, and an
associated element with separable characteristic polynomial. HL (II.1.2, printed p. 56) and
Lemaire 2004 call `γ` regular when its characteristic polynomial is squarefree; in positive
characteristic this can be a larger set, since an irreducible polynomial need not be
separable. Only the Library's version is stated here; the discriminant argument above works in
every characteristic. In characteristic zero the two notions coincide.

## Use

- `Langlands.BaseChange.CharacterFunction`: definitions 1–2 integrate over all of `GL_n`;
  statements 6–7 show that this agrees with HL's integrals over the (σ-)regular set.
- The input L0 of the B5 comparison in the global trace-formula part of cyclic base change (a σ-stable irreducible
  `Π` and a bijective `A` admit `φ` supported in the σ-regular set with
  `trace(Π(φ) ∘ A) ≠ 0`) needs statement 7 together with statement 5
  (`TwistedCharacterLocalIntegrabilityStatement`).

## Not stated here

No density statement beyond the measure statement, no statement about σ-elliptic or elliptic
elements, and no statement about HL's (squarefree) regular sets in positive characteristic.

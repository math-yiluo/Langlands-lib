# Local integrability of characters of `GL_n(F)` (statement 4)

The module `Langlands.BaseChange.CharacterLocalIntegrabilityStatement` states, as the
proposition `CharacterLocalIntegrabilityStatement.{u, uV}`, Harish-Chandra's theorem for
`GL_n`: the character of an irreducible admissible representation of `GL_n(F)`, for a
nonarchimedean local field `F` of characteristic zero, is a locally integrable function that
is locally constant on the regular semisimple set. The statement is **not** proved here. The
module also proves lemma 4′: the statement gives the Library's
`Langlands.JacquetLanglands.HasRegularSemisimpleCharacterValues`.

## Sources

- Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, notes by
  DeBacker and Sally, ULS 16, AMS 1999, source ID
  `harish-chandra-1999-admissible-invariant-distributions`, cited as HC (PDF page = printed
  page + 15; the text layer is OCR, so formulas were checked against the page images).
  Theorem 16.3 (Theorem 1 of the original), printed p. 75 (also quoted in the Introduction,
  printed p. 1): for `G` the group of rational points of a connected reductive group over a
  p-adic field of characteristic zero, the character `Θ_π` of an admissible irreducible
  representation `π` is a locally summable function on `G` which is locally constant on the
  regular set `G'`. The proofs are in HC §§17–21. `GL_n(F)` is such a `G`, and for it `G'`
  is the set of elements with separable characteristic polynomial, the Library's
  `IsRegularSemisimple`.
- Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, cited as HL
  (PDF page = printed page + 8). II.1.3, printed p. 57: for an admissible representation `π`
  of `G(F) = GL_n(F)`, the distribution `Θ_π(f) = trace π(f)`; if `π` moreover has finite
  length, it is given by a function locally constant on `G(F)_r` and locally integrable on
  `G(F)`, independent of the Haar measure. This is the form of statement 4. HL work in
  positive characteristic and take the fact from Lemaire 1996 (their [59], II.2.8, printed
  p. 69), whose proof is disputed (see "Hypotheses"); HL are cited for the formulation, not
  as a proof.
- Harish-Chandra, "A submersion principle and its applications", Proc. Indian Acad. Sci.
  90 (1981), source ID `harish-chandra-1981-submersion-principle` (PDF page = printed page −
  94). §4, Theorem 2 and its Corollary, printed pp. 98–100: in any characteristic, the
  character coincides on `G'` with a locally constant function. This is the local constancy
  half only; local integrability is not proved there.

## Statement

`CharacterLocalIntegrabilityStatement.{u, uV}` quantifies over a field `F : Type u` with
`[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]` and over
`n : ℕ`. The topological instances on `GL_n(F)` (Hausdorff, locally compact, totally
disconnected) are the Library theorems `LocalFieldTopology.generalLinear_t2Space`,
`generalLinear_locallyCompactSpace` and `generalLinear_totallyDisconnectedSpace`, bound with
`haveI` inside the statement, exactly as in `HasRegularSemisimpleCharacterValues`.

The claim: for every complex vector space `V : Type uV` and every
`ρ : Representation ℂ (GL_n(F)) V` with `hρ : IsAdmissible ρ` and `ρ.IsIrreducible`
(Mathlib's `Representation.IsIrreducible`), there is `Θ : GL_n(F) → ℂ` with
`IsCharacterFunction ρ hρ Θ` (definition 2 of `Langlands.BaseChange.CharacterFunction`: for
every Haar measure `μ`, `Θ` is locally integrable and `trace ρ(f) = ∫ f Θ dμ` for every test
function `f`) such that `∀ᶠ x in nhds g, Θ x = Θ g` for every `g` with
`IsRegularSemisimple g` (`Langlands/JacquetLanglands/RegularElliptic.lean`). That is, `Θ` is
locally constant near each regular semisimple element. Since `Θ` is only determined almost
everywhere, the statement asserts the existence of one such function rather than naming it.

## Lemma 4′ (proved)

`CharacterLocalIntegrabilityStatement.hasRegularSemisimpleCharacterValues`: from
`CharacterLocalIntegrabilityStatement.{u, uV}`, for every `F : Type u` as above (with
`[CharZero F]`) and every `n`, the Library's
`Langlands.JacquetLanglands.HasRegularSemisimpleCharacterValues.{u, uV} F n` holds: the
character of every irreducible admissible `ρ` has a value at every regular semisimple `g`.
Proof: take the function `Θ` of statement 4; it is locally constant near `g`, so by
`IsCharacterFunction.hasCharacterValue` the number `Θ g` is the character value
`HasCharacterValue ρ hρ g (Θ g)`.

## Use

- The proof task of `SigmaLiftCharacterIdentityStatement` (Task 7816, milestone 2:
  `IsShintaniLift → IsSigmaLift`) needs statements 4–5 for all test functions, not only for
  those supported in the regular set: the character identity at regular points is turned into
  an identity of distributions by integrating the character functions.
- The Weyl integration formulas for locally integrable invariant functions (HL II.2.10,
  printed pp. 70–72) are applied to the functions of statements 4–5.

## Hypotheses

Statement 4 assumes `CharZero F`, like `TwistedCharacterRegularValuesStatement` and the other
base-change statements of the programme. Harish-Chandra's theorem (HC Theorem 16.3) is
proved in characteristic zero, and it is the proof of statement 4 named here. Lemma 4′
accordingly gives
`HasRegularSemisimpleCharacterValues F n` only for `F` of characteristic zero. In
characteristic zero the Library's `IsRegularSemisimple` (separable characteristic polynomial)
is HL's regularity (squarefree characteristic polynomial, HL II.1.2, printed p. 56) and HC's
`G'`.

Nothing is stated or claimed in positive characteristic. The papers that claim a proof
there are Lemaire, "Intégrabilité locale des caractères-distributions de `GL_N(F)` où `F` est
un corps local non-archimédien de caractéristique quelconque", Compositio Math. 100 (1996),
41–75 (HL's [59], cited in HL II.2.8, printed p. 69, and not in the project literature), for
ordinary characters of `GL_N`, and Lemaire 2004 (source ID
`lemaire-2004-twisted-character-local-integrability`) for twisted characters of `GL_n(D)`.
These proofs are disputed. Aizenbud, Gourevitch, Kazhdan and Sayag, "On Harish-Chandra's
integrability theorem in positive characteristic", arXiv:2602.16389 (2026), source ID
`aizenbud-gourevitch-kazhdan-sayag-2026-integrability-positive-characteristic`, §1.2.1 and
Appendix B (printed pp. 3–4 and 56), state that the arguments of Lemaire 1996, Lemaire 2004
and Lemaire 2005 (`SL_n(D)`) have a flaw. Their key step, Lemma 2.3.2 of Lemaire 1996 (a
submersion replacing the Luna slice at closed orbits that are not semisimple), is formulated
inconsistently, and its consistent version, Lemma 5.4.2 of Lemaire's Mémoire SMF 70 (1997),
is false as stated. So these papers are not cited here as a proof of local integrability in
positive characteristic. HL (II.1.3, printed p. 57, and II.2.8, printed p. 69), who work in
positive characteristic, rely on them, so HL's statement of the ordinary case in positive
characteristic is also not used as a proof.

The companion statements 6–7 (`Langlands.BaseChange.RegularSetOpenConullStatement`) hold in
every characteristic and assume nothing more.

## Not stated here

No Weyl integration formula, no character expansion near singular points (HC Theorem 16.2),
no local boundedness of `|D|^{1/2} Θ` (the second half of HC Theorem 16.3), no
finite-length version (HL II.1.3 states it for finite length) and no statement in positive
characteristic.

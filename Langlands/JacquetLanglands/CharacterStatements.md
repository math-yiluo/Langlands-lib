# Analytic input for the Jacquet–Langlands character identity

The Jacquet–Langlands relation `IsJacquetLanglandsPair`
(`Langlands.JacquetLanglands.Relation`) asks for the distribution
characters of `ρ` and `ρ'` to have values at corresponding points,
with `Θ_ρ(g) = (-1)^(n-1) Θ_ρ'(g')`. The sources evaluate characters
at points using two analytic facts. This module states those facts as
separate propositions and proves that, where they hold, the relation
is exactly the source's identity of character functions. It neither
proves nor assumes the two facts.

Throughout, `F` is a nonarchimedean local field
(`IsNonarchimedeanLocalField F`) and `D` is a central division algebra
of finite dimension over `F` with its `F`-module topology, as in
`Langlands.JacquetLanglands.DivisionUnits`. `HasCharacterValue ρ hρ g c`
(`Langlands.JacquetLanglands.LocalCharacter`) says that, for every Haar
measure, the Library's distribution character of the admissible
representation `ρ` equals the constant `c` times the Haar measure near
`g`.

## Statements

- `HasRegularSemisimpleCharacterValues F n`. For every complex vector
  space `V` (in a fixed universe), every admissible representation
  `ρ` of `GL_n(F)` on `V` that is irreducible, and every regular
  semisimple `g ∈ GL_n(F)` (characteristic polynomial separable,
  `IsRegularSemisimple`), there is `c : ℂ` with
  `HasCharacterValue ρ hρ g c`.

  Source: Harish-Chandra's theorem on characters, as recalled by
  Deligne–Kazhdan–Vignéras (DKV, introduction, printed p. 33, PDF
  page 37 of the registered file). For an admissible representation `π`
  the character is the distribution `φ ↦ trace π(φ)`. Harish-Chandra
  showed it is a locally constant function `χ_π` on the regular set,
  that is, `trace π(φ) = ∫ χ_π φ` when `Supp(φ) ⊂ G_rg`. Near a regular
  `g` this says the distribution is the constant `χ_π(g)` times Haar
  measure, which is `HasCharacterValue ρ hρ g (χ_π(g))`. DKV work in
  characteristic zero. In any characteristic, Badulescu 2002
  (`math0201117.tex`, lines 2774–2778) writes `χ_π` for the character
  of a smooth representation of finite length of `GL_n(F)`, "vu comme
  fonction localement constante sur l'ensemble des éléments semisimples
  réguliers", and lines 3121–3125 use that characters are constant
  near `g_V` and `g'_V`. Badulescu 2008 (`0704.2920.tex`,
  lines 374–378) states the same for every non-archimedean local field:
  `χ_π` is "a locally constant map, stable under conjugation, defined
  on the set of regular semisimple elements".

  Only the local constancy (existence of a local value at each regular
  semisimple point) is stated. Local integrability of `χ_π` on all of
  `GL_n(F)` is not needed for the character identity, which only
  compares values at regular elliptic points.

- `IrreducibleDivisionUnitsFiniteDimensional F D`. For every complex
  vector space `W` (in a fixed universe), every smooth (`IsSmooth`,
  each vector has an open stabiliser) irreducible representation of
  `Dˣ` on `W` is finite-dimensional. The conclusion does not mention
  `F`. The binders carry the hypotheses that make the statement true:
  `D` is a finite-dimensional central division algebra over the
  nonarchimedean local field `F`, with the module topology.

  Provenance (derived). The sources use characters of irreducible
  representations of `D^×` as functions at every regular point, and
  Badulescu 2002 (line 3137) uses that `D^×_v` "est compact modulo le
  centre". Neither states the finite-dimensionality as a numbered
  result. The standard argument combines two facts. First, every
  irreducible smooth complex representation of a reductive group over
  a nonarchimedean local field is admissible: Bernstein–Deligne, *Le
  "centre" de Bernstein* (in the same registered file), Corollaire 3.4
  and the remarks after it (printed p. 27, PDF page 31). `D^× = GL_1(D)`
  is such a group. Second, the open compact subgroups
  `K_k = 1 + 𝔭_D^k` form a neighbourhood basis of `1` and are normal
  in `D^×`, because the valuation of `D` is invariant under
  conjugation. A nonzero smooth `W` has a vector fixed by some `K_k`,
  so `W^{K_k} ≠ 0`. This subspace is `D^×`-stable, hence equal to `W`
  by irreducibility, and it is finite-dimensional by admissibility.

## Proved consequences

- `IrreducibleDivisionUnitsFiniteDimensional.isAdmissible`: given the
  statement, an irreducible smooth representation of `Dˣ` is
  admissible. This is `isAdmissible_of_finiteDimensional`
  (`LocalCharacter`).

- `isJacquetLanglandsPair_iff_trace`: given
  `IrreducibleDivisionUnitsFiniteDimensional F D`,
  `IsJacquetLanglandsPair F D n ρ ρ'` holds if and only if
  `finrank F D = n^2`, `ρ` is irreducible and essentially
  square-integrable, `ρ'` is irreducible and smooth, and there is an
  admissibility proof `hρ` such that for every corresponding pair
  `g ↔ g'` (`Corresponds F D g g'`),
  `HasCharacterValue ρ hρ g ((-1)^(n-1) * trace ρ'(g'))`.

  Proof. Forward: `ρ'` is smooth because it is admissible and, by the
  statement, finite-dimensional. Its character has the value
  `trace ρ'(g')` at `g'` (`hasCharacterValue_trace`), so the common
  value `c` of the relation is `trace ρ'(g')` by
  `HasCharacterValue.unique`. Backward: `ρ'` is finite-dimensional,
  hence admissible (`isAdmissible_of_finiteDimensional`), and
  `c = trace ρ'(g')` witnesses the relation's condition via
  `hasCharacterValue_trace`.

- `isJacquetLanglandsPair_iff_of_regularity`: given both statements
  (for the universes of `V` and `W`), `IsJacquetLanglandsPair F D n ρ ρ'`
  holds if and only if the same conditions on `D`, `ρ`, `ρ'` hold and,
  for every admissibility proof `hρ`, every corresponding pair
  `g ↔ g'` and every value `a` of the character of `ρ` at `g`,
  `a = (-1)^(n-1) * trace ρ'(g')`.

  This is the source formulation: `χ_ρ(g) = (-1)^(n-1) χ_ρ'(g')` with
  `χ_ρ'(g') = trace ρ'(g')`, for all `g ↔ g'`, with no existence
  clause. DKV's identity `(-1)^m χ_π'(g') = (-1)^n χ_π(g)` with
  `m = 1` is the same sign, since `(-1)^(n-1) = (-1)^(n+1)`.

  Proof. Rewrite with `isJacquetLanglandsPair_iff_trace`. Forward: a
  value `a` at `g` equals the value supplied by the relation, by
  `HasCharacterValue.unique`. Backward: `ρ` is admissible
  (`IsEssentiallySquareIntegrable.isAdmissible`). A corresponding `g`
  is regular elliptic, hence regular semisimple
  (`IsRegularElliptic.isRegularSemisimple`), so
  `HasRegularSemisimpleCharacterValues` gives a value `a` at `g`, and
  the hypothesis says `a = (-1)^(n-1) * trace ρ'(g')`.

## Scope

The two propositions are statements for later proof tasks; nothing in
the Library assumes them. They are the analytic input that objective
item 3 of Task 5443 asks to state separately from the relation. The
relation itself keeps the existence of values at corresponding points
as part of its condition, so it is meaningful without them, and the
two equivalences above show that it agrees with the source identity
whenever they hold.

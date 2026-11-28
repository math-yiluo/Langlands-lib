# Statement: completeness of the characters of `Dˣ` against square-integrable characters

The module `Langlands.JacquetLanglands.DivisionEllipticCompletenessStatement` (namespace
`Langlands.JacquetLanglands`) states, as the proposition
`DivisionEllipticCompletenessStatement.{u, uV, uW}`, that the character of an irreducible
square-integrable representation `ρ` of `GL_n(F)`, carried to the regular units of a central
division algebra `D` of dimension `n^2` through the correspondence of regular elliptic elements,
is not orthogonal on `Dˣ / Z(Dˣ)` to the character of some irreducible admissible representation
of `Dˣ` with the same central character. This is the completeness of the characters of the group
`Dˣ`, which is compact modulo its centre, applied to one function. The statement is **not
proved** here.

## Notation

- `F`, `D`, `n`, the topologies of `GL_n(F)` and `Dˣ`, the quotient `Dˣ ⧸ Z(Dˣ)` with its Borel
  σ-algebra and a Haar measure `ν` on it, `IsSquareIntegrable`, `IsRegularElliptic`,
  `IsRegular`, `Corresponds`, `HasCharacterValue` and `star` are as in
  `Langlands.JacquetLanglands.DivisionEllipticOrthogonalityStatement`. In addition `Dˣ` is
  Hausdorff, locally compact and totally disconnected (`units_t2Space`,
  `units_locallyCompactSpace`, `units_totallyDisconnectedSpace` of
  `Langlands.JacquetLanglands.DivisionUnits`), so that `HasCharacterValue` applies to
  representations of `Dˣ`.
- `HasScalarCharacter ρ z ω` (`Langlands.Representation.Classification.ConstituentRelations`)
  means `ρ (z c) v = ω(c) v` for all `c` and `v`. For `GL_n(F)` it is used with
  `GeneralLinear.scalar : Fˣ →* GL_n(F)` (scalar matrices), for `Dˣ` with
  `Units.map (algebraMap F D) : Fˣ →* Dˣ`. Both say that the centre `Fˣ` acts through `ω`.
- `SmoothRep.{0, u, uW} ℂ Dˣ` (`Langlands.Representation.Category.Basic`) is the category of
  smooth complex representations of `Dˣ` with carriers in `Type uW`; `B.representation` is the
  underlying representation.

## The statement

For all `F`, `D`, `n` with `Module.finrank F D = n ^ 2`, every Haar measure `ν` on
`Dˣ ⧸ Z(Dˣ)`, every complex vector space `V : Type uV`, every irreducible representation `ρ` of
`GL_n(F)` on `V` with `hρ : IsSquareIntegrable ρ`, every `ω : Fˣ →* ℂˣ` with
`HasScalarCharacter ρ GeneralLinear.scalar ω`, and every function `Θρ` on the regular elliptic
elements with `HasCharacterValue ρ hρ.isAdmissible g (Θρ g)` for every regular elliptic `g`,
there are

- `B : SmoothRep.{0, u, uW} ℂ Dˣ` and `hB : IsAdmissible B.representation` with
  `B.representation` irreducible and `HasScalarCharacter B.representation
  (Units.map (algebraMap F D)) ω`;
- `ΘB : Dˣ → ℂ` with `HasCharacterValue B.representation hB g' (ΘB g')` for every unit `g'`;
- `p : Dˣ ⧸ Z(Dˣ) → ℂ` with `p (g' Z) = Θρ g * conj (ΘB g')` whenever `Corresponds F D g g'`,
  `p (g' Z) = 0` whenever `g'` is not regular, `p` is `ν`-integrable, and `∫ p dν ≠ 0`.

As in `DivisionEllipticOrthogonalityStatement`, the two conditions determine `p`, and they are
consistent: elements corresponding to the same unit are conjugate, and a central factor
`a ∈ Fˣ` multiplies `Θρ` by `ω(a)` and `ΘB` by `ω(a)`, which cancel in `Θρ · conj ΘB` because
`ω` is unitary (`ρ` is square-integrable). The value `ΘB g'` is the trace of `B(g')`, because
`B` is finite-dimensional (see the proof sketch).

## Why it is true (proof sketch, not formalized)

1. **The transferred character.** Let `θ(g') = Θρ g` for `g ↔ g'` (and `0` off the regular
   set). It is a class function on `Dˣ` with `θ(a g') = ω(a) θ(g')` for `a ∈ Fˣ`. By
   Clozel's orthogonality relations (Clozel 1991, Theorem 3) and Badulescu's isometry (2002, §6),
   `θ` lies in `L²(G'_e; ω)` for `G' = Dˣ`, and its norm is the norm `1` of the character of `ρ`
   in `L²(G_e; ω)`; in the form of
   `Langlands.JacquetLanglands.DivisionEllipticOrthogonalityStatement` (with `π = ρ`),
   `∫ |θ|² dν = ν(Dˣ/Z) ≠ 0`.
2. **Completeness.** `Dˣ / Fˣ` is compact. As for compact groups (Peter–Weyl), the characters of
   the irreducible smooth representations of `Dˣ` with central character `ω` form a Hilbert basis
   of `L²(G'_e; ω)` (Badulescu 2002, §6, printed p. 745: "les caractères de toutes les
   représentations lisses irréductibles de `G` de caractère central `ω` se trouvent dans
   `L²(G_e; ω)` et forment une base hilbertienne de cet espace ... C'est le cas du groupe des
   éléments inversibles d'une algèbre à division sur `F`"; DKV, B.1.g, printed pp. 81–82: "`G'_S /
   Z_S` étant compact, on sait que les caractères forment un système complet"). By Weyl
   integration on `Dˣ / Z` (as in step 3 of the sketch for
   `DivisionEllipticOrthogonalityStatement`), the pairing `⟨ , ⟩_e` on `Dˣ` is `ν(Dˣ/Z)⁻¹` times
   the integral over `Dˣ / Z` against `ν`. Since `θ ≠ 0` in `L²`, some irreducible smooth `B` with
   central character `ω` has `∫ θ conj χ_B dν ≠ 0`.
3. **The representation `B`.** An irreducible smooth representation of `Dˣ` is admissible and
   finite-dimensional (`Dˣ / Fˣ` is compact and `B` has a central character); it can be realized
   on a space in any universe, in particular in `Type uW`. Its character has the value
   `trace B(g')` at every unit `g'` (`Langlands.JacquetLanglands.hasCharacterValue_trace`), so
   `ΘB = trace ∘ B` and `p = θ · conj χ_B` descended to `Dˣ / Z`. It is integrable because `χ_B`
   is bounded (`B` is unitarizable) and `θ ∈ L²` on the finite measure space.

## Comparison with the sources (derived content)

- **Specialized form of completeness.** Badulescu §6 gives the character basis on the
  compact-modulo-centre side and the isometry used to transfer the split character. The resulting
  `L²` norm calculation in the derivation gives a nonzero element of `L²(G'_e; ω)`. Completeness
  provides a character `ΘB` with nonzero pairing. For every Haar measure `ν`, the Lean proposition
  supplies a `ν`-integrable quotient function `p` with value `Θρ g * conj (ΘB g')` on
  corresponding regular elements, with value zero on nonregular cosets, and with `∫ p dν ≠ 0`.
  Rescaling `ν` by a positive constant preserves nonvanishing.
- **Use.** DKV B.1.g–h (printed pp. 81–82) use completeness on the compact-modulo-centre side
  and split-side orthogonality to show that the map from the division side to the split discrete
  series is surjective. A split character outside its image would pair to zero with the entire
  division character basis after transfer, forcing the transferred character to have norm zero.
- **Characters.** Characters are Harish-Chandra's functions on the regular set, encoded by
  `HasCharacterValue` (DKV, introduction, printed p. 33).

## Hypotheses

- `CharZero F`: needed for Clozel's orthogonality relations, which give `θ ≠ 0` and `θ ∈ L²`.
- `Module.finrank F D = n ^ 2`: the correspondence `g ↔ g'` relates `GL_n(F)` and `Dˣ`.
- `IsSquareIntegrable ρ` and irreducibility: the transferred character then has norm `1`.
- `HasScalarCharacter ρ GeneralLinear.scalar ω`: names the central character, which the output
  `B` shares.
- No other hypothesis is added. The universes `u` (of `F` and `D`), `uV` (of the carrier of
  `ρ`) and `uW` (of the carrier of `B`) are independent.

## Dependencies and names

The module imports `Langlands.JacquetLanglands.Relation` (`IsSquareIntegrable`,
`HasCharacterValue`, `Corresponds`, `IsRegular`, `SmoothRep`, the topological facts of
`Langlands.JacquetLanglands.DivisionUnits`) and
`Langlands.Representation.Classification.ConstituentRelations` (`HasScalarCharacter`), together
with Mathlib's local field, module topology and Bochner integral modules.

## Sources

- P. Deligne, D. Kazhdan, M.-F. Vignéras, *Représentations des algèbres centrales simples
  p-adiques*, in Bernstein–Deligne–Kazhdan–Vignéras, *Représentations des groupes réductifs sur
  un corps local*, Hermann, 1984. Source ID `bdkv-1984-representations-local-field`, SHA-256
  `c1a4b4bd79575b5b41c15e1dacaf9a8094bd05c189efed06e27c62a64d22fcc3` (printed page = PDF page
  − 4). Introduction, printed p. 33; B.1.f–h, printed pp. 81–82 (PDF pp. 85–86).
- A. I. Badulescu, *Correspondance de Jacquet–Langlands pour les corps locaux de caractéristique
  non nulle*, Ann. Sci. ÉNS (4) 35 (2002), 695–747. Source ID `badulescu-2002-jl-char-p`
  (folder; published PDF SHA-256
  `638e7134bb13c9c718ee7e5c2c9f06634637598c6ba8cd465345baf1234ed370`, printed page = PDF page
  + 694). §6 (Annexe), printed pp. 745–746 (PDF pp. 51–52).
- L. Clozel, *Invariant harmonic analysis on the Schwartz space of a reductive p-adic group*, in
  *Harmonic Analysis on Reductive Groups*, Progress in Mathematics 101, Birkhäuser, 1991. Source
  ID `provided-698170812a35ff43dbc4156af9f67a8384f95d97d5836529575e646643af617b`, SHA-256
  `c5cb36139e9cf3ed29fe1338a45488236cc69abdc4806d5ba2180456faba08ba` (printed page = PDF page
  − 11). Theorem 3, printed p. 110 (PDF p. 121).

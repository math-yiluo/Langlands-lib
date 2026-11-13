# Statements of the local Jacquet–Langlands correspondence

This module states, as propositions that are not proved here, the
local Jacquet–Langlands theorem for `GL_n(F)` and the multiplicative
group `Dˣ` of a central division algebra `D` of dimension `n^2` over a
nonarchimedean local field `F`. It is built on the relation
`IsJacquetLanglandsPair F D n ρ ρ'`
(`Langlands.JacquetLanglands.Relation`): `ρ` is irreducible and
essentially square-integrable, `ρ'` is irreducible, both are
admissible, and their distribution characters satisfy
`Θ_ρ(g) = (-1)^(n-1) Θ_ρ'(g')` at corresponding regular elliptic
`g ↔ g'`. The bundled forms `IsJacquetLanglandsSmoothPair` (on
`SmoothRep`) and `IsJacquetLanglandsClassPair` (on isomorphism classes
`SmoothRep.IsoClass`) come from the same module.

Throughout, `F` carries `IsNonarchimedeanLocalField F` and `D` is a
finite-dimensional central division `F`-algebra with its `F`-module
topology (`IsModuleTopology F D`). The carriers of representations of
`GL_n(F)` lie in a universe `uV` and those of `Dˣ` in a universe `uW`.

## Sources

- Deligne–Kazhdan–Vignéras (DKV), *Représentations des algèbres
  centrales simples p-adiques* (in Bernstein–Deligne–Kazhdan–Vignéras
  1984), introduction, printed p. 34 (PDF page 38 of the registered
  file). Théorème principal: there is a bijection `π' ↦ π` from
  `E²(G')` onto `E²(G)`, for `G' = GL(m, D)` and `G = GL(n, F)`,
  characterized by `(-1)^m χ_π'(g') = (-1)^n χ_π(g)` on corresponding
  regular elliptic elements. Here `m = 1`, so `G' = Dˣ`, and
  `(-1)^(1+n) = (-1)^(n-1)`. DKV give a complete proof when characters
  are locally integrable (Harish-Chandra, characteristic zero) and note
  Kazhdan's reduction of positive characteristic to characteristic
  zero. Item d (printed pp. 34–35, PDF pages 38–39) lists properties
  of the bijection, among them "égalité des caractères centraux"
  `ω_π' = ω_π` and "torsion par un caractère": for a character `χ` of
  `Fˣ`, `χπ` denotes the twist by `χ ∘ det` on `G` (printed p. 34) and
  by `χ ∘ Nrd` on `G'` (for `m = 1`, DKV's `dét` on `G'` is the
  reduced norm, printed p. 34), and the bijection commutes with these
  twists. DKV add (printed p. 35) that, apart from the ε-factors, these
  properties are easy: those on L-functions follow from explicit
  formulas, and "les autres se lisent sur les caractères".
  DKV write `E²` for square-integrable classes (printed p. 34). The
  statements here use essentially square-integrable classes, as
  Badulescu 2002 (line 191) and Badulescu 2008 (lines 332 and 492)
  do; Badulescu 2008 cites DKV for this form in characteristic zero
  (line 497).
- Badulescu 2002, *Correspondance de Jacquet–Langlands pour les corps
  locaux de caractéristique non nulle* (`math0201117.tex`):
  Théorème 1.1 (lines 197–203) and Théorème 5.1 (lines 2789–2799).
  For every nonarchimedean local field, there is a unique map
  `C : E²(G) → E²(G')` with `χ_π(g) = (-1)^(n-r) χ_C(π)(g')` for all
  `g ↔ g'`, and `C` is bijective. Here `r = 1`. `E²` denotes classes
  of essentially square-integrable representations (line 34 and
  lines 190–193). Lines 3569–3573 extend `C` from unitary to all `π`
  by `C(|det|^x ⊗ π^u) = |nrd|^x C(π^u)`.
- Badulescu 2008, *Global Jacquet–Langlands correspondence,
  multiplicity one and classification of automorphic representations*
  (`0704.2920.tex`), lines 485–503. The local theorem with the unique
  bijection, citing DKV in characteristic zero and Badulescu 2002 in
  nonzero characteristic. After identifying the centres of `G_{nd}` and
  `G'_n`, "the correspondence preserves central characters".
- The objective also names Rogawski for characteristic zero. Rogawski's
  1983 paper is not available in the project's literature. DKV prove
  the general characteristic-zero theorem, and Badulescu 2008
  (line 498) cites Rogawski only as a particular case, so the
  characteristic-zero statement is matched to DKV.

## Statements

- `IsJacquetLanglandsBijection F D n`. Four conjuncts about bundled
  smooth representations (`SmoothRep ℂ G`):
  1. every irreducible, essentially square-integrable `A` of `GL_n(F)`
     has some `B` of `Dˣ` with `IsJacquetLanglandsSmoothPair F D n A B`;
  2. every irreducible admissible `B` of `Dˣ` has some `A` with
     `IsJacquetLanglandsSmoothPair F D n A B`;
  3. if `A` is related to `B₁` and to `B₂`, then `B₁ ≅ B₂`;
  4. if `A₁` and `A₂` are related to `B`, then `A₁ ≅ A₂`.

  Together these say that the relation, which is invariant under
  isomorphism on both sides (Relation module), is the graph of a
  bijection between the isomorphism classes of irreducible essentially
  square-integrable representations of `GL_n(F)` and the isomorphism
  classes of irreducible admissible representations of `Dˣ`. Every
  irreducible admissible representation of `Dˣ` is essentially
  square-integrable because `Dˣ` is compact modulo its centre, so the
  right-hand side is DKV's `E²(G')` and Badulescu's `E²(G')`.
  Uniqueness of the map (DKV's "caractérisée", Badulescu's "unique")
  is contained in conjuncts 3 and 4, since the relation itself is the
  character identity.

- `JacquetLanglandsCentralCharacterCompatibility F D n`. For every
  related pair `(ρ, ρ')` there is a homomorphism `ω : Fˣ →* ℂˣ` such
  that `ρ` has central character `ω` along the scalar matrices
  (`HasScalarCharacter ρ GeneralLinear.scalar ω`, that is,
  `ρ(a · 1) v = ω(a) v`) and `ρ'` has central character `ω` along the
  centre `Fˣ ⊆ Dˣ` (`HasScalarCharacter ρ' (Units.map (algebraMap F D)) ω`).
  `HasScalarCharacter` is the Library's
  `Langlands.Classification.HasScalarCharacter`. This is DKV's
  "égalité des caractères centraux" and the
  sentence of Badulescu 2008 on central characters, with the centres of
  `GL_n(F)` and `Dˣ` both identified with `Fˣ`.

- `JacquetLanglandsTwistCompatibility F D n`. For every related pair
  `(ρ, ρ')` and every homomorphism `χ : Fˣ →* ℂˣ` with open kernel
  (a smooth character of `Fˣ`), the twists
  `twist (χ ∘ det) ρ` and `twist (χ ∘ Nrd) ρ'` are related. Here
  `twist` is the Library's `Langlands.twist`
  (`g ↦ χ(g) • ρ(g)`), `det` is `GeneralLinear.determinant`, and
  `Nrd` is the Library's reduced norm on units,
  `Langlands.BinaryElementary.Reduced.coefficientNorm F D : Dˣ →* Fˣ`
  (the canonical reduced norm of `1 ⊗ a`). This is DKV's "torsion par
  un caractère".

- `JacquetLanglandsCharZeroStatement`: for every nonarchimedean local
  field `F` of characteristic zero (`CharZero F`), every finite-
  dimensional central division algebra `D` over `F` with its module
  topology, and every `n` with `finrank F D = n^2`, the three
  statements above hold. This is DKV's Théorème principal (`m = 1`)
  with the two properties from item d named above.

- `JacquetLanglandsPositiveCharStatement`: the same conclusion for
  every nonarchimedean local field `F` of characteristic `p`, for a
  prime `p` (`CharP F p`). Bijectivity is Badulescu 2002, Théorème 1.1
  and 5.1; central characters are Badulescu 2008, lines 501–503.
  Twist compatibility is not stated separately in Badulescu 2002. It
  is included because it follows from the character identity, as DKV
  note ("se lisent sur les caractères"): if `g ↔ g'` then
  `det g = Nrd g'` (equal characteristic polynomials have equal
  constant terms), so the characters of the twisted pair are those of
  `(ρ, ρ')` multiplied near `g` and `g'` by the same number
  `χ(det g)`, while twisting by a smooth character preserves
  irreducibility, admissibility and essential square-integrability.
  Lines
  3569–3573 of Badulescu 2002 use this compatibility for `χ = |·|^x`.

The hypothesis `finrank F D = n^2` is the source's setting. The
relation itself includes it, so for other `n` the relation never holds
and conjunct 2 of the bijection would fail.

## Proved consequences

- `IsJacquetLanglandsBijection.existsUnique_right`: under the bijection
  statement, for an irreducible essentially square-integrable `A`,
  there is exactly one isomorphism class `π'` of representations of
  `Dˣ` with `IsJacquetLanglandsClassPair F D n [A] π'`. Existence is
  conjunct 1 transported to classes by
  `isJacquetLanglandsClassPair_isoClass`; for uniqueness, a class `π'`
  is represented by some `B₂` (quotient induction), which is related to
  `A`, so `B₂ ≅ B` by conjunct 3 and the classes agree by
  `SmoothRep.isoClass_eq_iff`.
- `IsJacquetLanglandsBijection.existsUnique_left`: the symmetric
  statement for an irreducible admissible `B` of `Dˣ`, using conjuncts
  2 and 4.

## Scope

The deep theorems (bijectivity, central characters, twists) are stated
for later proof tasks; nothing in the Library assumes them. The
relation compares characters through local values of the Library's
distribution characters. Its agreement with the sources' character
functions, given Harish-Chandra's regularity theorem and the
finite-dimensionality of irreducible representations of `Dˣ`, is proved
in `Langlands.JacquetLanglands.CharacterStatements`. The equality of
L- and ε-factors, contragredients and formal degrees (the other
properties in DKV item d) are not part of objective item 4 and are not
stated.

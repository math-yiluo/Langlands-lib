# Statement: elliptic orthogonality of square-integrable characters, read on `Dˣ / Fˣ`

The module `Langlands.JacquetLanglands.DivisionEllipticOrthogonalityStatement` (namespace
`Langlands.JacquetLanglands`) states, as the proposition
`DivisionEllipticOrthogonalityStatement.{u, uV}`, the orthogonality relations for the characters
of square-integrable representations of `GL_n(F)` on the elliptic set, read on the compact
quotient of the unit group of a central division algebra `D` of dimension `n^2` by its centre.
The characters are carried to the regular units of `D` through the correspondence of regular
elliptic elements, and the pairing is the integral against an arbitrary Haar measure of that
quotient. The statement is **not proved** here.

## Notation

- `F : Type u` is a nonarchimedean local field of characteristic zero (`[Field F]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]`), and
  `D : Type u` a division ring with `[Algebra F D] [FiniteDimensional F D]
  [Algebra.IsCentral F D]`, carrying its `F`-module topology (`[TopologicalSpace D]
  [IsModuleTopology F D]`); `n : ℕ` satisfies `Module.finrank F D = n ^ 2`, so `n ≥ 1`.
- `GeneralLinear n F` is `GL_n(F)` with the topology of the units of the matrix ring. The
  theorems `generalLinear_t2Space`, `generalLinear_locallyCompactSpace` and
  `generalLinear_totallyDisconnectedSpace` of `Langlands.JacquetLanglands.DivisionUnits` are
  installed as instances, as in `IsJacquetLanglandsPair`.
- `Dˣ` carries the topology of units of `D`, a topological group by `units_isTopologicalGroup`
  (`Langlands.JacquetLanglands.DivisionUnits`). `Z(Dˣ) = Subgroup.center Dˣ` is the centre; since
  `D` is central over `F`, it is the image of `Fˣ`. The quotient group `Dˣ ⧸ Z(Dˣ)` carries the
  quotient topology and the Borel σ-algebra (`borel _`). `ν` is any Haar measure on it
  (`ν.IsHaarMeasure`). The quotient is compact, so `ν` is finite and `(ν univ).toReal` is its
  total mass.
- `IsSquareIntegrable ρ` (`Langlands.JacquetLanglands.EssentiallySquareIntegrable`): `ρ` is
  admissible, has a unitary central character with open kernel, and its absolute matrix
  coefficients are square-integrable on `GL_n(F) / Z` for every Borel Haar measure there.
  `UnitaryCentralCharacter ρ` (`Langlands.Representation.MatrixCoefficient.ModuloCenter`) is a
  unitary character of `Subgroup.center (GL_n(F))` with open kernel through which the centre acts
  on `ρ`; for an irreducible `ρ` its `character` field is the central character of `ρ`.
- `IsRegularElliptic g` (`Langlands.JacquetLanglands.RegularElliptic`): the characteristic
  polynomial of `g` is separable and irreducible over `F`. `IsRegular F D g'`: the reduced
  characteristic polynomial of `g'` is separable. `Corresponds F D g g'`: `g` is regular
  elliptic, `g'` is regular, and the characteristic polynomial of `g` equals the reduced
  characteristic polynomial of `g'`; the first component `h.1` of `h : Corresponds F D g g'` is
  the proof that `g` is regular elliptic.
- `HasCharacterValue ρ hρ g c` (`Langlands.JacquetLanglands.LocalCharacter`): for every Haar
  measure `μ` on `GL_n(F)`, the distribution character of `ρ` relative to `μ` equals `c · μ` on
  the test functions supported in some neighbourhood of `g`. The value is unique
  (`HasCharacterValue.unique`).
- `star` on `ℂ` is complex conjugation.

## The statement

For all `F`, `D`, `n` as above with `Module.finrank F D = n ^ 2`, every Haar measure `ν` on
`Dˣ ⧸ Z(Dˣ)`, all complex vector spaces `V`, `W : Type uV`, all representations `ρ` of `GL_n(F)`
on `V` and `π` on `W` with `hρ : IsSquareIntegrable ρ` and `hπ : IsSquareIntegrable π`, both
irreducible, all `cρ : UnitaryCentralCharacter ρ` and `cπ : UnitaryCentralCharacter π` with
`cρ.character = cπ.character`, and all functions `Θρ`, `Θπ` on the regular elliptic elements of
`GL_n(F)` with `HasCharacterValue ρ hρ.isAdmissible g (Θρ g)` and
`HasCharacterValue π hπ.isAdmissible g (Θπ g)` for every regular elliptic `g`: there is a
function `p : Dˣ ⧸ Z(Dˣ) → ℂ` such that

1. `p (g' Z) = Θρ g * conj (Θπ g)` whenever `Corresponds F D g g'`;
2. `p (g' Z) = 0` whenever `g'` is not regular;
3. `p` is `ν`-integrable;
4. `∫ p dν = (ν univ).toReal` if `ρ` and `π` are equivalent (`Nonempty (ρ.Equiv π)`), and
   `∫ p dν = 0` otherwise.

Conditions 1 and 2 determine `p`, because every coset is `g' Z` for a unit `g'`, and every
regular `g'` corresponds to some `g ∈ GL_n(F)` (`Langlands.JacquetLanglands.exists_corresponds`,
with `n` the reduced degree of `D`). The existential records that the values are consistent:

- two elements `g₁`, `g₂` corresponding to the same `g'` have the same separable irreducible
  characteristic polynomial, so they are conjugate in `GL_n(F)`, and character values are
  invariant under conjugation;
- if `g'₂ = g'₁ z` with `z ∈ Z(Dˣ)`, then `z` is the image of some `a ∈ Fˣ`, the element `a g₁`
  corresponds to `g'₂` (if `P` is the characteristic polynomial of `g₁`, both the characteristic
  polynomial of `a g₁` and the reduced characteristic polynomial of `a g'₁` are
  `aⁿ P(X/a)`), and `Θρ (a g₁) conj (Θπ (a g₁)) =
  |ω(a)|² Θρ g₁ conj (Θπ g₁)` for the common unitary central character `ω`;
- regularity is unchanged by central factors.

The pairing is linear in the first character and conjugate linear in the second.

## Why it is true (proof sketch, not formalized)

1. **Clozel's orthogonality on `GL_n(F)`.** Clozel 1991, Theorem 3 (printed p. 110): for two
   square-integrable representations `π₁`, `π₂` of `G = GL_n(F)` with the same central character,
   `Σ_T |W(G,T)|⁻¹ ∫_{Z\T} |D(γ)| Θ_{π₁}(γ) conj Θ_{π₂}(γ) dγ` is `1` if `π₁ ≅ π₂` and `0`
   otherwise. The sum runs over the elliptic maximal tori `T` up to conjugacy, `W(G,T)` is the
   rational Weyl group, `D` the Weyl discriminant, and `dγ` the Haar measure giving mass `1` to
   `Z\T` (Clozel's Remark after Theorem 3). Clozel prints the conjugate on the first character;
   both possible values are real, so the identity also holds with the conjugate on the second.
   This is Badulescu's `⟨χ_{π₁}, χ_{π₂}⟩_e = δ` (2002, §6, printed p. 745). The integrals
   converge absolutely by Clozel's Proposition 4 (`|D|^{1/2} |Θ|` is bounded on each elliptic
   torus, which is compact modulo `Z`).
2. **Transfer of tori.** Badulescu 2002, §6 (printed pp. 745–746): if `g ↔ g'`, the
   `F`-algebra isomorphism `F[g] ≃ F[g']` sending `g` to `g'` gives an isomorphism of the
   centralizers `F[g]ˣ ≃ F[g']ˣ`, maximal tori of `GL_n(F)` and of `Dˣ`. This gives a bijection
   `T ↦ T'` between the conjugacy classes of elliptic maximal tori of `GL_n(F)` and the
   conjugacy classes of maximal tori of `Dˣ` (all of which are elliptic), with isomorphisms
   `j_T : T ≃ T'` that are the identity on `Z = Fˣ`, hence preserve the Haar measures giving
   mass `1` to `T/Z` and `T'/Z`. Both `W(G,T)` and `W(Dˣ,T')` are the automorphism group of the
   extension `F[g]/F` (Skolem–Noether), and the Weyl discriminant is a function of the
   characteristic polynomial, so `D(t) = D(j_T(t))`. Hence the elliptic pairing of the
   characters of `π₁`, `π₂` equals the elliptic pairing on `Dˣ` of the transferred functions
   `θ_i(g') = Θ_{π_i}(g)` (Badulescu's isometry `i : L²(G_e; ω) ≃ L²(G'_e; ω)`).
3. **Weyl integration on `Dˣ / Z`.** The Weyl integration formula (Henniart–Lemaire 2011, II.2.10,
   formula (2), printed p. 72, for `GL_n(F)`; it follows from Harish-Chandra's Lemma 42 of his
   Chapter VII, which applies to any connected reductive group, here the inner form `Dˣ` of
   `GL_n`), applied on `Dˣ / Z` to the `Z`-invariant class function `φ = θ_1 conj θ_2`, gives
   `∫_{Dˣ/Z} φ dν = Σ_{T'} |W(Dˣ,T')|⁻¹ ∫_{T'/Z} |D(t)| (∫_{Dˣ/T'} φ(x t x⁻¹) dẋ) dt`, with
   `dt` of mass `1` on `T'/Z` and `dẋ` the quotient of `ν` by `dt`. Since `Dˣ/Z` is compact,
   `dẋ` has total mass `ν(Dˣ/Z)`, and the inner integral of the class function `φ` is
   `ν(Dˣ/Z) φ(t)`. Therefore `∫ p dν = ν(Dˣ/Z) · ⟨θ_1, θ_2⟩_e`, which by steps 1 and 2 is
   `ν(Dˣ/Z)` or `0`. The same computation with `|φ|` and step 1's absolute convergence gives the
   integrability of `p`. The non-regular units, where `p = 0`, form a `ν`-null set.

## Comparison with the sources (derived content)

- **Transported form.** Clozel states the orthogonality on the elliptic tori of `GL_n(F)` with
  explicit measures. Badulescu (§6) transports it to `Dˣ` by the isomorphism `i` and notes that
  the elliptic pairing on a group that is compact modulo its centre is the integral over the
  quotient. The statement records the result in this transported form: as an integral over
  `Dˣ / Z(Dˣ)` against an arbitrary Haar measure `ν`, with the total mass `(ν univ).toReal` as the
  value on the diagonal. The Haar measure on the compact quotient is unique up to a positive
  scalar, so no normalization of `ν` is needed; Clozel's normalized identity is the case
  `ν(Dˣ/Z) = 1`.
- **Relation to `Langlands.BaseChange.EllipticCharacterOrthogonalityStatement`.** That Library
  statement asserts Clozel's Theorem 3 on `GL_n(F)` with some measure on `GL_n(F)/Z` that
  realizes the elliptic pairing; it does not identify the measure. The present statement fixes
  the pairing through the Haar measure of `Dˣ / Z(Dˣ)`, which is what a comparison with
  representations of `Dˣ` requires. Neither statement is derived from the other in the Library.
- **Characters.** Characters are Harish-Chandra's locally constant functions on the regular
  set, encoded by `HasCharacterValue` (DKV, introduction, printed p. 33); Clozel §3 (printed
  p. 107) recalls that they exist and are locally integrable in characteristic zero.
- **Square-integrable representations.** Clozel's square-integrable representations are
  irreducible unitary representations with matrix coefficients square-integrable modulo `Z`;
  their smooth vectors are the irreducible admissible representations with `IsSquareIntegrable`,
  with the same characters, and equivalence corresponds (see the Markdown of
  `Langlands.BaseChange.EllipticCharacterOrthogonalityStatement`).
- **Use.** The relation is the orthogonality input of DKV, B.1.f (printed p. 81, "les formules
  d'orthogonalité des caractères ... vraies pour `G_S` si les caractères sont localement `L¹`")
  and of Badulescu's proof of surjectivity (§5, printed p. 741).

## Hypotheses

- `CharZero F`: Clozel's Theorem 3 is proved in characteristic zero, where Harish-Chandra's
  local integrability theorem holds; the Library's regularity notions (separable characteristic
  polynomials) are the sources' in characteristic zero.
- `Module.finrank F D = n ^ 2`: `D` has reduced degree `n`, so the correspondence `g ↔ g'`
  relates `GL_n(F)` and `Dˣ`.
- Equal unitary central characters: the hypothesis of Clozel's theorem, and what makes the
  product of characters invariant under `Z`.
- No other hypothesis is added. The carriers `V` and `W` lie in the same universe `uV`, and the
  universe `u` of `F` and `D` is independent of it.

## Dependencies and names

The module imports `Langlands.JacquetLanglands.Relation`, which provides
`IsSquareIntegrable`, `HasCharacterValue`, `IsRegularElliptic`, `IsRegular`, `Corresponds`,
`UnitaryCentralCharacter` and the topological facts of `Langlands.JacquetLanglands.DivisionUnits`,
together with Mathlib's local field, module topology and Bochner integral modules. The
proposition is written with `classical` so that `if Nonempty (ρ.Equiv π) then … else …` is
decidable.

## Sources

- L. Clozel, *Invariant harmonic analysis on the Schwartz space of a reductive p-adic group*, in
  W. H. Barker and P. J. Sally (eds.), *Harmonic Analysis on Reductive Groups*, Progress in
  Mathematics 101, Birkhäuser, 1991. Source ID
  `provided-698170812a35ff43dbc4156af9f67a8384f95d97d5836529575e646643af617b`, SHA-256
  `c5cb36139e9cf3ed29fe1338a45488236cc69abdc4806d5ba2180456faba08ba` (printed page = PDF page
  − 11). §3, printed p. 107 (characters, Proposition 4); Theorem 3 with its Remark and proof,
  printed pp. 110–111 (PDF pp. 121–122).
- A. I. Badulescu, *Correspondance de Jacquet–Langlands pour les corps locaux de caractéristique
  non nulle*, Ann. Sci. ÉNS (4) 35 (2002), 695–747. Source ID `badulescu-2002-jl-char-p`
  (folder; published PDF SHA-256
  `638e7134bb13c9c718ee7e5c2c9f06634637598c6ba8cd465345baf1234ed370`, printed page = PDF page
  + 694). §6 (Annexe), printed pp. 745–746 (PDF pp. 51–52): the space `L²(G_e; ω)`, the pairing
  `⟨ , ⟩_e`, Clozel's orthonormality, the case `G/Z` compact, and the isometry
  `i : L²(G_e; ω) ≃ L²(G'_e; ω)`; §5, "Surjectivité", printed p. 741 (PDF p. 47).
- P. Deligne, D. Kazhdan, M.-F. Vignéras, *Représentations des algèbres centrales simples
  p-adiques*, in Bernstein–Deligne–Kazhdan–Vignéras, *Représentations des groupes réductifs sur
  un corps local*, Hermann, 1984. Source ID `bdkv-1984-representations-local-field`, SHA-256
  `c1a4b4bd79575b5b41c15e1dacaf9a8094bd05c189efed06e27c62a64d22fcc3` (printed page = PDF page
  − 4). Introduction, printed p. 33; B.1.f, printed p. 81 (PDF p. 85).
- G. Henniart, B. Lemaire, *Changement de base et induction automorphe pour `GL_n` en
  caractéristique non nulle*, Mém. SMF 124 (2011). Source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, SHA-256
  `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0` (printed page = PDF page
  − 8). II.2.10, formula (2) and the remark after it, printed p. 72 (PDF p. 80): the Weyl
  integration formula and its source in Harish-Chandra.

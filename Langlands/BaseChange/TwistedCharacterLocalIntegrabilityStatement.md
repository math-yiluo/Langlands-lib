# Local integrability of twisted characters of `GL_n(E)` (statement 5)

The module `Langlands.BaseChange.TwistedCharacterLocalIntegrabilityStatement` states, as the
proposition `TwistedCharacterLocalIntegrabilityStatement.{u, v, uW}`, that for a cyclic
algebra `E` over a nonarchimedean local field `F` of characteristic zero, the twisted
character of an irreducible admissible representation of `GL_n(E)` is a locally integrable
function that is locally constant on the σ-regular set. The statement is **not** proved here.
The module also proves lemma 5′: the statement gives the Library's
`TwistedCharacterRegularValuesStatement`.

## Sources

- Clozel, "Characters of non-connected, reductive p-adic groups", Canad. J. Math. 39
  (1987), 149–167, source ID `clozel-1987-nonconnected-characters` (PDF page = printed page −
  148). §3.3, Theorem 1, printed p. 153: in characteristic zero, the character of an
  irreducible admissible representation of a non-connected reductive p-adic group is a
  locally integrable function, locally constant on the regular set. With Arthur–Clozel's
  Proposition 2.2 (below), this is the proof of statement 5 named here, for a cyclic field
  extension `E/F`; cyclic algebras are reached by HL II.2.8 (see "Cyclic algebras").
- Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*
  (1989), source ID `arthur-clozel-1989-base-change` (PDF page = printed page + 14).
  Chapter 1, Proposition 2.2, printed p. 11: they apply Clozel's theorem to the non-connected
  group `G(E) ⋊ ⟨σ⟩` for a cyclic field extension `E/F` of fields of characteristic zero. The
  twisted character `trace(Π(φ) I_σ)` is given by a locally integrable function, locally
  constant near σ-regular elements.
- Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, cited as HL
  (PDF page = printed page + 8). HL work in positive characteristic (Chapter I, printed
  p. 5). They are cited for the formulation of statement 5 and for the reduction from
  cyclic algebras to fields, not as a proof of local integrability.
  - I.5.1, printed pp. 28–30, in the setting of sections I.4–I.5, where `E/F` is an
    unramified field extension (I.4.1, printed p. 26): the twisted distribution
    `⟨φ, Θ^A_π⟩ = trace(π(φ dg_E) ∘ A)`, the uniqueness of `A` up to a scalar for
    irreducible `π` and, after their [60] (Lemaire 2004, Théorème 7.1), its local
    integrability and local constancy on `G(E)_{σ-r}` (p. 29); the Proposition (p. 30, a
    variant for finite length) and Remarque 2 (p. 30: the function depends neither on `dg_E`
    nor on the representative of the isomorphism class of `(π, A)`).
  - II.1.3, printed pp. 56–57, in the setting of Chapter II, where `E/F` is a finite cyclic
    field extension (printed p. 55): the same for a σ-stable `Π` of `G(E)` of finite length
    with `A ∘ Π(g) = Π(g^σ) ∘ A`, again after [60]. This is the cyclic-field form of
    statement 5.
  - II.2.8, printed pp. 67–69: the extension to a cyclic algebra `E = E₁^r`, a product of
    copies of a cyclic field extension (see below).
- Lemaire, "Intégrabilité locale des caractères tordus de `GL_n(D)`", J. reine angew. Math.
  566 (2004), 1–39, source ID `lemaire-2004-twisted-character-local-integrability` (PDF page =
  printed page), HL's reference [60]. Setting (Introduction, printed p. 1): `F` a
  nonarchimedean local field of any characteristic, `E/F` a cyclic Galois field extension of
  degree `l` with generator `σ`, `D` a central division algebra; `x` is σ-regular when the
  reduced characteristic polynomial of `N(x) = x x^σ ⋯ x^{σ^{l-1}}` is a product of pairwise
  distinct irreducible polynomials. Théorème 7.1, printed p. 38: for every irreducible
  σ-stable smooth representation `π` of `G_E`, the twisted character
  `Θ_{π,σ} = trace(π ∘ I_{π,σ})` is a locally integrable distribution on `G_E`, locally
  constant near the σ-regular elements. For `D = F` this is the form of statement 5 when `E`
  is a field. It is where HL take the result from. Its proof in positive characteristic is
  disputed (see "Hypotheses"), and it is not cited here as the proof of statement 5.
- Aizenbud, Gourevitch, Kazhdan and Sayag, "On Harish-Chandra's integrability theorem in
  positive characteristic", arXiv:2602.16389 (2026), source ID
  `aizenbud-gourevitch-kazhdan-sayag-2026-integrability-positive-characteristic`, §1.2.1 and
  Appendix B (printed pp. 3–4 and 56): the arguments of Lemaire's papers of 1996, 2004 and
  2005 in arbitrary characteristic have a flaw (see "Hypotheses").

## Statement

`TwistedCharacterLocalIntegrabilityStatement.{u, v, uW}` quantifies over exactly the data of
`TwistedCharacterRegularValuesStatement`:

- a field `F : Type u` with `[ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]`;
- a commutative `F`-algebra `E : Type v` with `[TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E]`;
- `σ : E ≃ₐ[F] E` and `l n : ℕ` with `hE : IsCyclicAlgebra σ l`
  (`Langlands/BaseChange/Norm.lean`).

`E` is then a finite `F`-module (`hE.1`), and the Library theorems
`generalLinear_t2Space_of_finite`, `generalLinear_locallyCompactSpace_of_finite` and
`generalLinear_totallyDisconnectedSpace_of_finite` (`Langlands/BaseChange/TwistedCharacter.lean`)
supply the topological instances on `GL_n(E)`, bound with `haveI` inside the statement.

The claim: for every complex vector space `W : Type uW`, every
`τ : Representation ℂ (GL_n(E)) W` with `hτ : IsAdmissible τ` and `τ.IsIrreducible`, and every
`A : SigmaIntertwiner σ n τ` (an isomorphism of `τ` onto `τ^σ = τ ∘ entrywiseAut σ n`), there is
`Θ : GL_n(E) → ℂ` with `IsTwistedCharacterFunction τ hτ A.toLinearMap Θ` (definition 1 of
`Langlands.BaseChange.CharacterFunction`: for every Haar measure `μ`, `Θ` is locally
integrable and `trace(τ(φ) ∘ A) = ∫ φ Θ dμ` for every test function `φ`) such that
`∀ᶠ x in nhds δ, Θ x = Θ δ` for every `δ` with `IsSigmaRegular σ l δ`. HL's `Π` is written
`τ` in Lean, as in `Langlands.BaseChange.TwistedCharacter`.

## Lemma 5′ (proved)

`TwistedCharacterLocalIntegrabilityStatement.regularValues`: statement 5 gives
`TwistedCharacterRegularValuesStatement.{u, v, uW}`. Proof: for `τ`, `A` and σ-regular `δ`,
take the function `Θ` of statement 5; it is locally constant near `δ`, so by
`IsTwistedCharacterFunction.hasTwistedCharacterValue` the number `Θ δ` is the twisted character
value at `δ`. A proof of statement 5 therefore also proves
`TwistedCharacterRegularValuesStatement`.

## Use

- The direction `IsShintaniLift → IsSigmaLift` of `SigmaLiftCharacterIdentityStatement`
  needs statements 4–5 (`CharacterLocalIntegrabilityStatement` and this statement) for all
  test functions, not only for
  those supported in the regular set.
- The nonvanishing input of the global comparison for local cyclic base change
  (`TwistedTraceRegularNonvanishingStatement`: a σ-stable irreducible
  `Π` and a bijective `A` admit `φ` supported in the σ-regular set with
  `trace(Π(φ) ∘ A) ≠ 0`) needs statement 5 together with statement 7
  (`SigmaRegularOpenConullStatement`): statement 5 represents the twisted distribution by a
  function that is locally constant on the σ-regular set, and statement 7 says that this set
  is open and that its complement contributes nothing to the integrals.
- The Weyl integration formulas for locally integrable invariant functions (HL II.2.10,
  printed pp. 70–72) are applied to the functions of statements 4–5.

## Hypotheses

Statement 5 assumes `CharZero F`. This scope is shared with
`TwistedCharacterRegularValuesStatement` and other base-change statements of the
Library. In this scope the proof named here is Clozel's Theorem 1 with Arthur–Clozel's
Proposition 2.2, both in characteristic zero, for a cyclic field extension `E/F`, together
with the reduction of HL II.2.8 for cyclic algebras (see "Cyclic algebras"). The two
regularity conventions also coincide there. The Library's `IsSigmaRegular σ l δ` asks for an
associated `γ` that is `IsRegularSemisimple`, that is, has a separable characteristic
polynomial. Lemaire and HL (II.1.2, printed p. 56) call `γ` regular when its characteristic
polynomial is squarefree, and call `δ` σ-regular when every associated `γ` is regular. Over
perfect fields, in particular in characteristic zero, separable and squarefree agree.

Nothing is stated or claimed in positive characteristic. The papers that claim a proof
there are Lemaire 2004 (twisted characters of `GL_n(D)`, any characteristic) and, for
ordinary characters of `GL_N`, Lemaire, Compositio Math. 100 (1996), 41–75 (HL's [59], not in
the project literature). HL (I.5.1 and II.1.3) take the twisted result from Lemaire 2004.
Aizenbud, Gourevitch, Kazhdan and Sayag (arXiv:2602.16389, §1.2.1 and Appendix B, printed
pp. 3–4 and 56) state that the arguments of Lemaire 1996, Lemaire 2004 and Lemaire 2005 in
arbitrary characteristic have a flaw. Their key step, Lemma 2.3.2 of Lemaire 1996 (a
submersion replacing the Luna slice at closed orbits that are not semisimple), is formulated
inconsistently, and its consistent version, Lemma 5.4.2 of Lemaire's Mémoire SMF 70 (1997),
is false as stated. So neither Lemaire 2004 nor HL's statements resting on it are cited here
as a proof of local integrability of twisted characters in positive characteristic.
Statement 7 is made in every characteristic and assumes nothing more. Its justification, the
discriminant argument in `RegularSetOpenConullStatement`, does not use Lemaire's work.

## Every `A`

For irreducible `τ` the isomorphism `A` of `τ` onto `τ^σ` is unique up to a nonzero scalar
(HL I.5.1, printed p. 29), and lemma `IsTwistedCharacterFunction.smul` transports the
function: if `Θ` represents the twisted character of `A`, then `x ↦ a * Θ x` represents that of
`a • A`. Statement 5 nevertheless quantifies over every `A`, so that no choice (for instance
HL's normalization `A^l = id` or Arthur–Clozel's Whittaker normalization) is needed.

## Cyclic algebras

Clozel's Theorem 1 as applied in Arthur–Clozel's Proposition 2.2, Lemaire 2004 and HL II.1.3
(printed pp. 56–57) treat a cyclic field extension `E/F`; the extension to cyclic algebras is
HL II.2.8. For a cyclic algebra `E = E₁^r`
(`E₁/F` a cyclic field extension of degree `l / r`), HL II.2.8 (printed pp. 67–69) identify
`GL_n(E)` with `GL_n(E₁)^r`, write a σ-stable irreducible representation as `Π₁^{⊗ r}` with a
cyclic-shift intertwiner built from an intertwiner `A₁` of `Π₁` (for `σ₁`, the restriction of
`σ^r` to `E₁`), and show that the twisted character of `GL_n(E)` is
`Θ^A_Π(δ) = Θ^{A₁}_{Π₁}(N'₁(δ))` with the partial norm `N'₁(δ₁, …, δ_r) = δ₁ ⋯ δ_r`, a
δ being σ-regular exactly when `N'₁(δ)` is σ₁-regular. In the split case `E = F^l`
(`E₁ = F`, `σ₁ = id`) this reduction ends at the ordinary character of `GL_n(F)`, that is,
at statement 4. In characteristic zero the field case `GL_n(E₁)` needed by this reduction is
Clozel's theorem with Arthur–Clozel's Proposition 2.2 when `E₁ ≠ F`, and Harish-Chandra's
theorem (statement 4) when `E₁ = F`. The statement is made for every `E` with
`IsCyclicAlgebra σ l`, the
characterization in `Langlands.BaseChange.Norm` of HL's cyclic algebras, as in
`TwistedCharacterRegularValuesStatement`.

## Not stated here

No Weyl integration formula, no character expansion near singular points, no finite-length
version (HL I.5.1, Proposition), no invariance of `Θ` under σ-conjugation (HL I.5.1,
Remarque 2) and no statement in positive characteristic.

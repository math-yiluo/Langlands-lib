# Twisted characters have values at σ-regular elements

The module `Langlands.BaseChange.TwistedCharacterRegularValuesStatement` states, as the
proposition `TwistedCharacterRegularValuesStatement.{u, v, uW}`, that the twisted character of
an irreducible admissible representation of `GL_n(E)` has a value at every σ-regular element.
It is the twisted analogue of the Library's `HasRegularSemisimpleCharacterValues`
(`Langlands/JacquetLanglands/CharacterStatements.lean`). The statement is **not** proved here.

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`. PDF page =
  printed page + 8. Cited as HL. II.2.8, printed pp. 67–69: for `Π₁` of finite length, the
  twisted character `Θ^{A₁}_{Π₁}` is locally constant on `G(E₁)_{σ₁-r}` and locally
  integrable (their reference [60] and their I.5.1). For a cyclic algebra `E = E₁ × ⋯ × E_r`
  the twisted character of `Π = Π₁^{⊗ r}` is `Θ^A_Π(δ) = Θ^{A₁}_{Π₁}(N'₁(δ))`, a locally
  constant function on `G(E)_{σ-r}`. II.1.3, printed p. 57, recalls the same for a field `E`.
- Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
  Formula* (1989), source ID `arthur-clozel-1989-base-change`, Chapter 1, Proposition 2.2,
  printed p. 11. In characteristic zero, for a cyclic extension of local fields, the
  twisted character is given by a locally integrable function that is locally constant in
  the neighbourhood of σ-regular elements. They deduce it from Clozel, *Characters of
  non-connected, reductive p-adic groups* (1987), which is not in the project's literature.

## Statement

`TwistedCharacterRegularValuesStatement.{u, v, uW}` quantifies over the following data:

- a field `F : Type u` with `[ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]`, a nonarchimedean local field of
  characteristic zero;
- a commutative `F`-algebra `E : Type v` with `[TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E]`;
- `σ : E ≃ₐ[F] E` and `l n : ℕ` with `IsCyclicAlgebra σ l` (module
  `Langlands.BaseChange.Norm`).

Under these, `E` is a finite `F`-module (the first component of `IsCyclicAlgebra`), and
`generalLinear_t2Space_of_finite`, `generalLinear_locallyCompactSpace_of_finite` and
`generalLinear_totallyDisconnectedSpace_of_finite` (lemma 9 of
`Langlands.BaseChange.TwistedCharacter`) supply the topological instances on `GL_n(E)`.
These instances are introduced with `haveI` inside the statement.

The claim is the following. For every complex vector space `W : Type uW`, every
`τ : Representation ℂ (GL_n(E)) W` with `hτ : IsAdmissible τ` and `τ.IsIrreducible`, every
`A : SigmaIntertwiner σ n τ` (an isomorphism of `τ` onto `τ^σ`) and every `δ : GL_n(E)` with
`IsSigmaRegular σ l δ`, there is `c : ℂ` with `HasTwistedCharacterValue τ hτ A δ c`. Here `A`
enters through its underlying linear map. In words: near every σ-regular `δ` the twisted
character `Θ^A_τ` is the constant `c` times Haar measure, for every Haar measure.

Only the existence of a value at each σ-regular point, that is local constancy, is stated.
Local integrability of the twisted character on all of `GL_n(E)`, also proved by HL and
Arthur–Clozel, is not part of this statement. HL state the result for representations of
finite length. The statement only asks for irreducible ones, a special case. As in item 3 of
`TwistedCharacter`, HL's `Π` is written `τ` in Lean.

## The hypothesis `CharZero F`

`IsSigmaRegular σ l δ` (`Langlands.BaseChange.Norm`) asks for an associated `γ` that is `IsRegularSemisimple`,
the Library's notion: the characteristic polynomial is separable (HL's `G(F)'`). HL call
`γ` regular when its characteristic polynomial is squarefree, a product of pairwise distinct
irreducible polynomials (II.1.2, printed p. 56). The two agree over perfect fields, in
particular in characteristic zero (Mathlib's `PerfectField.separable_iff_squarefree`).
There HL's σ-regular set `G(E)_{σ-r}` and the Lean condition coincide, and HL's results (and
those of Arthur–Clozel, who work in characteristic zero) apply verbatim. The hypothesis
`[CharZero F]` is made for this reason, as in `Langlands.BaseChange.RegularTransferStatement`.

## Cyclic algebras

HL's Chapter II takes `E` to be a cyclic field extension of `F` in II.1 (printed pp. 55–57).
From II.2.1 on (printed p. 61) it allows a cyclic `F`-algebra `E = E₁ × ⋯ × E_r`, and in
II.2.8 (printed pp. 67–68) it treats twisted characters for such `E` by reduction to the
field `E₁`. The base change argument needs the algebra case, for instance at split places.
The statement is therefore made for every `E` with `IsCyclicAlgebra σ l`, the
characterization in `Langlands.BaseChange.Norm` of HL's cyclic algebras.

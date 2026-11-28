# Twisted elliptic orbital integrals of cut-off supercuspidal coefficients

The module `Langlands.BaseChange.SupercuspidalCoefficientEllipticOrbitalStatement` states, as
the proposition `SupercuspidalCoefficientEllipticOrbitalStatement.{u, v, uW}`, that for an
irreducible supercuspidal representation `τ` of `GL_n(E)` with an isomorphism `A` of `τ` onto
`τ^σ`, the σ-twisted conjugates of a coefficient of the contragredient of `τ` around a
σ-elliptic element `δ`, integrated over `GL_n(E)` against the determinant window normalized over
the scalars `F^×`, give the value at `δ⁻¹` of the twisted character of `A⁻¹` times the twisted
trace `tr(τ(φ) ∘ A)` of the cut-off coefficient `φ`. The module states the proposition and does
not prove it.

## Notation (Library and Mathlib)

- `IsCyclicAlgebra σ l` (module `Langlands.BaseChange.Norm`): `E` is a finite `F`-algebra of
  dimension `l`, reduced, `σ` has order `l` and its fixed points are `F`. `entrywiseAut σ n x`
  is `x^σ`, the entrywise action of `σ` on `GL_n(E)`. `IsNormAssociated σ l δ γ`: the norm
  `N(δ) = δ δ^σ ⋯ δ^{σ^{l-1}}` is conjugate in `GL_n(E)` to `γ ∈ GL_n(F)`.
- `IsRegularElliptic γ` (module `Langlands.JacquetLanglands.RegularElliptic`): the
  characteristic polynomial of `γ` is irreducible and separable.
- `SigmaIntertwiner σ n τ` (module `Langlands.BaseChange.TwistedCharacter`): linear automorphisms
  `A` of `W` with `A τ(g) = τ(g^σ) A`; `A.symm.toLinearMap` is `A⁻¹`.
- `HasTwistedCharacterValue τ hτ.1 B g Θ` (module `Langlands.BaseChange.TwistedCharacter.Basic`):
  for every Haar measure `μ`, the distribution `f ↦ tr(τ(f) ∘ B)` equals `Θ ∫ f dμ` on a
  neighbourhood of `g`.
- `twistedDistribution μE τ hτ.1 A.toLinearMap φ = tr(τ(φ) ∘ A)` with
  `τ(φ) = ∫ φ(x) τ(x) dμE(x)`.
- `determinantWindow F (n * l)` (module `Langlands.BaseChange.DeterminantWindow`): the indicator
  of `0 ≤ ord_F N_{E/F}(det x) < n l`.

## Statement

`SupercuspidalCoefficientEllipticOrbitalStatement.{u, v, uW}` quantifies over a field
`F : Type u` with `[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
[CharZero F]`, a field `E : Type v` with `[Algebra F E] [TopologicalSpace E]
[IsTopologicalRing E] [IsModuleTopology F E]`, `σ : E ≃ₐ[F] E` and `l n : ℕ` with
`IsCyclicAlgebra σ l` and `0 < n`; `GL_n(E)` carries its locally compact topology and the Borel
σ-algebra. Write `b = determinantWindow F (n * l)`. For every irreducible
`τ : Representation ℂ (GeneralLinear n E) W` (`W : Type uW`) with
`hτ : GeneralLinear.IsSupercuspidal τ`, every `A : SigmaIntertwiner σ n τ`, every Haar measure
`μE` on `GL_n(E)`, every `v : W`, every `ℓ : SmoothDual τ` and every Schwartz–Bruhat `φ` with
`φ x = b x * ℓ (τ x⁻¹ v)` for all `x`, and for every `δ ∈ GL_n(E)` and `γ ∈ GL_n(F)` with
`IsNormAssociated σ l δ γ` and `IsRegularElliptic γ`, and every `Θ : ℂ` with
`HasTwistedCharacterValue τ hτ.1 A.symm.toLinearMap δ⁻¹ Θ`:

1. the function `x ↦ b x * ℓ (τ (x⁻¹ * δ * x^σ)⁻¹ v)` on `GL_n(E)` has compact support;
2. `∫ x, b x * ℓ (τ (x⁻¹ * δ * x^σ)⁻¹ v) ∂μE = Θ * twistedDistribution μE τ hτ.1 A.toLinearMap φ`.

With `E = F`, `σ = 1`, `l = 1` and `A` the identity, `IsNormAssociated 1 1 γ γ` holds for every
`γ`, the twisted character of the identity is the character
(`hasTwistedCharacterValue_one_iff`), and the statement says that
`∫ b(x) λ(π(x⁻¹ γ x)⁻¹ v) dμF(x) = Θ_π(γ⁻¹) tr π(φ)` for an irreducible supercuspidal
representation `π` of `GL_n(F)` and a regular elliptic `γ`.

## Why it is true

Write `c(y) = λ(τ(y)⁻¹ v)`. Since `τ(x^σ) = A τ(x) A⁻¹`,

`c(x⁻¹ δ x^σ) = (λ ∘ A)(τ(x)⁻¹ A⁻¹ τ(δ⁻¹) τ(x) v)`.

1. *Compact support.* The σ-centralizer `T_δ = G^σ_δ(F)` of a σ-elliptic `δ` is conjugate in
   `GL_n(E)` to the centralizer `G_γ(F) ≅ F[γ]^×` (Henniart–Lemaire 2011, I.2.7, printed
   pp. 20–21), so `T_δ / F^×` is compact, and σ-elliptic σ-conjugacy classes are closed with
   proper orbit maps modulo the centre. The coefficient `c` is compactly supported modulo the
   centre (Renard 2026, VI.2.1), so `{x : c(x⁻¹ δ x^σ) ≠ 0} ⊆ T_δ C` for a compact `C`; the
   window bounds `ord_F N_{E/F}(det x)` and therefore cuts `T_δ C` down to a compact set.
2. *Smearing.* Let `h` be locally constant with support in a small compact open neighbourhood
   `Ω` of `δ` in the σ-elliptic set, which is open (`isOpen_setOf_isSigmaElliptic`). Here the
   compactness of step 1 is needed locally uniformly in `δ`: the set of `x` with `b(x) ≠ 0` and
   `c(x⁻¹ y x^σ) ≠ 0` for some `y ∈ Ω` must be relatively compact. This does not follow from
   the closedness of the single twisted orbit of `δ` (in the Library,
   `isClosed_range_twistedConj_of_regularNorm` and
   `continuous_hasCompactSupport_cyclicTwistedOrbitFunction`, module
   `Langlands.BaseChange.RegularCyclicTwistedOrbit`); it is the twisted form of Harish-Chandra's
   compactness lemma for compact sets of elliptic regular elements, applied to the elements
   `y ⋊ σ` of `GL_n(E) ⋊ ⟨σ⟩`, and a proof of the statement has to establish it. Granting it,
   `(x, y) ↦ b(x) h(y) c(x⁻¹ y x^σ)` is bounded with support of finite measure, and Fubini
   gives `∫_Ω h(y) I(y) dμE(y) = ∫_G b(x) (λ ∘ A)(τ(x)⁻¹ A⁻¹ τ(ȟ) τ(x) v) dμE(x)`, where
   `I(y) = ∫_G b(x) c(x⁻¹ y x^σ) dμE(x)`, `ȟ(y) = h(y⁻¹)` and `τ(ȟ)` has finite rank
   (admissibility; `GL_n(E)` is unimodular).
3. *Schur orthogonality.* Writing the finite-rank operator `A⁻¹ τ(ȟ)` as `Σ_i λ_i(·) u_i` with
   smooth `λ_i`, Schur orthogonality for the window cut-off (the computation of
   `Langlands/BaseChange/SupercuspidalWindowSchurOrthogonalityStatement.md`, which gives
   `∫_G b(x) λ'(τ(x)⁻¹ w) λ''(τ(x) u) dμE(x) = d λ'(u) λ''(w)`) yields
   `∫_Ω h I dμE = d λ(A v) tr(A⁻¹ τ(ȟ)) = d λ(A v) tr(τ(ȟ) ∘ A⁻¹)`.
4. *Character value.* If `Ω⁻¹` lies in the neighbourhood of `δ⁻¹` on which
   `f ↦ tr(τ(f) ∘ A⁻¹)` equals `Θ ∫ f dμE`, then `tr(τ(ȟ) ∘ A⁻¹) = Θ ∫ h dμE`. The function
   `I` is locally constant on `Ω` (`φ`-type coefficients are invariant under an open subgroup,
   uniformly over the relevant compact set of `x`), so `I(δ) = Θ d λ(A v)`. Finally
   `τ(φ) ∘ A = d (u ↦ λ(A u) v)`, whose trace is `d λ(A v)`.

## Sources and provenance

The proposition is formulated for this Library (derived). It is step 3 of the proof sketch of
`Langlands.BaseChange.SupercuspidalCoefficientEllipticMatchingStatement`, written without
quotient measures: the integral over `GL_n(E)` against the window replaces the integral over
`F^× \ GL_n(E)`. Its untwisted case is the relation between elliptic orbital integrals and
characters of contragredients in Henniart–Lemaire 2011 (*Changement de base et induction
automorphe pour `GL_n` en caractéristique non nulle*, Mém. SMF 124), II.4.10, Lemme 2 and
Remarques (2)–(3), printed pp. 93–94, for a cut-off supercuspidal coefficient. The twisted
characters are those of HL II.2.7–II.2.8, printed pp. 66–69, and the contragredient
intertwiner of HL II.2.9, Remarque (5), printed p. 70, explains why the value at `δ⁻¹` of the
twisted character of `A⁻¹` appears. Schur orthogonality is D. Renard, *Représentations des
groupes réductifs p-adiques* (2026 version), IV.3.3, Lemma and Remark, printed pp. 101–102, and
the compact support modulo the centre is Renard 2026, VI.2.1, Théorème, printed pp. 137–138.

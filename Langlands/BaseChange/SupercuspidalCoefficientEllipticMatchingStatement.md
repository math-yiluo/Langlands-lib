# Elliptic matching of supercuspidal matrix coefficients

The module `Langlands.BaseChange.SupercuspidalCoefficientEllipticMatchingStatement` states, as
the proposition `SupercuspidalCoefficientEllipticMatchingStatement.{u, v, uV, uW}`, that for a
cyclic field extension `E/F` of nonarchimedean local fields of characteristic zero with generator
`σ`, an irreducible supercuspidal representation `τ` of `GL_n(E)` with an isomorphism `A` of `τ`
onto `τ^σ`, and an irreducible supercuspidal representation `π` of `GL_n(F)` whose characters
satisfy `Θ_τ^{A⁻¹}(δ⁻¹) = c Θ_π(γ⁻¹)` with `c ≠ 0` at every associated pair `(δ, γ)` with `γ`
regular elliptic, there are cusp forms `φ` on `GL_n(E)` and `f` on `GL_n(F)` that concord at
every such pair, with `f` zero at the regular elliptic elements that are not norms and
`tr(τ(φ) ∘ A) ≠ 0`. The module states the proposition and does not prove it.

## Notation (Library and Mathlib)

- `IsCyclicAlgebra σ l`, `IsNormAssociated σ l δ γ` (`N(δ)` is conjugate in `GL_n(E)` to `γ`)
  and `IsNorm σ l γ` (`γ` is associated with some `δ`), module `Langlands.BaseChange.Norm`;
  `IsRegularElliptic γ` (separable irreducible characteristic polynomial), module
  `Langlands.JacquetLanglands.RegularElliptic`.
- `GeneralLinear.IsSupercuspidal`, `SigmaIntertwiner σ n τ` (`A τ(g) = τ(g^σ) A`), as in
  `Langlands.BaseChange.SigmaStableSupercuspidalDescentStatement`. `A.symm` is the inverse
  isomorphism (Mathlib's `Representation.Equiv.symm`), so `A.symm.toLinearMap` is `A⁻¹`.
- `HasCharacterValue π hπ g a` (module `Langlands.JacquetLanglands.LocalCharacter`): for every
  Haar measure `μ`, the character distribution `f ↦ tr π(f)` equals `a ∫ f dμ` on a
  neighbourhood of `g`. `HasTwistedCharacterValue τ hτ B g b` (module
  `Langlands.BaseChange.TwistedCharacter.Basic`): the same for the distribution
  `φ ↦ tr(τ(φ) ∘ B)` and the value `b`.
- `twistedDistribution μE τ hτ.1 A.toLinearMap φ = tr(τ(φ) ∘ A)`, with
  `τ(φ)w = ∫ φ(x) τ(x)w dμE(x)`.
- `HasVanishingConstantTerms` (module `Langlands.BaseChange.CuspForm`) and
  `ConcordAt σ l μF μE φ f δ γ` (module `Langlands.BaseChange.OrbitalIntegral`, HL I.2.5): for
  all associated right Haar measures `μδ` on the σ-centralizer `G^σ_δ(F)` and `μγ` on the
  centralizer `G_γ(F)` and all compatible quotient measures, the σ-orbital integral
  `∫ φ(x⁻¹ δ x^σ) dνδ(x)` equals the orbital integral `∫ f(x⁻¹ γ x) dνγ(x)`.

## Statement

`SupercuspidalCoefficientEllipticMatchingStatement.{u, v, uV, uW}` quantifies over a field
`F : Type u` with `[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
[CharZero F]`; a field `E : Type v` with `[Algebra F E] [TopologicalSpace E]
[IsTopologicalRing E] [IsModuleTopology F E]`; `σ : E ≃ₐ[F] E` and `l n : ℕ` with
`IsCyclicAlgebra σ l` and `0 < n`. The topological instances on `GL_n(F)` and `GL_n(E)` and the
Borel σ-algebras on both are introduced inside the statement.

The claim: let `τ : Representation ℂ (GeneralLinear n E) W` (`W : Type uW`) with
`hτ : GeneralLinear.IsSupercuspidal τ` be irreducible, `A : SigmaIntertwiner σ n τ`,
`π : Representation ℂ (GeneralLinear n F) V` (`V : Type uV`) with
`hπ : GeneralLinear.IsSupercuspidal π` irreducible, and `c : ℂ` with `c ≠ 0`. Assume that for
all `δ ∈ GL_n(E)` and `γ ∈ GL_n(F)` with `IsNormAssociated σ l δ γ` and `IsRegularElliptic γ`
there is `a : ℂ` with `HasCharacterValue π hπ.1 γ⁻¹ a` and
`HasTwistedCharacterValue τ hτ.1 A.symm.toLinearMap δ⁻¹ (c * a)`. Then for all Haar measures
`μF` on `GL_n(F)` and `μE` on `GL_n(E)` there are `φ : SchwartzBruhat (GeneralLinear n E)` and
`f : SchwartzBruhat (GeneralLinear n F)` with

1. `HasVanishingConstantTerms φ` and `HasVanishingConstantTerms f`;
2. `f γ = 0` for every regular elliptic `γ` with `¬ IsNorm σ l γ`;
3. `ConcordAt σ l μF μE φ f δ γ` whenever `IsNormAssociated σ l δ γ` and `IsRegularElliptic γ`;
4. `twistedDistribution μE τ hτ.1 A.toLinearMap φ ≠ 0`.

## Why the hypothesis is on `δ⁻¹` and `γ⁻¹`

The functions are cut-off matrix coefficients of the contragredients:
`φ(x) = b_E(x) λ(τ(x)⁻¹ v)` and `f(x) = b_F(x) λ'(π(x)⁻¹ w)` for vectors `v`, `w` and smooth
linear forms `λ`, `λ'`. Schur orthogonality pairs a coefficient of the contragredient of `τ`
with `τ`, which makes `tr(τ(φ) ∘ A)` nonzero; a coefficient of `τ` itself can give the trace
`0` (in rank one with `E = F`, `σ = id` and a character `χ` of order three, nontrivial on
`O_F^×`, the trace is `∫ b χ² = 0`). The σ-orbital integral of `φ` at `δ` is then proportional to
the value at `δ` of the twisted character of the contragredient of `τ` with the contragredient
intertwiner of HL II.2.9, Remarque (5); that value is the value at `δ⁻¹` of the distribution
`φ ↦ tr(τ(φ) ∘ A⁻¹)`. In the same way the orbital integral of `f` at `γ` is proportional to
`Θ_π(γ⁻¹)`, the value at `γ` of the character of the contragredient of `π`. On the ordinary
side this is the form of HL II.4.10, Lemme 2, the simple local trace formula for elliptic
functions on `GL_n(F)`, in which an elliptic orbital integral is paired with the characters
`Θ_π̌` of the contragredients. The twisted coefficient formula is the direct computation by Schur
orthogonality in step 3 of the proof sketch below; the twisted simple local trace formula of
HL II.4.10 (Proposition, printed pp. 94–95) is stated there under the hypothesis that a
concordant transfer exists, and is not used. Since `δ⁻¹` and `γ⁻¹` are associated for the generator `σ⁻¹` when `δ` and `γ`
are associated for `σ` (`N_{σ⁻¹}(δ⁻¹) = δ⁻¹ N_σ(δ)⁻¹ δ`), the hypothesis holds when `τ`, with
the σ⁻¹-intertwiner `A⁻¹`, is a σ⁻¹-lift of `π` (HL II.2.9 and its Remarques).

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour `GL_n` en
  caractéristique non nulle*, Mém. SMF 124 (2011), file
  `/home/taskhub/central-library/Henniart-Lemaire--Changement de base et induction automorphe pour GLn en caracteristique non nulle--2011.pdf`
  (PDF page = printed page + 8), cited as HL. I.2.5, printed pp. 17–18 (associated measures and
  concordance); I.2.7, remark, printed pp. 20–21 (local constancy of (σ-)orbital integrals on
  the regular sets, and conjugacy of `G^σ_δ(F)` and `G_γ(F)` in `G(E)` for associated `(δ, γ)`
  with `γ` regular); II.2.7–II.2.8, printed pp. 66–69 (twisted characters and their locally
  constant character functions on the σ-regular set); II.2.9, Remarques (3)–(5), printed p. 70
  (central characters, twists and contragredients of σ-lifts); II.4.10, Lemmes 1–2 and
  Remarques (2)–(3), printed pp. 93–94 (the simple local trace formula for elliptic functions
  on `GL_n(F)`; in Lemme 2 the elliptic orbital integrals are paired with the characters of the
  contragredients), and the Proposition of II.4.10, printed pp. 94–95 (its σ-twisted form, under
  the hypothesis that a concordant transfer exists); II.6.3–II.6.4, printed pp. 119–121 (matrix coefficients of cuspidal
  representations at an auxiliary place of the global comparison).
- Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*
  (1989), source ID `arthur-clozel-1989-base-change`, file
  `/home/taskhub/central-library/Arthur-Clozel--Simple algebras, base change, and the advanced theory of the trace formula (book)--1989.pdf`
  (PDF page = printed page + 14). Chapter 1, Lemma 1.4, printed pp. 8–9 (a regular elliptic
  element is a norm if and only if its determinant is a norm; in the Library
  `EllipticNormCriterionStatement`).
- Renard, *Représentations des groupes réductifs p-adiques* (2026 version), source ID
  `renard-2026-representations-groupes-reductifs-padiques`, file
  `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
  IV.3.3, Lemma and Remark, printed pp. 101–102 (Schur orthogonality and formal degree modulo a
  closed central subgroup with compact quotient of the centre); VI.2.1, Théorème, printed
  pp. 137–138 (coefficients of supercuspidal representations are compactly supported modulo the
  centre).

## Proof sketch

Let `Z = F^×`, embedded as scalar matrices; it is central in both groups, lies in every
centralizer and σ-centralizer, and has compact quotient in the centre of `GL_n(E)`. Fix a Haar
measure `μZ` on `Z`, let `q` be the order of the residue field of `F` and `|y|_E = |N_{E/F}y|_F`.

1. *Test functions.* Put `b_E(x) = 1{q^{-nl} < |det x|_E ≤ 1} / μZ(O_F^×)` and
   `b_F(x) = 1{q^{-nl} < |det x|_F ≤ 1} · 1{det x ∈ N_{E/F}E^×}`, and
   `φ = b_E · λ(τ(·)⁻¹ v)`, `f₁ = b_F · λ'(π(·)⁻¹ w)` with `λ(A v) ≠ 0` and `λ'(w) ≠ 0`. The
   coefficients are locally constant and compactly supported modulo the centre (Renard VI.2.1),
   and the cut-offs make `φ` and `f₁` compactly supported; `N_{E/F}E^×` is open, so they are
   Schwartz–Bruhat. The cut-offs are invariant under `x ↦ x u y ↦ x y` for `u` unipotent, and
   the vanishing of the Jacquet coinvariants makes `∫_U λ(τ(x u y)⁻¹ v) du = 0`; so both are cusp
   forms.
2. *Trace.* Exactly one `O_F^×`-coset of `Z` puts `z x` in the window of `b_E`, so
   `∫_Z b_E(z x) dμZ = 1`, and `λ(τ(z x)⁻¹ v) τ(z x) = λ(τ(x)⁻¹ v) τ(x)`. Schur orthogonality for
   `μE / μZ` with formal degree `d_E` gives `τ(φ) ∘ A = d_E⁻¹ (w ↦ λ(A w) v)`, whose trace is
   `d_E⁻¹ λ(A v) ≠ 0`.
3. *Elliptic orbital integrals.* For `δ` associated with a regular elliptic `γ`,
   `T_δ = G^σ_δ(F)` is conjugate in `GL_n(E)` to `G_γ(F) ≅ F[γ]^×` (HL I.2.7), so `T_δ / Z` is
   compact. The σ-elliptic elements form an open set (their norms have irreducible separable
   characteristic polynomials, an open condition). On the σ-centralizer `T_y` of each σ-elliptic
   `y` use the *normalized* Haar measure `μ^0_y`, for which `μ^0_y / μZ` gives `T_y / Z` volume
   `1`; then the quotient integral formula through `T_y / Z` gives
   `Λ^0_σ(φ, y) = ∫_{Z \ G(E)} φ(x⁻¹ y x^σ) d(μE / μZ)(x)`, a choice that depends on `y` only
   through `T_y` and is compatible in the sense of HL I.2.7. Fix a compact open neighbourhood
   `Ω` of `δ` of σ-elliptic elements on which `|det|_E` is constant. The set of `x ∈ Z \ G(E)`
   with `x⁻¹ Ω x^σ` meeting the support of `φ` is compact (compactness of σ-elliptic orbits
   modulo the centre, uniformly on compact sets), so `|φ(x⁻¹ y x^σ)|` is bounded and supported
   in a compact subset of `Ω × (Z \ G(E))`. Hence, for `h` locally constant with support in
   `Ω`, Fubini applies to `∫_Ω h(y) Λ^0_σ(φ, y) dμE(y)`. Using `b_E(x⁻¹ y x^σ) = b_E(δ)` and
   `τ(x^σ) = A τ(x) A⁻¹`, the inner integral is
   `b_E(δ) (λ ∘ A)(τ(x)⁻¹ A⁻¹ τ(ȟ) τ(x) v)` with `ȟ(y) = h(y⁻¹)` and `τ(ȟ) = ∫ ȟ(y) τ(y) dμE(y)`
   of finite rank (admissibility). Schur orthogonality for the finite-rank operator
   `A⁻¹ τ(ȟ)` gives
   `∫_Ω h Λ^0_σ(φ, ·) dμE = b_E(δ) λ(A v) d_E⁻¹ tr(τ(ȟ) ∘ A⁻¹)`, and
   `tr(τ(ȟ) ∘ A⁻¹) = Θ'(δ⁻¹) ∫ h dμE` when `Ω` lies in the inverse of the neighbourhood of `δ⁻¹`
   on which `φ ↦ tr(τ(φ) ∘ A⁻¹)` has the value `Θ'(δ⁻¹)` (the Haar measure of the unimodular
   group `GL_n(E)` is inversion invariant). Since `y ↦ Λ^0_σ(φ, y)` is locally constant on `Ω`
   (`φ` is invariant under an open subgroup, uniformly over the compact set of relevant `x`),
   `Λ^0_σ(φ, δ) = b_E(δ) λ(A v) Θ'(δ⁻¹) / d_E`. For an arbitrary right Haar measure `μδ` on
   `T_δ`, `μδ = s μ^0_δ` with `s = vol_{μδ/μZ}(T_δ / Z)`, and a quotient measure compatible with
   `μE` and `μδ` is `s⁻¹` times the one for `μ^0_δ` (the Library's `IsCompatible.smul_eq_smul`),
   so `Λ_σ(φ, δ) = b_E(δ) λ(A v) Θ'(δ⁻¹) / (d_E vol_{μδ/μZ}(T_δ / Z))`. In the same way, with
   `E = F`, `σ = id` and `A = 1`,
   `Λ(f₁, γ) = b_F(γ) λ'(w) Θ_π(γ⁻¹) / (d_F vol_{μγ/μZ}(G_γ(F) / Z))`.
4. *Matching.* For associated `(δ, γ)`, `det γ = N_{E/F}(det δ)`, so `b_F(γ) = b_E(δ)
   μZ(O_F^×)`; associated measures transport to the same measure and fix `Z`, so the two volumes
   agree. With the hypothesis `Θ'(δ⁻¹) = c Θ_π(γ⁻¹)`, `f = κ f₁` with
   `κ = c d_F λ(A v) / (d_E λ'(w) μZ(O_F^×))` concords with `φ` at every elliptic associated
   pair, for all associated measures and compatible quotient measures.
5. *Non-norms.* A regular elliptic `γ` that is not a norm has `det γ ∉ N_{E/F}E^×` (Arthur–Clozel
   Lemma 1.4), so `b_F(γ) = 0` and `f(γ) = 0`.

## Derived content

The statement is formulated for this Library; the sources do not state it in this form. It
isolates the elliptic part of the matching of cusp forms at an auxiliary place: Henniart–Lemaire
impose at one place a combination of elliptic support and cuspidal matrix coefficients
(II.6.3–II.6.4). On `GL_n(F)`, their Lemme 2 of II.4.10 expresses elliptic orbital integrals
of elliptic functions through the characters of contragredients; it motivates the ordinary
side, and the twisted side rests on the direct Schur orthogonality computation of step 3. The
hypothesis is phrased with the values at
`δ⁻¹` and `γ⁻¹` because those are the values that the orbital integrals of the coefficients of
the contragredients produce; the cut-off by a determinant window normalized over the scalars
`F^×` and the direct computation of the trace are this Library's construction.

# Matching cusp forms for a σ-stable supercuspidal representation

The module `Langlands.BaseChange.TwistedSupercuspidalCuspFormMatchingStatement` states, as the
proposition `TwistedSupercuspidalCuspFormMatchingStatement.{u, v, uW}`, that for a cyclic field
extension `E/F` of nonarchimedean local fields of characteristic zero, every σ-stable
irreducible supercuspidal representation `τ` of `GL_n(E)` has a pair of concordant cusp forms
`φ` on `GL_n(E)` and `f` on `GL_n(F)` (both with vanishing constant terms) such that the
twisted trace `tr(τ(φ) ∘ A)` is nonzero. The statement is **not** proved here.

## Notation (Library and Mathlib)

- `IsCyclicAlgebra σ l` (module `Langlands.BaseChange.Norm`); `E` is a field here.
- `GeneralLinear.IsSupercuspidal τ` (module
  `Langlands.Representation.Classification.Supercuspidal`): admissible (first component `hτ.1`)
  with vanishing Jacquet coinvariants along every proper block parabolic subgroup and its
  conjugates.
- `SigmaIntertwiner σ n τ` (module `Langlands.BaseChange.TwistedCharacter`): an isomorphism of
  `τ` onto `τ^σ`; `twistedDistribution μE τ hτ.1 A.toLinearMap φ = tr(τ(φ) ∘ A)` (module
  `Langlands.BaseChange.TwistedCharacter.Basic`).
- `HasVanishingConstantTerms f` (module `Langlands.BaseChange.CuspForm`): for every proper
  standard block parabolic subgroup with unipotent radical `U`, every Haar measure on `U` and
  all `x, y`, the function `u ↦ f(x u y)` is integrable on `U` with integral `0`.
- `AreConcordant σ l μF μE φ f` (module `Langlands.BaseChange.OrbitalIntegral`, HL I.2.5,
  printed p. 17): the orbital integrals of `f` vanish at every regular semisimple non-norm, and
  for every `δ ∈ GL_n(E)` associated with a regular semisimple `γ ∈ GL_n(F)` the σ-orbital
  integral of `φ` at `δ` equals the orbital integral of `f` at `γ`, for associated centralizer
  measures and compatible quotient measures.

## Statement

`TwistedSupercuspidalCuspFormMatchingStatement.{u, v, uW}` quantifies over a field `F : Type u`
with `[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]`; a
field `E : Type v` with `[Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
[IsModuleTopology F E]`; `σ : E ≃ₐ[F] E`, `l n : ℕ` with `hE : IsCyclicAlgebra σ l` and
`0 < n`. The topological instances on `GL_n(F)` (`LocalFieldTopology.generalLinear_*`) and on
`GL_n(E)` (`generalLinear_*_of_finite`) and the Borel σ-algebras on both are introduced inside
the statement.

The claim: for every complex vector space `W : Type uW`, every
`τ : Representation ℂ (GeneralLinear n E) W` with `hτ : GeneralLinear.IsSupercuspidal τ` and
`τ.IsIrreducible`, every `A : SigmaIntertwiner σ n τ` and all Haar measures `μF` on `GL_n(F)`
and `μE` on `GL_n(E)`, there are `φ : SchwartzBruhat (GeneralLinear n E)` and
`f : SchwartzBruhat (GeneralLinear n F)` with

1. `HasVanishingConstantTerms φ` and `HasVanishingConstantTerms f`;
2. `AreConcordant σ l μF μE φ f`;
3. `twistedDistribution μE τ hτ.1 A.toLinearMap φ ≠ 0`.

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour `GL_n` en
  caractéristique non nulle*, Mém. SMF 124 (2011), file
  `/home/taskhub/central-library/Henniart-Lemaire--Changement de base et induction automorphe pour GLn en caracteristique non nulle--2011.pdf`
  (PDF page = printed page + 8), cited as HL. I.2.5, printed pp. 17–18 (associated measures
  and concordance); I.2.7, remark, printed pp. 20–21 (σ-orbital and orbital integrals of
  `C_c^∞` functions are locally constant on the regular sets for compatibly chosen centralizer
  measures, and `G^σ_δ(F)` and `G_γ(F)` are conjugate in `G(E)` for associated `(δ, γ)` with
  `γ` regular); II.2.7–II.2.8, printed pp. 66–69 (twisted character distributions and their
  locally constant character functions on the σ-regular set); II.2.9, Proposition and
  Remark (3), printed pp. 69–70 (a σ-lift is
  characterized by `Θ^A_Π(δ) = c Θ_π(γ)` with `c ≠ 0` for every associated pair `(δ, γ)` with
  `γ` regular, and `ω_Π = ω_π ∘ N_{E/F}`); II.4.5, formula (1), printed p. 86 (descent
  formula `Λ_σ(φ, δ) = |D_{G/M,σ}(δ)|_F^{-1/2} Λ^{M(E)}_σ(φ_{P,σ}, δ)` for `δ ∈ M(E)` with
  `G^σ_δ ⊂ M`, where
  `φ_{P,σ}(m) = δ_P(m)^{1/2} ∫_{U(E) × K_E} φ(k⁻¹ m u k^σ) du dk`; `σ = id` gives the
  ordinary case); II.4.6(2), printed p. 88 (a σ-stable discrete series is the σ-lift of a
  discrete series); II.4.12, Remarque, printed p. 97 (last sentence: the descent `π` is
  cuspidal if and only if `Π` is isomorphic to a parabolic induction of a cuspidal
  representation of a Levi subgroup, for example `Π` itself when `Π` is cuspidal); II.4.10,
  Lemme 2, printed pp. 93–94 (the elliptic orbital integral of a coefficient is paired with
  the contragredient character, consistent with the conjugate coefficients below); II.6.3–II.6.4, printed pp. 119–121, and
  II.6.6, printed pp. 122–123 (global context: conditions `c_{v₁}(f)`, `c^σ_{v₁}(φ)` and the
  comparison for concordant functions).
- Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*
  (1989), source ID `arthur-clozel-1989-base-change`, file
  `/home/taskhub/central-library/Arthur-Clozel--Simple algebras, base change, and the advanced theory of the trace formula (book)--1989.pdf`
  (PDF page = printed page + 14). Chapter 1, Lemma 1.4, printed pp. 8–9 (norm criterion for
  elliptic elements); Lemma 2.12, printed p. 19 (context only: Arthur–Clozel use twisted
  pseudo-coefficients at the auxiliary place; the construction below does not use this lemma).
- Renard, *Représentations des groupes réductifs p-adiques* (2026 version), source ID
  `renard-2026-representations-groupes-reductifs-padiques`, file
  `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
  IV.3.3, Lemma and Remark, printed pp. 101–102 (Schur orthogonality relations and formal
  degree for a square-integrable representation modulo a closed central subgroup with compact
  quotient of the centre); VI.2.1, Théorème, printed pp. 137–138 (supercuspidal if and only if
  the matrix coefficients are compactly supported modulo the centre).

## Why it is true (sketch for the reviewer)

Conventions fixed by the Library. A σ-intertwiner satisfies `A τ(g) = τ(g^σ) A`
(`SigmaIntertwiner.comp_apply_eq`). The integrated action is `τ(φ)a = ∫ φ(x) τ(x)a dμE(x)` and
`twistedDistribution μE τ hτ.1 A φ` is the trace of the finite-rank operator `τ(φ) ∘ A`. The
σ-orbital integral is `∫ φ(x⁻¹ δ x^σ) dνδ(x)` over `G^σ_δ \ GL_n(E)`, and the ordinary orbital
integral is the case `σ = id`. Let `Z = F^×`, embedded as scalar matrices in both `GL_n(F)` and
`GL_n(E)`. It is central in both groups, lies in every centralizer `G_γ(F)` and every
σ-centralizer `G^σ_δ(F)`, and has compact quotient `E^×/F^×` in the centre of `GL_n(E)`. Fix
one Haar measure `μZ` on `Z`. Let `q` be the order of the residue field of `F`, `|·|_F`
normalized, and `|y|_E = |N_{E/F} y|_F`, so `|z|_E = |z|_F^l` for `z ∈ F^×`.

0. **Unitary normalization.** Choose `s ∈ ℂ` so that `τ₁ = τ ⊗ |det|_E^{-s}` has unitary
   central character. Its coefficients are compactly supported modulo the centre (Renard
   VI.2.1). Fix a nonzero smooth linear form `λ` on `τ₁`. Then
   `⟨a, b⟩ = ∫ λ(τ₁(g)a) conj λ(τ₁(g)b) dg`, taken over the centre quotient, converges and is
   a `GL_n(E)`-invariant inner product. It is positive definite by irreducibility. Since
   `|det x^σ|_E = |det x|_E`, `A` is also a σ-intertwiner for `τ₁`. The form
   `(a, b) ↦ ⟨Aa, Ab⟩` is again invariant, so by Schur's lemma it equals `r⟨a, b⟩` with `r > 0`.
   Put `A₁ = r^{-1/2} A`, which is unitary.
1. **Descent.** `τ₁` is a σ-stable unitary supercuspidal, hence σ-discrete, representation. By
   HL II.4.6(2) it is the σ-lift of a discrete series `π₁` of `GL_n(F)`, and `π₁` is
   supercuspidal by the last sentence of the Remarque in HL II.4.12, applied with the Levi
   subgroup `GL_n(E)` itself. By HL II.2.9 there is `c ≠ 0` with
   `Θ^{A₁}_{τ₁}(δ) = c Θ_{π₁}(γ)` for every associated pair `(δ, γ)` with `γ` regular. By
   Remark (3) there, `ω_{τ₁} = ω_{π₁} ∘ N_{E/F}`. So `|ω_{π₁}|` is a positive character trivial
   on the finite-index subgroup `N_{E/F}E^×`; it is therefore trivial and `π₁` is unitary too.
   (The Library statements `SigmaDiscreteDescentStatement` and
   `CuspidalSigmaLiftExistenceStatement` record descents of this kind.)
2. **Test functions.** Take unit vectors `v` in `τ₁` and `w` in `π₁`. Use the **conjugate**
   (contragredient) coefficients
   `C_E(x) = conj ⟨τ₁(x) A₁ v, v⟩` and `C_F(x) = conj ⟨π₁(x) w, w⟩`,
   and the cutoffs
   `b_E(x) = 1{q^{-nl} < |det x|_E ≤ 1} / μZ(O_F^×)` and
   `b_F(x) = 1{q^{-nl} < |det x|_F ≤ 1} · 1{det x ∈ N_{E/F}E^×} / μZ(O_F^×)`.
   Put `φ₁ = b_E C_E` and `f₁ = b_F C_F`. The forward coefficient `⟨τ₁(x)A₁v, v⟩` does not
   work. In rank one with `E = F`, `σ = id`, and `τ₁ = χ` a character of order three that is
   nontrivial on `O_F^×`, it gives the trace `∫ b χ²`, which vanishes. The conjugate
   coefficient gives `∫ b χ⁻¹ χ = 1`.
   - *Schwartz–Bruhat.* The coefficients are locally constant and supported in `K Z` for a
     compact set `K` (Renard VI.2.1). Writing `x = kz` with `k ∈ K`, the cutoff bounds
     `v_F(z)` to finitely many values, so `φ₁` and `f₁` have compact support. They are locally
     constant because `|det|` is locally constant and `N_{E/F}E^×` is open (it contains
     `(F^×)^l`, open since `F` has characteristic zero).
   - *Vanishing constant terms.* For a proper standard block parabolic subgroup with radical
     `U`, `b(x u y) = b(x y)`. Also
     `∫_U C_E(x u y) du = conj ∫_U ⟨τ₁(u) τ₁(y) A₁ v, τ₁(x)⁻¹ v⟩ du`. The integrand is compactly
     supported on `U`, because `U ∩ Z = 1`, `UZ` is closed, and the coefficient has compact
     support modulo `Z`. Hence it is integrable for every Haar measure on `U`. Since the Jacquet
     coinvariants of `τ₁` vanish, every vector is a finite sum of vectors `τ₁(u_j)a_j − a_j`,
     and the integral vanishes by invariance of the Haar measure on `U`. The same argument
     works for `π₁` and `f₁`.
3. **The trace.** For every `x`, `|det(zx)|_E = |z|_F^{nl} |det x|_E` for `z ∈ Z`. Exactly one
   `O_F^×`-coset of `Z` puts `zx` in the window, so `∫_Z b_E(zx) dμZ(z) = 1`. Also
   `C_E(zx) τ₁(zx) = C_E(x) τ₁(x)` because `|ω_{τ₁}| = 1`. By the Weil formula for
   `μE / μZ`, `τ₁(φ₁) = ∫_{Z\GL_n(E)} C_E(x) τ₁(x) dx` weakly. Let `d_E > 0` be the formal
   degree of `τ₁` for `μE / μZ` (Renard IV.3.3 and its Remark, applicable because `E^×/F^×`
   is compact). Schur orthogonality gives
   `⟨τ₁(φ₁) A₁ a, b⟩ = d_E⁻¹ ⟨A₁ a, A₁ v⟩ ⟨v, b⟩ = d_E⁻¹ ⟨a, v⟩ ⟨v, b⟩`.
   So `τ₁(φ₁) ∘ A₁` is the rank-one operator `a ↦ d_E⁻¹ ⟨a, v⟩ v`, and its trace is
   `d_E⁻¹ ≠ 0`. No Weyl integration formula and no nonvanishing result for `Θ^{A₁}_{τ₁}` is
   needed for this step.
4. **Elliptic orbital integrals.** Let `γ` be regular elliptic and `δ` σ-regular with
   `N δ` conjugate to `γ`. Conjugation by an element `x ∈ GL_n(E)` with `x⁻¹ N(δ) x = γ`, the
   map used in `IsAssociatedMeasure`, carries `G^σ_δ(F)` onto `G_γ(F) ≅ F[γ]^×` (HL I.2.7,
   remark) and fixes `Z` pointwise. So `T = G^σ_δ(F)` has `T/Z` compact. Using
   `A₁ τ₁(x) = τ₁(x^σ) A₁` and unitarity,
   `C_E(x⁻¹ δ x^σ) = conj ⟨τ₁(δ) A₁ τ₁(x) v, τ₁(x) v⟩`, which is left `T`-invariant in `x`.
   The cutoff `b_E` is constant on σ-conjugacy classes. Put
   `I(y) = ∫_{Z\GL_n(E)} ⟨τ₁(y) A₁ τ₁(x) v, τ₁(x) v⟩ dx` for `y` σ-regular σ-elliptic with
   `b_E(y) ≠ 0`. Take `h` smooth and compactly supported on that open set. By Fubini,
   `∫ h(y) I(y) dy = ∫_{Z\G} ⟨τ₁(h) A₁ τ₁(x) v, τ₁(x) v⟩ dx`. Fubini applies because
   `|φ₁|` is again in `C_c^∞`, so its σ-orbital integrals are locally constant, hence locally
   bounded, on the σ-regular set (HL I.2.7, remark), and `vol(T_y/Z)` is locally constant
   there for compatibly chosen measures. For the finite-rank operator `K = τ₁(h) A₁`, Schur
   orthogonality gives `∫_{Z\G} ⟨K τ₁(x) v, τ₁(x) v⟩ dx = d_E⁻¹ tr K = d_E⁻¹ ∫ h Θ^{A₁}_{τ₁}`.
   Here `Θ^{A₁}_{τ₁}` is the twisted character function, which is locally constant on the
   σ-regular set (HL II.2.7–II.2.8, printed pp. 66–69). `I` is locally constant on this set as
   well, so `I = d_E⁻¹ Θ^{A₁}_{τ₁}` pointwise. Applying the Weil formula to `Z ⊂ T`, for every Haar measure `μδ` on `T` and
   every quotient measure `νδ` compatible with `μE / μδ`:
   `Λ_σ(φ₁, δ) = b_E(δ) conj Θ^{A₁}_{τ₁}(δ) / (d_E · vol_{μδ/μZ}(T/Z))`.
   The same argument with `σ = id`, applied to `π₁` with formal degree `d_F` for `μF / μZ`,
   gives
   `Λ(f₁, γ) = b_F(γ) conj Θ_{π₁}(γ) / (d_F · vol_{μγ/μZ}(G_γ(F)/Z))`.
5. **Matching.** Let `(δ, γ)` be associated with `γ` regular elliptic. Then
   `det γ = N_{E/F}(det δ) ∈ N_{E/F}E^×` and `|det γ|_F = |det δ|_E`, so `b_F(γ) = b_E(δ)`.
   Also `Θ^{A₁}_{τ₁}(δ) = c Θ_{π₁}(γ)`. For associated `μδ, μγ` the transported measures agree
   and `Z` is fixed, so the two volumes of `T/Z` agree. Hence `Λ_σ(φ₁, δ) = κ Λ(f₁, γ)` with
   `κ = conj(c) d_F / d_E`. Put `f₂ = κ f₁`.
   - At non-elliptic regular `γ`, and at any `δ` associated with it, both orbital integrals
     vanish. Conjugate `γ` into a proper standard block Levi subgroup `M(F)`. Replace `δ` by a
     σ-conjugate `δ'` with `N(δ') = γ`, which leaves the σ-orbital integral unchanged (HL
     I.2.5). Then `δ' γ = δ' N(δ')^σ = N(δ') δ' = γ δ'`, so `δ'` lies in the torus
     `G_γ(E) ⊂ M(E)`, and so does `G^σ_{δ'}(F)`. By the descent formula HL II.4.5(1) (with
     `σ = id` for `f₂`), each orbital integral is a nonzero multiple of an orbital integral on
     `M` of `φ_{P,σ}` resp. `f_P`. These functions are zero because
     `∫_U φ(x u y) du = 0` for all `x, y` (step 2).
   - At a regular elliptic non-norm `γ`, `det γ ∉ N_{E/F}E^×` by the norm criterion
     (`EllipticNormCriterionStatement`, Arthur–Clozel Lemma 1.4). So `f₂` vanishes on the
     conjugacy class of `γ`, and its orbital integral is zero.
   So `AreConcordant σ l μF μE φ₁ f₂` holds for all associated centralizer measures and
   compatible quotient measures, as the Lean predicate requires.
6. **Back to `τ` and `A`.** Put `φ = |det|_E^{-s} φ₁` and `f = |det|_F^{-s} f₂`. Then
   `τ(φ) = τ₁(φ₁)` and `A = r^{1/2} A₁`, so `tr(τ(φ) ∘ A) = r^{1/2} / d_E ≠ 0`. The factor
   `|det|^{-s}` is constant on (σ-)conjugacy classes and along `x U y`. Since
   `|det γ|_F = |det δ|_E` for associated pairs, it preserves compact support, local
   constancy, the vanishing constant terms and concordance. This holds for the given, arbitrary
   Haar measures `μF` and `μE`.

## Derived content

The statement is formulated for this project; the sources do not state it in this form.
Henniart–Lemaire impose at one place `v₁` the combined condition (elliptic support and
combination of cuspidal coefficients). The Library's simple trace formulas
(`Langlands.TraceFormula.GeneralLinearSimpleTraceFormulaStatement`,
`GeneralLinearSimpleTwistedTraceFormulaStatement`) and their comparison
(`GeneralLinearBaseChangeTraceComparisonStatement`) separate the two conditions: a factor whose
integrals along the adelic unipotent radicals vanish (a cusp form at one place) and elliptic
support at another place. The present statement supplies the cusp-form place: a matched pair
`(φ, f)` of cusp forms with nonzero twisted trace for the given `τ`. It is made for a field `E`
only (a place of the base field with exactly one place above it), and for one pair of Haar
measures at a time, any pair. The construction in the sketch (conjugate coefficients,
determinant cutoff normalized over the scalars `F^×`, direct Schur computation of the trace)
is the project's; the cited sources supply the descent, the character identity, the
orbital-integral descent and the norm criterion.

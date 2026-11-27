# σ-discrete series are detected by test functions with σ-elliptic orbital integrals

Module `Langlands.BaseChange.SigmaDiscreteEllipticOrbitalTestStatement`, declaration
`Langlands.BaseChange.SigmaDiscreteEllipticOrbitalTestStatement` (level parameters `u v uW`).
This is a statement only. Nothing in the module is proved.

## Statement

Let `F` be a nonarchimedean local field of characteristic zero. Let `E` be a field that is a
cyclic `F`-algebra of degree `l` with generator `σ`, with its module topology over `F`. Let
`r : ℕ` and `n = r + 1`. Give `GL_n(E)` its Borel σ-algebra. Let `τ` be an admissible
representation of `GL_n(E)` on a complex vector space `W : Type uW` that is a σ-discrete
series representation, let `A` be an isomorphism of `τ` onto `τ^σ`, and let `μ` be a Haar
measure on `GL_n(E)`. Then some Schwartz–Bruhat function `φ` on `GL_n(E)` satisfies

- the σ-orbital integrals of `φ` vanish at every σ-regular element `δ` of `GL_n(E)` that is not
  σ-elliptic, for every right Haar measure on the σ-centralizer of `δ` and every quotient measure
  compatible with it and with `μ` (`SigmaOrbitalIntegralsVanishOffElliptic σ l μ ⇑φ`); and
- `tr(τ(φ) ∘ A) ≠ 0` (`twistedDistribution μ τ hτ A.toLinearMap φ ≠ 0`).

The Lean binders are those of the Library's `SigmaDiscreteEllipticNonvanishingStatement`
(module `Langlands.BaseChange.SigmaDiscreteEllipticNonvanishingStatement`), in the same order:
`F : Type u` with `[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F] [CharZero F]`; `E : Type v` with `[Field E] [Algebra F E]
[TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]`; `σ : E ≃ₐ[F] E`; `l r : ℕ`;
`hE : IsCyclicAlgebra σ l`; then, by `haveI`/`letI`, `Module.Finite F E` from `hE.1`, the
Hausdorff, locally compact and totally disconnected structures on `GeneralLinear (r + 1) E`
(`generalLinear_t2Space_of_finite`, `generalLinear_locallyCompactSpace_of_finite`,
`generalLinear_totallyDisconnectedSpace_of_finite`), the Borel σ-algebra and its `BorelSpace`
instance; then `W : Type uW` with `[AddCommGroup W] [Module ℂ W]`,
`τ : Representation ℂ (GeneralLinear (r + 1) E) W` and `hτ : IsAdmissible τ`. The proposition is

`IsSigmaDiscreteSeries σ (r + 1) τ → ∀ (A : SigmaIntertwiner σ (r + 1) τ)
(μ : Measure (GeneralLinear (r + 1) E)) [μ.IsHaarMeasure],
∃ φ : SchwartzBruhat (GeneralLinear (r + 1) E),
SigmaOrbitalIntegralsVanishOffElliptic σ l μ ⇑φ ∧ twistedDistribution μ τ hτ A.toLinearMap φ ≠ 0`.

## Library notation

- `IsSigmaDiscreteSeries σ n τ` (module `Langlands.BaseChange.PseudoCoefficient`): `τ` is
  admissible, irreducible, tempered and σ-stable, and not isomorphic to the smooth induction,
  from the standard upper block parabolic subgroup of any block shape with at least two blocks,
  of a smooth σ-stable representation of the Levi product (Arthur–Clozel, Chapter 1, §2.3;
  Henniart–Lemaire, II.4.6).
- `SigmaIntertwiner σ n τ` and `twistedDistribution` (modules `Langlands.BaseChange.TwistedCharacter`
  and `Langlands.BaseChange.TwistedCharacter.Basic`): an isomorphism `A` of `τ` onto
  `τ^σ = τ ∘ entrywiseAut σ n`, and the twisted distribution character `φ ↦ tr(τ(φ) ∘ A)` with
  `τ(φ) = ∫ φ(g) τ(g) dμ(g)`.
- `SigmaOrbitalIntegralsVanishOffElliptic σ l μ φ` (module
  `Langlands.BaseChange.EllipticOrbitalIntegral`): for every `δ` with `IsSigmaRegular σ l δ` and
  not `IsSigmaElliptic σ l δ`, every right Haar measure `μδ` on the σ-centralizer
  `{x | x⁻¹ δ x^σ = δ}` and every measure `νδ` on its coset space compatible with `μ` and `μδ`,
  the σ-orbital integral `∫ φ(x⁻¹ δ x^σ) dνδ(x)` is `0`.
- `SchwartzBruhat (GeneralLinear n E)`: locally constant compactly supported complex functions.

## Design

- **Weakest form used.** The statement asks for one function with the two properties used in the
  proof of Arthur–Clozel, Chapter 1, Lemma 2.12 (i): vanishing σ-orbital integrals off the
  σ-elliptic set and nonzero twisted trace. It asks neither for the value `1` nor for vanishing
  on other representations. The Library's `TwistedCuspidalPseudoCoefficientExistenceStatement`
  (module `Langlands.BaseChange.TwistedCuspidalPseudoCoefficientExistenceStatement`) asks for
  more: a twisted pseudo-coefficient (twisted trace `1` on `(τ, A)`, `0` on the other tempered
  irreducible representations with the same central character), vanishing on properly induced
  representations, the same orbital vanishing, and nonvanishing σ-orbital integrals on an open
  set of σ-elliptic elements. Its parts (a) and (c) give the present statement; the module
  `Langlands.BaseChange.SigmaDiscreteEllipticNonvanishingReduction` proves this implication
  (`TwistedCuspidalPseudoCoefficientExistenceStatement.sigmaDiscreteEllipticOrbitalTest`).
- **No central character in the hypotheses.** A σ-discrete series is tempered, hence has a
  central character, so none is supplied.
- **Same setting as the nonvanishing statement.** `n = r + 1`, a field `E`, every `A` and every
  Haar measure `μ`, as in `SigmaDiscreteEllipticNonvanishingStatement`, of which this statement
  is the main input.
- **Compactly supported test functions.** Henniart–Lemaire and Arthur–Clozel construct
  pseudo-coefficients compactly supported modulo the centre, with a central character. Multiplying
  such a function by the indicator of the set where the normalized valuation of the determinant
  lies in `{0, …, n − 1}` gives a compactly supported function. That valuation is constant on
  σ-conjugacy classes (the valuation of `E` is `σ`-invariant), so each σ-orbital integral of the
  product is a constant multiple of the corresponding one of the original function. For a
  representation with that central character, the twisted trace is multiplied by a positive
  constant: summing the indicator over the central translates `ϖ_E^k`, `k ∈ ℤ`, gives `1`.
  So the compact-support form follows from the sources.

## Provenance

This is a derived statement. A twisted pseudo-coefficient of a σ-discrete series exists
(Henniart–Lemaire 2011, II.5.13, Proposition, printed p. 113, construction p. 114;
Arthur–Clozel 1989, Chapter 1, Corollary 2.10, printed p. 18). Its twisted trace on `(τ, A)` is
`1`, and its σ-orbital integrals vanish at the σ-regular elements that are not σ-elliptic
(Henniart–Lemaire 2011, II.5.14, Proposition 2 (2), printed p. 115, proof pp. 116–117;
Arthur–Clozel 1989, Chapter 1, Lemma 2.12 (ii), printed p. 19). The passage to compactly
supported functions is explained under Design.

## Sources

- G. Henniart, B. Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011): II.5.13 (printed pp. 113–114), II.5.14,
  Propositions 1 and 2 and Corollaire 1 (printed pp. 114–117).
- J. Arthur, L. Clozel, *Simple algebras, base change, and the advanced theory of the trace
  formula*, Ann. of Math. Stud. 120 (1989): Chapter 1, Corollary 2.10 (printed p. 18) and
  Lemma 2.12 (printed p. 19).

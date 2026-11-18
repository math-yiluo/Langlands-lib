# Orbital and σ-orbital integrals on `GL_n`, associated measures and concordance

Module `Langlands.BaseChange.OrbitalIntegral`, namespace `Langlands.BaseChange`.
Write `GL_n(R)` for the Library's `GeneralLinear n R`.

## Source

Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle*, Mém. SMF 124 (2011), source ID
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`
(PDF page = printed page + 8):

- I.2.2, printed p. 11: the σ-centralizer `G^σ_δ(F)`;
- printed p. 14, the paragraph that ends I.2.3, just before the heading I.2.4:
  centralizers of associated elements when `γ` is regular;
- I.2.4, printed pp. 14–16: the centralizer `G_γ(F)`, the orbital integral
  `Λ^{G(F)}(f, γ)`, the σ-orbital integral `Λ^{G(E)}_σ(φ, δ)` and their quotient measures;
- I.2.5, printed p. 17: the associated measure ("mesure associée"), the normalization
  `d̄g^σ_δ = dg_E/dg^σ_δ`, `d̄g_γ = dg/dg_γ`, and the Définition of concordance;
  printed p. 18: support in `G(F)_r` and in `G(E)_{σ-r}`.

Arthur–Clozel (1989), Chapter 1, §§1–3, treat the same notions for a cyclic field
extension in characteristic zero; the formalization follows HL.

## Setting

`F` is a field and `E` a commutative `F`-algebra, both topological rings, `σ : E ≃ₐ[F] E`,
and `l n : ℕ`. HL's σ-conjugation `g⁻¹ δ g^σ` is `twistedConj (entrywiseAut σ n) g δ`
(Task 7402's module `Langlands.TraceFormula.TwistedOrbital`, with `entrywiseAut` from
Task 7405's module `Langlands.BaseChange.Norm`). HL's quotients `G_γ(F)\G(F)` are the
Library's `QuotientIntegration.LeftQuotient`, whose points are the cosets `H g`.

**Measurable structures.** `GL_n(F)` and `GL_n(E)` carry a supplied σ-algebra with
`[BorelSpace _]` for Mathlib's topology on the units of the matrix ring. A subgroup
carries Mathlib's subtype σ-algebra, which is the Borel σ-algebra of the subspace
topology. For the left coset space, the module defines the reducible definition
`leftQuotientMeasurableSpace H := borel (LeftQuotient H)` and proves
`leftQuotient_borelSpace H`. It installs them with `attribute [local instance high]` and
`attribute [local instance]`; the two statement modules repeat these two lines. The high
priority is needed: a supplied `[MeasurableSpace G]` would otherwise also make Mathlib's
quotient σ-algebra `Quotient.instMeasurableSpace` available, and a check with
`with_reducible rfl` confirmed that the instance found on `LeftQuotient (glCentralizer γ)`
is the Borel one. The instances are local, so importing the module changes no instance
elsewhere. This is the arrangement the task prescribed, as a named local instance.

## Definitions (items 1–6)

1. **Centralizers.** `sigmaCentralizer σ n δ` is the reducible abbreviation of
   `twistedCentralizer (entrywiseAut σ n) δ`, the subgroup
   `{x ∈ GL_n(E) | x⁻¹ δ x^σ = δ}`: HL's σ-centralizer `G^σ_δ(F)` (I.2.2, p. 11).
   `glCentralizer γ`, for `γ : GL_n(F)`, is the reducible abbreviation of
   `twistedCentralizer (MonoidHom.id _) γ`: HL's `G_γ(F)` (I.2.4, p. 14). It is
   expressed through `twistedCentralizer` so that `LeftQuotient (glCentralizer γ)` is
   exactly the domain of the quotient measure in Task 7402's `orbitalIntegral γ ν f`.
2. **σ-orbital integral.** `sigmaOrbitalIntegral σ n δ ν φ` is the reducible abbreviation
   of `twistedOrbitalIntegral (entrywiseAut σ n) δ ν φ`, for a measure `ν` on
   `LeftQuotient (sigmaCentralizer σ n δ)` and `φ : GL_n(E) → ℂ`. It is
   `∫ φ(x⁻¹ δ x^σ) dν(x)` over `G^σ_δ(F)\G(E)`, HL's `Λ^{G(E)}_σ(φ, δ)` (I.2.4,
   pp. 15–16). The ordinary orbital integral `Λ^{G(F)}(f, γ)` is Task 7402's
   `orbitalIntegral γ ν f`; no second one is defined. Both are Mathlib Bochner
   integrals, which are `0` for non-integrable integrands; no convergence is asserted.
3. **Associated measure.** `IsAssociatedMeasure σ l δ γ μδ μγ`, for measures `μδ` on
   `sigmaCentralizer σ n δ` and `μγ` on `glCentralizer γ`, says: there is `x : GL_n(E)` with
   `x⁻¹ * cyclicNorm σ l δ * x = baseChange F E n γ` such that the image of `μδ` under
   `c ↦ x⁻¹ c x` and the image of `μγ` under `t ↦ baseChange F E n t` are the same measure
   on `GL_n(E)` (both `Measure.map`). This is HL's "mesure associée" (I.2.5, p. 17) for
   regular `γ`; see below. `Measure.map` along a map that is not almost-everywhere
   measurable is `0`. The conjugation is continuous; `baseChange` is continuous when
   `algebraMap F E` is, which is the case under the `[IsModuleTopology F E]` hypothesis
   of the two statements. These continuity facts are not proved here.
4. **Concordance at a pair.** `ConcordAt σ l μF μE φ f δ γ`, for measures `μF` on
   `GL_n(F)` and `μE` on `GL_n(E)` (explicit arguments), `φ : GL_n(E) → ℂ`,
   `f : GL_n(F) → ℂ`: for all right Haar measures `μδ` on `sigmaCentralizer σ n δ` and
   `μγ` on `glCentralizer γ` (instance binders `IsHaarMeasure` and
   `IsMulRightInvariant`), all `νδ` with
   `QuotientIntegration.IsCompatible (sigmaCentralizer σ n δ) μE μδ νδ`, and all `νγ`
   with `IsCompatible (glCentralizer γ) μF μγ νγ`, if
   `IsAssociatedMeasure σ l δ γ μδ μγ` then
   `sigmaOrbitalIntegral σ n δ νδ φ = orbitalIntegral γ νγ f`. This is HL's "φ et f
   concordent en (δ, γ)" (I.2.5, Définition, p. 17). HL's normalization
   `d̄g^σ_δ = dg_E/dg^σ_δ`, `d̄g_γ = dg/dg_γ` is expressed by `IsCompatible`: the
   quotient measure is nonzero, regular, right invariant, and satisfies Weil's formula
   with the subgroup and ambient measures. The definition accepts arbitrary measures
   `μF`, `μE`; the statements take them Haar.
5. **Concordance.** `VanishesOffNorms σ l μF f`: for every `γ` with
   `IsRegularSemisimple γ` and `¬ IsNorm σ l γ`, every right Haar measure `μγ` on
   `glCentralizer γ` and every `νγ` with `IsCompatible (glCentralizer γ) μF μγ νγ`,
   `orbitalIntegral γ νγ f = 0`. `AreConcordant σ l μF μE φ f` is the conjunction of
   `VanishesOffNorms σ l μF f` and `ConcordAt σ l μF μE φ f δ γ` for all `δ`, `γ` with
   `IsNormAssociated σ l δ γ` and `IsRegularSemisimple γ`. This is HL's "φ et f
   concordent" (I.2.5, Définition, p. 17).
6. **Regular support.** `IsRegularSupported f`: every `g` with `f g ≠ 0` satisfies
   `IsRegularSemisimple g`. `IsSigmaRegularSupported σ l φ`: every `δ` with `φ δ ≠ 0`
   satisfies `IsSigmaRegular σ l δ`. These are HL's "à support dans `G(F)_r`" and "à
   support dans `G(E)_{σ-r}`" (I.2.5, p. 18).

## Lemmas with proofs (items 7–9)

7. `mem_sigmaCentralizer`: `x ∈ sigmaCentralizer σ n δ ↔ x⁻¹ * δ * entrywiseAut σ n x = δ`.
   Proof: `Iff.rfl`, by the definition of `twistedCentralizer`.
8. `glCentralizer_eq_centralizer`: `glCentralizer γ = Subgroup.centralizer {γ}`.
   Proof: Task 7402's `twistedCentralizer_id`.
9. `conj_mem_sigmaCentralizer`: if `c ∈ sigmaCentralizer σ n δ`, then
   `x⁻¹ * c * x ∈ sigmaCentralizer σ n (x⁻¹ * δ * entrywiseAut σ n x)` for every `x`.
   Proof: `entrywiseAut σ n` is multiplicative, so the stabilizer equation for
   `x⁻¹ c x` at `x⁻¹ δ x^σ` simplifies (`simp` with `map_mul`, `map_inv`, group
   cancellation) to `x⁻¹ (c⁻¹ δ c^σ) x^σ`, which is `x⁻¹ δ x^σ` by the hypothesis.

## Mathematical explanations (not formalized)

**Why item 3 is HL's associated measure.** Let `σ ^ l = 1`, `IsCyclicAlgebra σ l` (so
the `σ`-fixed elements of `E` are those of `F`), and `γ` regular semisimple associated
with `δ`, with `x` as in item 3. Put `δ' = x⁻¹ δ x^σ` and `N = cyclicNorm σ l`. Then
`N(δ') = x⁻¹ N(δ) x^{σ^l} = x⁻¹ N(δ) x = γ`. Applying `σ` to `N(δ') = γ` gives
`δ'⁻¹ γ δ' = γ^σ = γ`, so `δ'` commutes with `γ`. The centralizer `G_γ(E)` of a regular
semisimple `γ` is commutative. If `y` is in `G^σ_{δ'}(F)`, then taking norms gives
`y⁻¹ γ y = γ`, so `y ∈ G_γ(E)` commutes with `δ'`, and `y⁻¹ δ' y^σ = δ'` becomes
`y^σ = y`, so `y` has entries in `F`. Conversely an element of `G_γ(F)` commutes with
`δ'` and is fixed by `σ`. Hence `G^σ_{δ'}(F)` is the image of `G_γ(F)` under
`baseChange` (HL, printed p. 14, the paragraph just before I.2.4). By lemma 9,
conjugation by `x` carries `G^σ_δ(F)` into `G^σ_{δ'}(F)`; lemma 9 for `x⁻¹` at `δ'`
carries `G^σ_{δ'}(F)` back into `G^σ_δ(F)`, so the conjugation is onto. Item 3 thus says that `μδ` is transported from `μγ` through the isomorphism
`G^σ_δ(F) → G^σ_{δ'}(F) = G_γ(F)`, which is HL's definition (I.2.5, p. 17). It does not
depend on `x`: another choice is `x y` with `y ∈ G_γ(E)`, and `y` commutes with the
commutative group `G_γ(F) ⊂ G_γ(E)`, so both conjugations give the same map.

**Fixed versus quantified measures.** HL fix Haar measures `dg` and `dg_E` and,
for each pair `(δ, γ)`, associated Haar measures `dg^σ_δ`, `dg_γ` and the quotients
`dg_E/dg^σ_δ`, `dg/dg_γ`. Items 4 and 5 take `μF` and `μE` as parameters and quantify
over all the other measures. The two agree:
right Haar measures on `G_γ(F)` are the positive multiples of one of them, scaling
`dg_γ` by `c > 0` scales the associated measure by `c`, and, by Weil's formula, scales
both compatible quotient measures by `c⁻¹`. Both sides of the equation in item 4 are
multiplied by `c⁻¹`, and the vanishing in item 5 is unchanged. Statement 10
(`OrbitalMeasureExistenceStatement`) provides the measures, so the universal
quantifiers in items 4 and 5 are not vacuous.

**Non-regular closed elements.** For closed non-regular `γ`, HL associate `dg^σ_δ` with
`dg_γ` through the inner form `H^σ_{δ'}` of the `L`-group scheme `H_γ`, `L = F[γ]`
(I.2.5, p. 17, citing their reference [57, 3.5]). This is not formalized. Concordance is
tested at regular `γ` only, which is HL's concordance; their strong concordance (at all
closed elements) is not part of this module.

**Regular elements.** The Library's `IsRegularSemisimple` asks for a separable
characteristic polynomial (HL's `G(F)'`). HL's regular elements have a characteristic
polynomial that is a product of pairwise distinct irreducible polynomials, that is,
squarefree (HL I.2.3, printed p. 13). The two agree in characteristic zero. In positive
characteristic the separable elements form a smaller set, so item 5 tests vanishing and
concordance at fewer elements than HL, and item 6 asks for support in a smaller set.

**Support.** The fibres of a locally constant `f` are open, so `{f ≠ 0}` is open and
closed and equals the support of `f` (its closure). For the Schwartz–Bruhat functions of
the statements, item 6 is therefore HL's condition that the support lies in `G(F)_r`,
respectively `G(E)_{σ-r}`.

## Dependencies

Task 7402 (`Langlands.TraceFormula.TwistedOrbital`): `twistedCentralizer`,
`twistedCentralizer_id`, `twistedOrbitalIntegral`, `orbitalIntegral`. Task 7405
(`Langlands.BaseChange.Norm`): `entrywiseAut`, `baseChange`, `cyclicNorm`,
`IsNormAssociated`, `IsNorm`, `IsSigmaRegular`. Library:
`Langlands.QuotientIntegration.IsCompatible` and `LeftQuotient`
(`Langlands/Analysis/Local/QuotientMeasure.lean`), `Langlands.GeneralLinear`,
`Langlands.JacquetLanglands.IsRegularSemisimple`. No measure is chosen or normalized in
a definition, and no axiom or unproved assertion is used.

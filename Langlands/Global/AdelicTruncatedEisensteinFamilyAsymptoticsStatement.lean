import Langlands.Global.AdelicTruncatedEisensteinAsymptoticsStatement

/-! # Asymptotics of truncated inner products for holomorphic families of inducing vectors

Lapid 2011, Proposition 1 (p.313, formula (2)), for holomorphic families
`λ ↦ ∑_l b_l(λ) v_l` of inducing vectors with entire coefficients, whose Eisenstein series is
assumed holomorphic near the parameters considered (nothing is assumed about the series of the
individual `v_l`), together with the projection property of the truncation (Arthur 2005, after
Proposition 13.1), for one common compact subgroup `K`.

* `LocalTruncatedEisensteinFamilyInnerProductStatement`: the proposition. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct CompactlySupported Classical

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints Langlands.Analysis.Meromorphic
  ArthurTruncation ArthurParabolicSpaces

/-- **Lapid 2011, Proposition 1 (p.313, formula (2)), under local regularity, for holomorphic
families of inducing vectors, jointly with Arthur's projection property.**

The data, normalizations and conclusion are those of
`LocalTruncatedEisensteinInnerProductStatement`, with two changes.

* The compact subgroup: the proposition asserts that some maximal compact `K` with
  `Q(𝔸)K = G(𝔸)` for `P_0` and every standard `Q`, with `P_0(𝔸) ∩ K` commuting with the
  positive torus of every Siegel setup, has both of the following properties: for all
  reflection data `D` and comparisons `hρ`, the norm-one and full-quotient truncations with
  respect to `K` extend to orthogonal projections on `L²` for sufficiently regular parameters
  (the conclusion of `TruncationOrthogonalProjectionStatement`), and the asymptotic formula
  below holds for all data with respect to `K`.
* The inducing data: `φ(λ) = ∑_l b_l(λ) v_l` with `v_l ∈ A^2_P` and entire coefficients `b_l`;
  `E` is holomorphic on `DE` and equals `∑_l b_l(λ) E_P(v_l, λ)` for sufficiently regular `λ`,
  and the expansions `∑_a coeff S t a λ • ψ S t a` are those of `M(w, λ)φ(λ)`; likewise for
  `P'`. Only the combination `E` is assumed holomorphic near the parameters considered, as in
  Lapid's hypothesis that `E_P(·, φ(λ), λ)` is smooth.

The asymptotic formula: for every finitely generated cone in the open positive chamber and every
compact set `C` of coordinate pairs with `λ = i e_P(x) ∈ i(𝔞_P^G)^*` in `DE ∩ DM` and
`λ' = i e_{P'}(x') ∈ i(𝔞_{P'}^G)^*` in `DE' ∩ DM'`, the truncations `Λ^T E(λ)`, `Λ^T E'(λ')`
are square integrable on `G(F) \ G(𝔸)¹` and, off the hyperplanes `⟨wλ + w'λ̄', α^∨⟩ = 0`,
`|(Λ^T E(λ), Λ^T E'(λ'))_{G(F)\G(𝔸)¹} − M(T; λ, λ')| ≤ const · e^{−δ ∑ τ_j}` for
`T = ∑ τ_j gen_j` beyond a threshold, with the main term of
`LocalTruncatedEisensteinInnerProductStatement`. -/
def LocalTruncatedEisensteinFamilyInnerProductStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    IsGenericCocharacter i ν →
  ∃ K : Subgroup (AdelicGroupPoints F G),
    IsMaximalCompactSubgroup F G K ∧
    IsIwasawaCompact (Standard.parabolicHom i ν ∅) K ∧
    (∀ S : StandardIndex hG hi ν, IsIwasawaCompact (Standard.parabolicHom i ν S.roots) K) ∧
    (∀ (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
      AdelicSiegelFactors.IsSiegelAlgebraicSetup F G T i ν T₀ j →
        AdelicSiegelFactors.IsPositiveTorusCompatible F G T i ν T₀ j K) ∧
  ∀ (D : RelativeRootReflectionData i) (hρ : Function.Bijective (restrictToTorus F i ν ∅))
    (hK₀ : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hK : ∀ S : StandardIndex hG hi ν, IsIwasawaCompact (Standard.parabolicHom i ν S.roots) K),
    (∃ C : ℝ, ∀ Tp : V T, (∀ β ∈ simpleRelativeRoots i ν, C < eval T β Tp) →
      IsOrthogonalL2Extension (normOneRationalQuotientHaarMeasure F G)
          (fun f q => normOneTruncation hG hi D hK₀ hρ Tp
            (fun x => f (LeftCosetSpace.mk (rationalNormOneSubgroup F G) x)) q.out) ∧
        IsOrthogonalL2Extension (rationalQuotientHaarMeasure F G)
          (fun f q => truncation hG hi D hK₀ hρ Tp
            (fun x => f (LeftCosetSpace.mk (rationalSubgroup F G) x)) q.out)) ∧
  ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsClosedSubgroup rho →
  ∀ (π : ∀ S : StandardIndex hG hi ν,
      Standard.parabolicScheme i ν S.roots ⟶ Standard.leviScheme i ν S.roots),
    (∀ S : StandardIndex hG hi ν,
      Standard.leviToParabolic i ν S.roots ≫ π S = 𝟙 (Standard.leviScheme i ν S.roots)) →
  ∀ (μM : ∀ S : StandardIndex hG hi ν,
      Measure (AdelicGroupPoints F (Standard.leviScheme i ν S.roots))),
    (∀ S : StandardIndex hG hi ν, (μM S).IsHaarMeasure ∧
      IsIwasawaCompatibleMeasure K (hK S).isCompact (Standard.parabolicHom i ν S.roots)
        (Standard.unipotentToParabolic i ν S.roots) (Standard.leviToParabolic i ν S.roots)
        (μM S)) →
  ∀ (n : StandardIndex hG hi ν → ℕ)
    (e : ∀ S : StandardIndex hG hi ν, (Fin (n S) → ℝ) ≃ₗ[ℝ]
      RealCharacterParameter F (Standard.parabolicScheme i ν S.roots))
    (β : ∀ S : StandardIndex hG hi ν, (Fin (n S) → ℝ) → ℝ),
    (∀ S : StandardIndex hG hi ν, Continuous (β S) ∧ HasCompactSupport (β S) ∧ ∫ y, β S y = 1) →
  ∀ (m : ℕ) (c : Fin m → V T), LinearIndependent ℝ c →
    Submodule.span ℝ (Set.range c) = relativeCentralDirections i →
  ∀ (μ₁ : Measure (normOneSubgroup F G)), μ₁.IsHaarMeasure →
  ∀ (s : (Fin m → ℝ) → AdelicGroupPoints F G),
    (∀ (y : Fin m → ℝ) (χ : rationalCharacters G),
      characterLog F G (s y) χ =
        pair T (rationalCharacterRestrictReal i ((1 : ℝ) ⊗ₜ[ℤ] χ)) (∑ k, y k • c k)) →
    (∀ f : C_c(AdelicGroupPoints F G, ℂ),
      ∫ g, f g ∂(Measure.haar : Measure (AdelicGroupPoints F G)) =
        ∫ y, ∫ x, f ((x : AdelicGroupPoints F G) * s y) ∂μ₁ ∂(volume : Measure (Fin m → ℝ))) →
  ∀ (J : StandardIndex hG hi ν) (q : ℕ) (v : Fin q → AdelicGroupPoints F G → ℂ)
    (b : Fin q → ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots) → ℂ)
    (E : ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots) →
      AdelicGroupPoints F G → ℂ)
    (DE : Set (ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots))),
    (∀ l, IsSquareIntegrableInducedForm K (hK J).isCompact rho hsmooth hcalc
      (Standard.parabolicHom i ν J.roots) (Standard.unipotentToParabolic i ν J.roots)
      (Standard.leviToParabolic i ν J.roots) (v l)) →
    (∀ l, IsMeromorphicInCoordinatesOn (b l) Set.univ) →
    (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) DE) →
    (∃ R : ℝ, ∀ lam, IsStandardRegularParameter D J.roots R lam → ∀ g,
      E lam g = ∑ l, b l lam * (hK J).eisensteinSeries (v l) lam g) →
  ∀ (Ω : StandardIndex hG hi ν → Type) [∀ S : StandardIndex hG hi ν, Fintype (Ω S)]
    (w : ∀ S : StandardIndex hG hi ν, Ω S → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
    (cw : ∀ S : StandardIndex hG hi ν, Ω S →
      (Standard.leviScheme i ν S.roots ⟶ Standard.leviScheme i ν J.roots)),
    (∀ (S : StandardIndex hG hi ν) t, IsWeylConjugation (Standard.parabolicHom i ν J.roots)
      (Standard.leviToParabolic i ν J.roots) (Standard.parabolicHom i ν S.roots)
      (Standard.leviToParabolic i ν S.roots) (w S t) (cw S t)) →
    (∀ S : StandardIndex hG hi ν, Function.Injective
      (fun t => weylParameter (Standard.leviToParabolic i ν J.roots) (cw S t) (π S))) →
    (∀ S : StandardIndex hG hi ν, ∀ σ ∈ weylParameterSet (Standard.parabolicHom i ν J.roots)
        (Standard.leviToParabolic i ν J.roots) (Standard.parabolicHom i ν S.roots)
        (Standard.leviToParabolic i ν S.roots) (π S),
      ∃ t, weylParameter (Standard.leviToParabolic i ν J.roots) (cw S t) (π S) = σ) →
  ∀ (k : ℕ) (ψ : ∀ S : StandardIndex hG hi ν, Ω S → Fin k → AdelicGroupPoints F G → ℂ)
    (coeff : ∀ S : StandardIndex hG hi ν, Ω S → Fin k →
      ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots) → ℂ)
    (DM : Set (ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots))),
    (∀ (S : StandardIndex hG hi ν) t a,
      IsSquareIntegrableInducedForm K (hK S).isCompact rho hsmooth hcalc
      (Standard.parabolicHom i ν S.roots) (Standard.unipotentToParabolic i ν S.roots)
      (Standard.leviToParabolic i ν S.roots) (ψ S t a)) →
    (∀ (S : StandardIndex hG hi ν) t a, IsMeromorphicInCoordinatesOn (coeff S t a) DM) →
    (∀ (S : StandardIndex hG hi ν) t, ∃ R : ℝ,
      ∀ lam, IsStandardRegularParameter D J.roots R lam → ∀ g,
      ∑ l, b l lam * (hK J).intertwiningOperator (hK S)
          (Standard.unipotentToParabolic i ν J.roots)
          (Standard.leviToParabolic i ν J.roots) (Standard.unipotentToParabolic i ν S.roots)
          (cw S t) (π S) (w S t) (v l) lam g =
        ∑ a, coeff S t a lam * ψ S t a g) →
  ∀ (J' : StandardIndex hG hi ν) (q' : ℕ) (v' : Fin q' → AdelicGroupPoints F G → ℂ)
    (b' : Fin q' → ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots) → ℂ)
    (E' : ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots) →
      AdelicGroupPoints F G → ℂ)
    (DE' : Set (ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots))),
    (∀ l, IsSquareIntegrableInducedForm K (hK J').isCompact rho hsmooth hcalc
      (Standard.parabolicHom i ν J'.roots) (Standard.unipotentToParabolic i ν J'.roots)
      (Standard.leviToParabolic i ν J'.roots) (v' l)) →
    (∀ l, IsMeromorphicInCoordinatesOn (b' l) Set.univ) →
    (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E' lam g) DE') →
    (∃ R : ℝ, ∀ lam, IsStandardRegularParameter D J'.roots R lam → ∀ g,
      E' lam g = ∑ l, b' l lam * (hK J').eisensteinSeries (v' l) lam g) →
  ∀ (Ω' : StandardIndex hG hi ν → Type) [∀ S : StandardIndex hG hi ν, Fintype (Ω' S)]
    (w' : ∀ S : StandardIndex hG hi ν, Ω' S → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
    (cw' : ∀ S : StandardIndex hG hi ν, Ω' S →
      (Standard.leviScheme i ν S.roots ⟶ Standard.leviScheme i ν J'.roots)),
    (∀ (S : StandardIndex hG hi ν) t, IsWeylConjugation (Standard.parabolicHom i ν J'.roots)
      (Standard.leviToParabolic i ν J'.roots) (Standard.parabolicHom i ν S.roots)
      (Standard.leviToParabolic i ν S.roots) (w' S t) (cw' S t)) →
    (∀ S : StandardIndex hG hi ν, Function.Injective
      (fun t => weylParameter (Standard.leviToParabolic i ν J'.roots) (cw' S t) (π S))) →
    (∀ S : StandardIndex hG hi ν, ∀ σ ∈ weylParameterSet (Standard.parabolicHom i ν J'.roots)
        (Standard.leviToParabolic i ν J'.roots) (Standard.parabolicHom i ν S.roots)
        (Standard.leviToParabolic i ν S.roots) (π S),
      ∃ t, weylParameter (Standard.leviToParabolic i ν J'.roots) (cw' S t) (π S) = σ) →
  ∀ (k' : ℕ) (ψ' : ∀ S : StandardIndex hG hi ν, Ω' S → Fin k' → AdelicGroupPoints F G → ℂ)
    (coeff' : ∀ S : StandardIndex hG hi ν, Ω' S → Fin k' →
      ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots) → ℂ)
    (DM' : Set (ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots))),
    (∀ (S : StandardIndex hG hi ν) t a,
      IsSquareIntegrableInducedForm K (hK S).isCompact rho hsmooth hcalc
      (Standard.parabolicHom i ν S.roots) (Standard.unipotentToParabolic i ν S.roots)
      (Standard.leviToParabolic i ν S.roots) (ψ' S t a)) →
    (∀ (S : StandardIndex hG hi ν) t a, IsMeromorphicInCoordinatesOn (coeff' S t a) DM') →
    (∀ (S : StandardIndex hG hi ν) t, ∃ R : ℝ,
      ∀ lam, IsStandardRegularParameter D J'.roots R lam → ∀ g,
      ∑ l, b' l lam * (hK J').intertwiningOperator (hK S)
          (Standard.unipotentToParabolic i ν J'.roots)
          (Standard.leviToParabolic i ν J'.roots) (Standard.unipotentToParabolic i ν S.roots)
          (cw' S t) (π S) (w' S t) (v' l) lam g =
        ∑ a, coeff' S t a lam * ψ' S t a g) →
  ∀ (r : ℕ) (gen : Fin r → V T), (∀ j, ∀ α ∈ simpleRelativeRoots i ν, 0 < eval T α (gen j)) →
  ∀ (C : Set ((Fin (n J) → ℝ) × (Fin (n J') → ℝ))), IsCompact C →
    (∀ x ∈ C,
      restrictToTorus F i ν J.roots (e J x.1) ∈ relativeRootSpanReal i ∧
      restrictToTorus F i ν J'.roots (e J' x.2) ∈ relativeRootSpanReal i ∧
      imaginaryParameter F _ (e J x.1) ∈ DE ∩ DM ∧
      imaginaryParameter F _ (e J' x.2) ∈ DE' ∩ DM') →
  let μQ : Measure (NormOneRationalQuotient F G) :=
    LeftCosetSpace.discreteQuotientMeasure (rationalNormOneSubgroup F G)
      (isDiscrete_rationalNormOneSubgroup F G) μ₁
  let ΛE (Tp : V T) (lam : ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots))
      (q : NormOneRationalQuotient F G) : ℂ :=
    normOneTruncation hG hi D hK₀ hρ Tp (fun x => E lam x) q.out
  let ΛE' (Tp : V T) (lam' : ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots))
      (q : NormOneRationalQuotient F G) : ℂ :=
    normOneTruncation hG hi D hK₀ hρ Tp (fun x => E' lam' x) q.out
  let Λ (S : StandardIndex hG hi ν) (t : Ω S) (t' : Ω' S)
      (lam : ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots))
      (lam' : ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots)) :
      ComplexCharacterParameter F (Standard.parabolicScheme i ν S.roots) :=
    weylParameter (Standard.leviToParabolic i ν J.roots) (cw S t) (π S) lam +
      weylParameter (Standard.leviToParabolic i ν J'.roots) (cw' S t') (π S)
        (parameterConj F _ lam')
  let denom (S : StandardIndex hG hi ν) (t : Ω S) (t' : Ω' S)
      (lam : ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots))
      (lam' : ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots)) : ℂ :=
    ∏ α ∈ simpleFinset ν hG hi \ S.1,
      complexParameterPairing F _ (Λ S t t' lam lam')
        (toCharacterDual F i ν S.roots (corootVector D α))
  let mainTerm (Tp : V T)
      (lam : ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots))
      (lam' : ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots)) : ℂ :=
    ∑ S : StandardIndex hG hi ν, ∑ t : Ω S, ∑ t' : Ω' S,
      (corootCovolume hG hi ν D S (e S) c : ℂ) *
        Complex.exp (complexParameterPairing F _ (Λ S t t' lam lam')
          (toCharacterDual F i ν S.roots Tp)) *
        (∑ a, ∑ b, coeff S t a lam * (starRingEnd ℂ) (coeff' S t' b lam') *
          inducedInnerProduct K (hK S).isCompact (Standard.parabolicHom i ν S.roots)
            (Standard.leviToParabolic i ν S.roots) (μM S) (e S) (β S) (ψ S t a) (ψ' S t' b)) /
        denom S t t' lam lam'
  ∃ δ : ℝ, 0 < δ ∧ ∃ B t₀ : ℝ, ∀ τ : Fin r → ℝ, (∀ j, 0 ≤ τ j) → t₀ ≤ ∑ j, τ j →
    ∀ x ∈ C,
      MemLp (ΛE (∑ j, τ j • gen j) (imaginaryParameter F _ (e J x.1))) 2 μQ ∧
      MemLp (ΛE' (∑ j, τ j • gen j) (imaginaryParameter F _ (e J' x.2))) 2 μQ ∧
      ((∀ (S : StandardIndex hG hi ν) t t', denom S t t' (imaginaryParameter F _ (e J x.1))
          (imaginaryParameter F _ (e J' x.2)) ≠ 0) →
        ‖(∫ q, ΛE (∑ j, τ j • gen j) (imaginaryParameter F _ (e J x.1)) q *
              (starRingEnd ℂ) (ΛE' (∑ j, τ j • gen j) (imaginaryParameter F _ (e J' x.2)) q)
            ∂μQ) -
          mainTerm (∑ j, τ j • gen j) (imaginaryParameter F _ (e J x.1))
            (imaginaryParameter F _ (e J' x.2))‖ ≤
        B * Real.exp (-(δ * ∑ j, τ j)))

end Langlands.Global

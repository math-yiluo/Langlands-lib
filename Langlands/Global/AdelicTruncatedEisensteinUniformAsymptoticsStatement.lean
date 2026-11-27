import Langlands.Global.AdelicTruncatedEisensteinFamilyAsymptoticsStatement

/-! # Truncated Eisenstein families: asymptotics and locally uniform square integrability

Lapid 2011, Proposition 1 (p.313, formula (2)), for holomorphic families of inducing vectors,
jointly with Arthur's projection property, as in
`LocalTruncatedEisensteinFamilyInnerProductStatement`, but with the error term uniform also in
the central parameter (pairs of imaginary parameters with equal central components), together
with a third property of the same compact subgroup `K`: for a holomorphic family as there and a
compact set of imaginary
parameters inside its domain of holomorphy, the truncations `Λ^T E(λ)` on `G(F) \ G(𝔸)¹` are
jointly measurable in `(λ, g)` and bounded in `L²` uniformly in `λ`, for every sufficiently
regular `T` (Arthur 1980, Lemma 1.4, with Lapid's Working hypothesis).

* `LocalTruncatedEisensteinFamilyUniformInnerProductStatement`: the proposition.
* `localTruncatedEisensteinFamilyInnerProduct_of_uniform`: it implies
  `LocalTruncatedEisensteinFamilyInnerProductStatement`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct CompactlySupported Classical

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints Langlands.Analysis.Meromorphic
  ArthurTruncation ArthurParabolicSpaces

/-- **Lapid 2011, Proposition 1 (p.313, formula (2)), for holomorphic families of inducing
vectors, uniformly in the central parameter, jointly with Arthur's projection property and the
locally uniform square integrability of truncated families.**

The statement has the layout of `LocalTruncatedEisensteinFamilyInnerProductStatement` with two
changes, for the same compact subgroup `K` and the same `D`, `hρ`, `hK₀`, `hK`.

First, the asymptotic formula is asserted on compact sets `C` of pairs of full parameters
`(i e(x), i e'(x'))` in `i𝔞_P^* × i𝔞_{P'}^*` whose central components agree, that is, with
`λ|_T − λ'|_T` in the real span of the roots, instead of pairs in `i(𝔞_P^G)^* × i(𝔞_{P'}^G)^*`.
For `μ ∈ i𝔞_G^*` the restrictions to `G(𝔸)¹` of `E_P(φ(λ + μ), λ + μ)` and
`E_P(φ(λ + μ), λ)` agree, so this is Proposition 1 for the shifted families `φ(· + μ)` with the
error uniform in `μ`, as used in Lapid's §8 (p.328).

Second, there is one more conjunct: for every closed matrix
realization, every Haar measure `μ₁` on `G(𝔸)¹`, every standard `J`, every holomorphic family
`φ(λ) = ∑_l b_l(λ) v_l` (`v_l ∈ A^2_P`, `b_l` entire) with `E` holomorphic on `DE` and equal to
`∑_l b_l(λ) E_P(v_l, λ)` for sufficiently regular `λ`, every real linear coordinates `e` on
`X^*(P) ⊗ ℝ` and every compact set `C` of coordinates with `i e(x) ∈ DE` for `x ∈ C`, there
is a threshold `c₀` such that for every `T` with `β(T) > c₀` for all simple roots `β`:

* `(x, y) ↦ Λ^T E(i e(x))(y)` is almost everywhere strongly measurable on `C × G(F) \ G(𝔸)¹`
  for the product of Lebesgue measure on `C` and the quotient measure of `μ₁`;
* for some `B` and every `x ∈ C`, `Λ^T E(i e(x))` is square integrable on `G(F) \ G(𝔸)¹`
  with `∫ |Λ^T E(i e(x))|² ≤ B`.

The parameters `i e(x)` range over `i𝔞_P^*`, not only `i(𝔞_P^G)^*`: on `G(𝔸)¹` only the
restriction of `E(λ)` enters. -/
def LocalTruncatedEisensteinFamilyUniformInnerProductStatement : Prop :=
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
  (∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
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
      restrictToTorus F i ν J.roots (e J x.1) - restrictToTorus F i ν J'.roots (e J' x.2) ∈
        relativeRootSpanReal i ∧
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
        B * Real.exp (-(δ * ∑ j, τ j)))) ∧
  ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsClosedSubgroup rho →
  ∀ (μ₁ : Measure (normOneSubgroup F G)), μ₁.IsHaarMeasure →
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
  ∀ (n : ℕ)
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (Standard.parabolicScheme i ν J.roots))
    (C : Set (Fin n → ℝ)), IsCompact C →
    (∀ x ∈ C, imaginaryParameter F _ (e x) ∈ DE) →
  let μQ : Measure (NormOneRationalQuotient F G) :=
    LeftCosetSpace.discreteQuotientMeasure (rationalNormOneSubgroup F G)
      (isDiscrete_rationalNormOneSubgroup F G) μ₁
  let ΛE (Tp : V T) (x : Fin n → ℝ) (q : NormOneRationalQuotient F G) : ℂ :=
    normOneTruncation hG hi D hK₀ hρ Tp (fun g => E (imaginaryParameter F _ (e x)) g) q.out
  ∃ c₀ : ℝ, ∀ Tp : V T, (∀ β ∈ simpleRelativeRoots i ν, c₀ < eval T β Tp) →
    AEStronglyMeasurable (fun z : (Fin n → ℝ) × NormOneRationalQuotient F G => ΛE Tp z.1 z.2)
      ((volume.restrict C).prod μQ) ∧
    ∃ B : ℝ, ∀ x ∈ C, MemLp (ΛE Tp x) 2 μQ ∧ ∫ q, ‖ΛE Tp x q‖ ^ 2 ∂μQ ≤ B

/-- The proposition contains `LocalTruncatedEisensteinFamilyInnerProductStatement`: on a compact
set of parameters in `i(𝔞_P^G)^* × i(𝔞_{P'}^G)^*` the central components agree (both vanish), so
the asymptotic formula of the second part applies; the third part is dropped. -/
theorem localTruncatedEisensteinFamilyInnerProduct_of_uniform
    (h : LocalTruncatedEisensteinFamilyUniformInnerProductStatement) :
    LocalTruncatedEisensteinFamilyInnerProductStatement := by
  intro F _ _ G _ _ T i _ ν hG hi hν
  obtain ⟨K, hKmax, hK₀, hK, hpos, hrest⟩ := h F G T i ν hG hi hν
  refine ⟨K, hKmax, hK₀, hK, hpos, fun D hρ hK₀' hK' => ⟨(hrest D hρ hK₀' hK').1, ?_⟩⟩
  intro N d rho hsmooth hcalc hrho π hπ μM hμM n e β hβ m c hc hspan μ₁ hμ₁ s hs hHaar
    J q v b E DE hv hb hE hEis Ω _ w cw hw hinj hsurj k ψ coeff DM hψ hcoeff hexp
    J' q' v' b' E' DE' hv' hb' hE' hEis' Ω' _ w' cw' hw' hinj' hsurj' k' ψ' coeff' DM' hψ'
    hcoeff' hexp' r gen hgen C hC hCx
  exact (hrest D hρ hK₀' hK').2.1 rho hsmooth hcalc hrho π hπ μM hμM n e β hβ m c hc hspan μ₁
    hμ₁ s hs hHaar J q v b E DE hv hb hE hEis Ω w cw hw hinj hsurj k ψ coeff DM hψ hcoeff hexp
    J' q' v' b' E' DE' hv' hb' hE' hEis' Ω' w' cw' hw' hinj' hsurj' k' ψ' coeff' DM' hψ'
    hcoeff' hexp' r gen hgen C hC fun x hx =>
      ⟨Submodule.sub_mem _ (hCx x hx).1 (hCx x hx).2.1, (hCx x hx).2.2⟩

end Langlands.Global

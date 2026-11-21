import Langlands.Global.AdelicInducedInnerProduct
import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Global.AdelicIntertwiningImaginaryUnitarityReduction
import Langlands.Analysis.Meromorphic.LinearCoordinates
import Langlands.GroupScheme.Dynamic.RepresentedStructure

/-! # Adjunction of continued intertwining operators

Mœglin–Waldspurger II.1.8 (pp.93–94) and IV.1.9 (e): `(M(w, λ)φ, φ')_{P'} = (φ, M(w⁻¹, -wλ̄)φ')_P`
for `φ ∈ A^2_P`, `φ' ∈ A^2_{P'}`, first for `Re λ` in the cone of absolute convergence and then,
by meromorphic continuation, as an identity of meromorphic functions of `λ`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Adjunction of the continued intertwining operators `M(w, λ)` and `M(w⁻¹, -wλ̄)`
(Mœglin–Waldspurger II.1.8 and IV.1.9 (e)). Let `P = MU` and `P' = M'U'` be parabolics of a
connected reductive `G` over a number field with presentations `r`, `r'` and Levi retractions
`π`, `π'`, let `(w, cw)` present an element of `W(P, P')` and `(w⁻¹, cw')` its inverse in
`W(P', P)`, and fix `K`, Iwasawa-compatible Haar measures `μM`, `μM'`, real coordinates `e` and
`e' = w ∘ e` and weights `β`, `β'` of integral `1`, which define `(·,·)_P` and `(·,·)_{P'}`.
Take `φ ∈ A^2_P` with `M(w, λ)φ = ∑ i, coeff i λ • ψ i` for `Re λ` sufficiently regular
(`ψ i ∈ A^2_{P'}`, `coeff i` meromorphic with domain `D`), and `φ' i' ∈ A^2_{P'}` with
`M(w⁻¹, ν)(φ' i') = ∑ x, coeff' i' x ν • χ x` for `Re ν` sufficiently regular (`χ x` automorphic
on `U(𝔸)M(F) \ G(𝔸)`, `coeff' i' x` meromorphic with domain `D'`). Then, writing
`λ = realChart e s` (so that `-λ̄ = realChart e (-conj s)`), for `s` in an open dense subset of
`ℂⁿ`, `λ ∈ D` and `-wλ̄ ∈ D'`, and every finite combination `∑ i', c i' • φ' i'` for which the
product of `φ` with the conjugate of `M(w⁻¹, -wλ̄)(∑ i', c i' • φ' i')` is integrable on
`K × M(F) \ M(𝔸)`, `(M(w, λ)φ, ∑ i', c i' • φ' i')_{P'} = (φ, M(w⁻¹, -wλ̄)(∑ i', c i' • φ' i'))_P`,
where both operators are given by the continued expansions. -/
def IntertwiningContinuedAdjunctionStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U P' M' U' : GroupScheme (Spec (CommRingCat.of F)))
    (A A' : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    [IsAffine P'.X.left] [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]
    [IsAffine U'.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    [IsClosedImmersion (iU ≫ p).hom.hom.left]
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) (π : P ⟶ M)
    (p' : P' ⟶ G) [IsClosedImmersion p'.hom.hom.left] (iU' : U' ⟶ P') (l' : M' ⟶ P')
    [IsClosedImmersion (iU' ≫ p').hom.hom.left]
    (a' : A'.toGrp ⟶ M') (r' : ParabolicRootPresentation p' l' a')
    [Mono r'.data.i.hom.hom.left] [Fintype (relativeWeylGroup r'.data.i)]
    [Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left]
    (hA' : IsSplitTorus A'.toGrp) (hT' : IsSplitTorus r'.data.T.toGrp) (π' : P' ⟶ M')
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (cw : M' ⟶ M) (cw' : M ⟶ M'),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    haveI : LocallyOfFiniteType P'.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p') ‹IsClosedImmersion p'.hom.hom.left›
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    LeviSubgroup.IsGeometricUnipotentRadical iU' → l ≫ π = 𝟙 M → l' ≫ π' = 𝟙 M' →
    IsWeylConjugation p l p' l' w cw → IsWeylConjugation p' l' p l w⁻¹ cw' →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hK' : IsIwasawaCompact p' K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (μM : Measure (AdelicGroupPoints F M)) [μM.IsHaarMeasure]
      (μM' : Measure (AdelicGroupPoints F M')) [μM'.IsHaarMeasure],
      IsIwasawaCompatibleMeasure K hK.isCompact p iU l μM →
      IsIwasawaCompatibleMeasure K hK'.isCompact p' iU' l' μM' →
    ∀ {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
      (e' : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P'),
      (∀ x, e' x = realWeylParameter l cw π' (e x)) →
    ∀ (β β' : (Fin n → ℝ) → ℝ),
      Continuous β → HasCompactSupport β → ∫ y, β y = 1 →
      Continuous β' → HasCompactSupport β' → ∫ y, β' y = 1 →
    ∀ (φ : AdelicGroupPoints F G → ℂ) (k : ℕ) (ψ : Fin k → AdelicGroupPoints F G → ℂ)
      (coeff : Fin k → ComplexCharacterParameter F P → ℂ)
      (D : Set (ComplexCharacterParameter F P)),
      IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l φ →
      (∀ i, IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' (ψ i)) →
      (∀ i, IsMeromorphicInCoordinatesOn (coeff i) D) →
      (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
        hK.intertwiningOperator hK' iU l iU' cw π' w φ lam g = ∑ i, coeff i lam * ψ i g) →
    ∀ (m : ℕ) (φ' : Fin m → AdelicGroupPoints F G → ℂ) (k' : ℕ)
      (χ : Fin k' → AdelicGroupPoints F G → ℂ)
      (coeff' : Fin m → Fin k' → ComplexCharacterParameter F P' → ℂ)
      (D' : Set (ComplexCharacterParameter F P')),
      (∀ i', IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' (φ' i')) →
      (∀ x, IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
        (K.comap (ofInfinite F G).toMonoidHom) rho (χ x)) →
      (∀ i' x, IsMeromorphicInCoordinatesOn (coeff' i' x) D') →
      (∀ i', ∃ R : ℝ, ∀ nu, r'.IsRegularParameter hA' hT' R nu → ∀ g,
        hK'.intertwiningOperator hK iU' l' iU cw' π w⁻¹ (φ' i') nu g =
          ∑ x, coeff' i' x nu * χ x g) →
    ∃ S : Set (Fin n → ℂ), IsOpen S ∧ Dense S ∧ ∀ s ∈ S, realChart e s ∈ D →
      weylParameter l cw π' (realChart e (fun t => -(starRingEnd ℂ) (s t))) ∈ D' →
      ∀ c : Fin m → ℂ,
        Integrable (AdelicGroupPoints.inducedInnerProductIntegrand K p l e β φ
            (fun g => ∑ x, (∑ i', c i' *
              coeff' i' x (weylParameter l cw π' (realChart e (fun t => -(starRingEnd ℂ) (s t))))) *
                χ x g))
          ((compactHaarProbability F G K hK.isCompact).prod
            (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
              (isDiscrete_rationalSubgroup F M) μM)) →
        inducedInnerProduct K hK'.isCompact p' l' μM' e' β'
            (fun g => ∑ i, coeff i (realChart e s) * ψ i g) (fun g => ∑ i', c i' * φ' i' g) =
          inducedInnerProduct K hK.isCompact p l μM e β φ
            (fun g => ∑ x, (∑ i', c i' *
              coeff' i' x (weylParameter l cw π' (realChart e (fun t => -(starRingEnd ℂ) (s t))))) *
                χ x g)

end Langlands.Global

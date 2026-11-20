import Langlands.Global.AdelicInducedInnerProduct
import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Analysis.Meromorphic.LinearCoordinates
import Langlands.GroupScheme.Dynamic.RepresentedStructure

/-! # Isometry of intertwining operators at imaginary points of holomorphy

Mœglin–Waldspurger IV.3.12 (p.161), first step: from the adjunction formula and the functional
equation, `(M(w, λ)φ, M(w, λ)φ')_{P'} = (φ, φ')_P` for every `λ ∈ i𝔞_P^*` at which `M(w, ·)` is
holomorphic. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Isometry of `M(w, λ)` at the imaginary points where it is holomorphic (Mœglin–Waldspurger
IV.3.12, first step; Lapid 2011, p.312). In the setting of
`IntertwiningImaginaryUnitarityStatement`, let `M(w, λ) v j = ∑ i, coeff j i λ • ψ j i` for
`Re λ` sufficiently regular, with `coeff j i` meromorphic with one domain `DM`. Let `coeff'` be
any coefficients, meromorphic with one domain `DM'`, that give the same functions
`∑ i, coeff' j i λ • ψ j i = ∑ i, coeff j i λ • ψ j i` for `λ ∈ DM ∩ DM'`. Then for every
imaginary `λ ∈ DM'`
`(∑ i, coeff' j i λ • ψ j i, ∑ i', coeff' j' i' λ • ψ j' i')_{P'} = (v j, v j')_P`. -/
def IntertwiningImaginaryIsometryStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U P' M' U' : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    [IsAffine P'.X.left] [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]
    [IsAffine U'.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    [IsClosedImmersion (iU ≫ p).hom.hom.left]
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (p' : P' ⟶ G) [IsClosedImmersion p'.hom.hom.left] (iU' : U' ⟶ P') (l' : M' ⟶ P')
    [IsClosedImmersion (iU' ≫ p').hom.hom.left] (π' : P' ⟶ M')
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (cw : M' ⟶ M),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    haveI : LocallyOfFiniteType P'.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p') ‹IsClosedImmersion p'.hom.hom.left›
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    IsParabolicSubgroup p' → LeviSubgroup.IsGeometricUnipotentRadical iU' →
    IsRationalLeviSubgroup l' → IsIso (subgroupMultiplication l' iU') → l' ≫ π' = 𝟙 M' →
    IsWeylConjugation p l p' l' w cw →
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
    ∀ (k m : ℕ) (v : Fin k → AdelicGroupPoints F G → ℂ)
      (ψ : Fin k → Fin m → AdelicGroupPoints F G → ℂ)
      (coeff : Fin k → Fin m → ComplexCharacterParameter F P → ℂ)
      (DM : Set (ComplexCharacterParameter F P)),
      (∀ j, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (v j)) →
      (∀ j i,
        IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' (ψ j i)) →
      (∀ j i, IsMeromorphicInCoordinatesOn (coeff j i) DM) →
      (∀ j, ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
        hK.intertwiningOperator hK' iU l iU' cw π' w (v j) lam g =
          ∑ i, coeff j i lam * ψ j i g) →
    ∀ (coeff' : Fin k → Fin m → ComplexCharacterParameter F P → ℂ)
      (DM' : Set (ComplexCharacterParameter F P)),
      (∀ j i, IsMeromorphicInCoordinatesOn (coeff' j i) DM') →
      (∀ j, ∀ lam ∈ DM ∩ DM', ∀ g,
        ∑ i, coeff' j i lam * ψ j i g = ∑ i, coeff j i lam * ψ j i g) →
      ∀ (mu : RealCharacterParameter F P) (j j' : Fin k),
        imaginaryParameter F P mu ∈ DM' →
        ∑ i, ∑ i', coeff' j i (imaginaryParameter F P mu) *
            (starRingEnd ℂ) (coeff' j' i' (imaginaryParameter F P mu)) *
            inducedInnerProduct K hK'.isCompact p' l' μM' e' β' (ψ j i) (ψ j' i') =
          inducedInnerProduct K hK.isCompact p l μM e β (v j) (v j')

end Langlands.Global

import Langlands.Global.AdelicTruncatedEisensteinPairing
import Langlands.Global.AdelicSiegelFiniteVolume
import Langlands.Analysis.Meromorphic.LinearCoordinates

/-! # Truncated pairing of Eisenstein series with a logarithmically square-integrable form -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints
  Automorphic.GroupSchemeFunctions AdelicSiegelFactors Langlands.Analysis.Meromorphic

namespace StandardParabolicFamily

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

/-- The truncation parameter is in the relative coroot space, and every simple root
is at least the stated positive threshold. -/
def IsRegularTruncationParameter (R : ℝ) (T : V fam.T) : Prop :=
  T ∈ fam.coroots.realCorootSpan ∧
  ∀ α ∈ simpleRelativeRoots fam.i fam.ν, R ≤ eval fam.T α T

end StandardParabolicFamily

/-- The analytic extension and exponential comparison of the characteristic and regularized
pairings, with a logarithmically square-integrable tested form. Positive Haar scalars and the
Siegel domain are fixed before choosing the test forms. -/
def EisensteinTemperedTruncationEstimateStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G),
  ∃ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact (fam.p fam.bot) K)
    (C : CompactFactors F G (Standard.unipotentScheme fam.i fam.ν ∅)
      (Standard.leviScheme fam.i fam.ν ∅))
    (T₀ : V fam.T) (vol : StandardIndex F G fam.i fam.ν → ℝ),
    IsMaximalCompactSubgroup F G K ∧
    (∀ J, IsMaximalCompactSubgroup F (fam.M J)
      (K.comap (map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom)) ∧
    IsPositiveTorusCompatible F G fam.T fam.i fam.ν fam.T (𝟙 fam.T) K ∧
    C.compactSubgroup = K ∧ ArthurTruncation.IsRationalCovering C ∧
    (∀ q : NormOneRationalQuotient F G, ∃ T, q ∈ fam.truncationRegion hK C T₀ T) ∧
    (∀ Q, 0 < vol Q) ∧
  ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsClosedSubgroup rho →
  ∀ (P : StandardIndex F G fam.i fam.ν) (Φ φ : AdelicGroupPoints F G → ℂ),
    IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ →
    IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc
      (fam.p P) (fam.iU P) (fam.l P) φ →
  ∀ (_ : IsClosedImmersion (fam.p P).hom.hom.left)
    (hKP : IsIwasawaCompact (fam.p P) K)
    (r : ParabolicRootPresentation (fam.p P) (fam.l P) (fam.a P))
    (_ : Mono r.data.i.hom.hom.left) (_ : Fintype (relativeWeylGroup r.data.i))
    (_ : Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left)
    (hA : IsSplitTorus (fam.A P).toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (E : ComplexCharacterParameter F (fam.P P) → AdelicGroupPoints F G → ℂ)
    (DE : Set (ComplexCharacterParameter F (fam.P P))),
    Set.range (imaginaryParameter F (fam.P P)) ⊆ DE →
    (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) DE) →
    (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hKP.eisensteinSeries φ lam) →
  ∀ {n nT nZ : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (fam.P P))
    (ec : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F (fam.P P))
    (eT : V fam.T ≃ₗ[ℝ] (Fin nT → ℝ))
    (eZ : RealCharacterDual F (fam.P fam.top) ≃ₗ[ℝ] (Fin nZ → ℝ)),
    let ix (x : Fin n → ℝ) : Fin n → ℂ := fun j => (x j : ℂ) * Complex.I
    (∀ x, ec (ix x) = imaginaryParameter F (fam.P P) (e x)) →
    ∃ (R : ℝ) (L : ∀ Q, fam.AffineExponentLabels P Q)
      (expansion : (Fin n → ℝ) → fam.positiveSplitComponent fam.top →
        ∀ Q, fam.UnitaryPairingExpansion Q)
      (ω : V fam.T → fam.positiveSplitComponent fam.top → (Fin n → ℂ) → ℂ)
      (Dω : V fam.T → fam.positiveSplitComponent fam.top → Set (Fin n → ℂ)),
    let generic := {x | ec (ix x) ∈ fam.genericParameterRegion P L}
    0 < R ∧ IsOpen generic ∧ Dense generic ∧
    (∀ x ∈ generic, ∀ Z,
      fam.IsWeakConstantTermPairingExpansion hsmooth hcalc rho hK Z
        (E (ec (ix x))) Φ (expansion x Z) ∧
      ∀ Q, (expansion x Z Q).IsLabelledBy (L Q) (ec (ix x))) ∧
    (∀ T, fam.IsRegularTruncationParameter R T → ∀ Z,
      IsOpen (Dω T Z) ∧ Set.range ix ⊆ Dω T Z ∧ DifferentiableOn ℂ (ω T Z) (Dω T Z) ∧
      ∀ x ∈ generic, ω T Z (ix x) = fam.regularizedPairing vol (expansion x Z) T) ∧
    ∀ δ : ℝ, 0 < δ → ∀ Λ : Set (Fin n → ℝ), Bornology.IsBounded Λ →
      ∃ (B ε : ℝ) (k : ℕ), 0 < B ∧ 0 < ε ∧
      ∀ T, fam.IsRegularTruncationParameter R T →
      (∀ α ∈ simpleRelativeRoots fam.i fam.ν, δ * ‖eT T‖ ≤ eval fam.T α T) →
      ∀ Z, ∀ x ∈ Λ,
        IntegrableOn (fam.truncatedPairingIntegrand Z (E (ec (ix x))) Φ)
          (fam.truncationRegion hK C T₀ T) (normOneRationalQuotientHaarMeasure F G) ∧
        ‖fam.truncatedPairing hK C T₀ T Z (E (ec (ix x))) Φ - ω T Z (ix x)‖ ≤
          B * Real.exp (-ε * ‖eT T‖) *
            (1 + ‖eZ (characterLog F (fam.P fam.top) Z.val)‖ ^ k)

end Langlands.Global

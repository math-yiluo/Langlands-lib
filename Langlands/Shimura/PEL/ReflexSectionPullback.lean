import Langlands.Shimura.PEL.LieDeterminantCondition

/-! # Pullback of the actual reflex determinant coefficients -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

namespace Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

variable {R : CommRingCat.{u}} {S T : AlgebraicGeometry.Scheme.{u}}

/-- Structure constants on sections commute with pullback to any smaller inverse-image open. -/
lemma secHom_comp_appLE (s : S ⟶ Spec R) (f : T ⟶ S) (U : S.Opens)
    (W : T.Opens) (e : W ≤ f ⁻¹ᵁ U) :
    secHom s U ≫ f.appLE U W e = secHom (f ≫ s) W := by
  unfold secHom
  rw [Category.assoc, Scheme.Hom.appLE_comp_appLE]

/-- In particular, the structure constants pull back on the full inverse-image open. -/
lemma secHom_comp_app (s : S ⟶ Spec R) (f : T ⟶ S) (U : S.Opens) :
    secHom s U ≫ f.app U = secHom (f ≫ s) (f ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.appLE_eq_app]
  exact secHom_comp_appLE s f U _ le_rfl

end Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

variable {E K A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
    {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
    (hΦ : IsCMSection E K Φ)
    {S T : AlgebraicGeometry.Scheme.{0}}
    (s : S ⟶ Spec (CommRingCat.of (D.kottwitzCocharacterReflexField C)))
    (f : T ⟶ S) {ι : Type} [Fintype ι]

/-- The actual reflex determinant polynomial pulls back along the actual structure morphism. -/
theorem harrisReflexSectionDeterminant_pullbackLE
    (a : ι → D.harrisHodgePELIntegralOrder C) (U : S.Opens)
    (W : T.Opens) (e : W ≤ f ⁻¹ᵁ U) :
    MvPolynomial.map (f.appLE U W e).hom
        (D.harrisReflexSectionDeterminant C hΦ s a U) =
      D.harrisReflexSectionDeterminant C hΦ (f ≫ s) a W := by
  unfold harrisReflexSectionDeterminant kottwitzReflexDeterminantBaseChange
  rw [MvPolynomial.map_map]
  have hs : (f.appLE U W e).hom.comp (secHom s U).hom =
      (secHom (f ≫ s) W).hom :=
    congrArg (fun g => g.hom) (secHom_comp_appLE s f U W e)
  rw [hs]

/-- Reflex determinant pullback on each full inverse-image open. -/
theorem harrisReflexSectionDeterminant_pullback
    (a : ι → D.harrisHodgePELIntegralOrder C) (U : S.Opens) :
    MvPolynomial.map (f.app U).hom
        (D.harrisReflexSectionDeterminant C hΦ s a U) =
      D.harrisReflexSectionDeterminant C hΦ (f ≫ s) a (f ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.appLE_eq_app]
  exact D.harrisReflexSectionDeterminant_pullbackLE C hΦ s f a U _ le_rfl

/-- Every reflex determinant coefficient pulls back to the actual coefficient on the target. -/
theorem coeff_harrisReflexSectionDeterminant_pullbackLE
    (a : ι → D.harrisHodgePELIntegralOrder C) (U : S.Opens)
    (W : T.Opens) (e : W ≤ f ⁻¹ᵁ U) (d : ι →₀ ℕ) :
    f.appLE U W e ((D.harrisReflexSectionDeterminant C hΦ s a U).coeff d) =
      (D.harrisReflexSectionDeterminant C hΦ (f ≫ s) a W).coeff d := by
  rw [← D.harrisReflexSectionDeterminant_pullbackLE C hΦ s f a U W e]
  exact (MvPolynomial.coeff_map _ _ _).symm

end Langlands.Shimura.CentralSimpleUnitaryData

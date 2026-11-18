import Langlands.GroupScheme.Rational.RealAnisotropicFormStatement
import Langlands.GroupScheme.Rational.RealCompactFormExistenceStatement
import Langlands.GroupScheme.Rational.RealCompactFormUniquenessStatement
import Langlands.GroupScheme.Rational.RealAnisotropicCompactnessStatement
import Langlands.GroupScheme.SimplyConnected.SemisimpleFieldExtensionProof

/-! # Reduction of the real anisotropic-form theorem to compact forms -/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The three independent compact-form inputs to the anisotropic-form theorem. -/
def RealCompactFormInputs : Prop :=
  RealCompactFormExistenceStatement ∧ RealCompactFormUniquenessStatement ∧
    RealAnisotropicCompactnessStatement

/-- These compact-form inputs imply the unchanged real anisotropic-form target. -/
theorem realAnisotropicForm_of_compactFormInputs
    (h : RealCompactFormInputs) : RealAnisotropicFormStatement := by
  rcases h with ⟨hex, huniq, hcompact⟩
  intro G hG
  constructor
  · obtain ⟨H, hH, hc, e⟩ := hex
      ((GroupScheme.baseChange (algebraBaseMap ℝ ℂ)).obj G)
      (isSemisimpleFieldExtension ℝ ℂ G hG)
    let : IsAffineHom H.X.hom := hH.isConnectedReductive.isAffineHom
    let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
    exact ⟨H, hH, isAnisotropic_of_hasCompactRealPoints H hc, e⟩
  · intro G₁ G₂ h₁ h₂ ha₁ ha₂ e₁ e₂
    obtain ⟨e₁⟩ := e₁
    obtain ⟨e₂⟩ := e₂
    exact huniq G₁ G₂ h₁ h₂
      (hcompact G₁ h₁.isConnectedReductive ha₁)
      (hcompact G₂ h₂.isConnectedReductive ha₂)
      ⟨e₁ ≪≫ e₂.symm⟩

end Langlands.GroupScheme

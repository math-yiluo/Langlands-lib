import Langlands.AlgebraicGeometry.FiniteLinearEquationsScheme
import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic

/-! # Local finite linear models for presheaves on a scheme slice -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.FiniteLinearEquations

variable {B : Scheme.{u}}

/-- A finite homogeneous linear model, naturally on the entire scheme slice. -/
def HasModel {R : CommRingCat.{u}} (F : AlgebraicSpace.Presheaf (Spec R)) : Prop :=
  ∃ (m n : ℕ) (a : Fin m → Fin n → R), Nonempty (F ≅ solutionsPresheaf a)

/-- Finite homogeneous linear models on an open cover by actual spectra. -/
def HasLocalModels (F : AlgebraicSpace.Presheaf B) : Prop :=
  ∃ (I : Type u) (R : I → CommRingCat.{u}) (j : ∀ i, Spec (R i) ⟶ B),
    (∀ i, IsOpenImmersion (j i)) ∧
    (∀ b : B, ∃ i, ∃ x : Spec (R i), (j i).base x = b) ∧
    ∀ i, HasModel ((Over.map (j i)).op ⋙ F)

namespace HasModel

/-- A natural isomorphism transports the entire linear model. -/
lemma of_iso {R : CommRingCat.{u}} {F G : AlgebraicSpace.Presheaf (Spec R)}
    (hF : HasModel F) (e : F ≅ G) : HasModel G := by
  obtain ⟨m, n, a, ⟨eF⟩⟩ := hF
  exact ⟨m, n, a, ⟨e.symm ≪≫ eF⟩⟩

/-- Every finite linear model gives an actual affine finitely presented representer. -/
theorem exists_representation {R : CommRingCat.{u}}
    {F : AlgebraicSpace.Presheaf (Spec R)} (hF : HasModel F) :
    ∃ H : Over (Spec R),
      Nonempty ((AlgebraicSpace.schemeYoneda (Spec R)).obj H ≅ F) ∧
      IsAffineHom H.hom ∧ LocallyOfFinitePresentation H.hom := by
  obtain ⟨m, n, a, ⟨e⟩⟩ := hF
  exact ⟨equationsScheme a, ⟨solutionsPresheafIso a ≪≫ e.symm⟩,
    inferInstance, inferInstance⟩

end HasModel

/-- The explicit finite solution presheaves themselves have finite linear models. -/
lemma hasModel_solutionsPresheaf {R : CommRingCat.{u}} {m n : ℕ}
    (a : Fin m → Fin n → R) : HasModel (solutionsPresheaf a) :=
  ⟨m, n, a, ⟨Iso.refl _⟩⟩

namespace HasLocalModels

/-- Transport local models through a natural isomorphism on the full slice. -/
lemma of_iso {F G : AlgebraicSpace.Presheaf B} (hF : HasLocalModels F) (e : F ≅ G) :
    HasLocalModels G := by
  obtain ⟨I, R, j, hj, hcover, hmodel⟩ := hF
  exact ⟨I, R, j, hj, hcover,
    fun i ↦ (hmodel i).of_iso (Functor.isoWhiskerLeft (Over.map (j i)).op e)⟩

/-- On every model chart the restricted presheaf has an actual affine finitely
presented scheme representer. Global descent is a separate obligation. -/
theorem exists_local_representations {F : AlgebraicSpace.Presheaf B}
    (hF : HasLocalModels F) :
    ∃ (I : Type u) (R : I → CommRingCat.{u}) (j : ∀ i, Spec (R i) ⟶ B),
      (∀ i, IsOpenImmersion (j i)) ∧
      (∀ b : B, ∃ i, ∃ x : Spec (R i), (j i).base x = b) ∧
      ∀ i, ∃ H : Over (Spec (R i)),
        Nonempty ((AlgebraicSpace.schemeYoneda (Spec (R i))).obj H ≅
          (Over.map (j i)).op ⋙ F) ∧
        IsAffineHom H.hom ∧ LocallyOfFinitePresentation H.hom := by
  obtain ⟨I, R, j, hj, hcover, hmodel⟩ := hF
  exact ⟨I, R, j, hj, hcover, fun i ↦ (hmodel i).exists_representation⟩

end HasLocalModels

end Langlands.AlgebraicGeometry.FiniteLinearEquations

import Langlands.GroupScheme.Dynamic.AdjointDeterminantFunctorialityStatement

/-! # Proof of functoriality of the actual adjoint determinant -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace MatrixRepresentation

variable {R : CommRingCat.{u}} {H : GroupScheme (Spec R)} [IsAffine H.X.left]
  {n : Type} [Fintype n] [DecidableEq n]

/-- On an affine group scheme, a matrix representation is determined by its
matrices on all affine test points. -/
theorem ext_affineMatrix {ρ₁ ρ₂ : MatrixRepresentation H n}
    (h : ∀ (A : CommAlgCat.{u} R) (x : H.affinePoints A),
      ρ₁.affineMatrix A x = ρ₂.affineMatrix A x) :
    ρ₁ = ρ₂ := by
  let e := AffineCoordinates.groupSchemeIso H
  have hx : e.hom.hom.hom ≫ ρ₁.hom.hom = e.hom.hom.hom ≫ ρ₂.hom.hom :=
    (GeneralLinear.affinePointsEquiv n R _).injective (h _ e.hom.hom.hom)
  have key : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 H.X := by
    rw [← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom]
  apply Grp.hom_ext
  calc ρ₁.hom.hom = (e.inv.hom.hom ≫ e.hom.hom.hom) ≫ ρ₁.hom.hom := by
        rw [key, Category.id_comp]
    _ = e.inv.hom.hom ≫ (e.hom.hom.hom ≫ ρ₂.hom.hom) := by
        rw [Category.assoc, hx]
    _ = ρ₂.hom.hom := by
        rw [← Category.assoc, key, Category.id_comp]

end MatrixRepresentation

namespace AutomorphicAction

variable {R : CommRingCat.{u}} {H P U : GroupScheme (Spec R)}
  [IsAffineHom U.X.hom] (a : AutomorphicAction P U) {d : ℕ}
  (c : Lie.FiniteCoordinates U d) (j : H ⟶ P)

/-- Restricting the action restricts its coordinate differential. -/
theorem coordinateAction_restrict (A : CommAlgCat.{u} R) (h : H.affinePoints A) :
    (a.restrict j).coordinateAction c A h = a.coordinateAction c A (h ≫ j.hom.hom) := by
  apply LinearEquiv.ext
  intro v
  change c.equiv A ((a.restrict j).differential h ((c.equiv A).symm v)) =
    c.equiv A (a.differential (h ≫ j.hom.hom) ((c.equiv A).symm v))
  rw [differential_restrict]

/-- Restricting the action restricts its coordinate matrices. -/
theorem coordinateMatrix_restrict (A : CommAlgCat.{u} R) (h : H.affinePoints A) :
    (a.restrict j).coordinateMatrix c A h = a.coordinateMatrix c A (h ≫ j.hom.hom) := by
  unfold coordinateMatrix
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, coordinateAction_restrict]

variable [IsAffine H.X.left] [IsAffine P.X.left]

/-- The finite representation of the restricted action is the restricted representation. -/
theorem finiteRepresentation_restrict :
    (a.restrict j).finiteRepresentation c = j ≫ a.finiteRepresentation c := by
  apply MatrixRepresentation.ext_affineMatrix
  intro A h
  rw [finiteRepresentation_affineMatrix, coordinateMatrix_restrict,
    MatrixRepresentation.affineMatrix_apply, Grp.comp_hom_hom, ← Category.assoc,
    ← MatrixRepresentation.affineMatrix_apply, finiteRepresentation_affineMatrix]

/-- Restricting the determinant character gives the determinant character of the
restricted action. -/
theorem determinantCharacter_restrict :
    characterRestrict j (a.determinantCharacter c) =
      (a.restrict j).determinantCharacter c := by
  rw [determinantCharacter, determinantCharacter, finiteRepresentation_restrict,
    characterRestrict_comp]
  rfl

end AutomorphicAction

/-- Coefficient change and restriction of the actual action preserve the
constructed differential and algebraic determinant character. -/
theorem dynamicAdjointDeterminantFunctoriality :
    DynamicAdjointDeterminantFunctorialityStatement.{u} := by
  intro R G P U χ iP iU hP hU _ _ d c a δ
  refine ⟨fun A B f p x => a.differential_naturality f.hom p x,
    fun A B f p => a.differential_det_naturality c f p,
    fun A B f p => ?_, fun H _ j => ?_⟩
  · exact (Dynamic.adjointDeterminantCharacter_affinePoints hP hU c B
        (P.affinePointMap f p)).trans
      ((a.differential_det_naturality c f p).trans
        (congrArg (Units.map f.hom.toRingHom.toMonoidHom)
          (Dynamic.adjointDeterminantCharacter_affinePoints hP hU c A p).symm))
  · exact ⟨a.determinantCharacter_restrict c j,
      fun A h => a.differential_restrict j h⟩

end Langlands.GroupScheme

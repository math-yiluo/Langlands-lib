import Langlands.Global.AdelicIwasawaOrbitHeight
import Langlands.GroupScheme.Dynamic.AdjointDeterminantLine
import Langlands.GroupScheme.MatrixRepresentation.Reindex

/-! # Adelic height bounds for the actual dynamic determinant -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G Q U : GroupScheme (Spec (CommRingCat.of F))}
  {ζ : (GroupScheme.Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
  {q : Q ⟶ G} {iU : U ⟶ G}
  [IsAffineHom G.X.hom] [IsAffineHom U.X.hom]
  {N : ℕ} (cG : Lie.FiniteCoordinates G N)

/-- Enumerate the exterior matrix coordinates in a finite initial segment. -/
def adjointExteriorFinRepresentation (d : ℕ) :
    MatrixRepresentation G (Fin (Fintype.card (Set.powersetCard (Fin N) d))) :=
  (Dynamic.adjointExteriorRepresentation cG (d := d)).reindex
    (Fintype.equivFin (Set.powersetCard (Fin N) d))

variable [IsAffine G.X.left] [IsAffine Q.X.left] [IsClosedImmersion q.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} {d : ℕ} (cU : Lie.FiniteCoordinates U d)

include cG in
/-- The Iwasawa height at the actual dynamic parabolic determinant character is
bounded above on principal rational points. -/
theorem exists_height_adjointDeterminant_le (hK : IsIwasawaCompact q K)
    (hQ : (Dynamic.parabolic ζ).IsRepresentedBy q)
    (hU : (Dynamic.unipotent ζ).IsRepresentedBy iU) :
    ∃ D : ℝ, ∀ x : RationalGroupPoints F G,
      hK.height (rational F G x) (Dynamic.adjointDeterminantCharacter hQ hU cU) ≤ D := by
  let := hU.1
  let I := Set.powersetCard (Fin N) d
  let e := Fintype.equivFin I
  let ρ := adjointExteriorFinRepresentation cG d
  let w : I → F := Dynamic.adjointExteriorCoordinates cG cU iU (CommAlgCat.of F F)
  let v : Fin (Fintype.card I) → F := w ∘ e.symm
  have hw : w ≠ 0 := Dynamic.adjointExteriorCoordinates_ne_zero cG cU _ (Field.toIsField F)
  have hv : v ≠ 0 := by
    intro hv
    apply hw
    funext i
    have hi := congrFun hv (e i)
    simpa only [v, Function.comp_apply, e.symm_apply_apply, Pi.zero_apply] using hi
  let χ := Dynamic.adjointDeterminantCharacter hQ hU cU
  have ha (y : AdelicGroupPoints F Q) :
      (adelicMatrix F G ρ (map F Q G q y)).val *ᵥ PrimitiveAdelicHeight.rational F _ v =
        (character F Q χ.toMul y).val • PrimitiveAdelicHeight.rational F _ v := by
    let B := CommAlgCat.of F (Adeles F)
    let ρ₀ := Dynamic.adjointExteriorRepresentation cG (d := d)
    let wB := Dynamic.adjointExteriorCoordinates cG cU iU B
    have hW : PrimitiveAdelicHeight.rational F _ v = wB ∘ e.symm := by
      funext i
      have hi := congrFun (Dynamic.adjointExteriorCoordinates_naturality cG cU
        (iU := iU) (CommAlgCat.ofHom (Algebra.ofId F (Adeles F)))) (e.symm i)
      exact hi.symm
    have hact : (ρ₀.affineMatrix B (y ≫ q.hom.hom)).val *ᵥ wB =
        (character F Q χ.toMul y).val • wB := by
      rw [← MatrixRepresentation.affineAction_apply]
      exact Dynamic.adjointExteriorCoordinates_character_action hQ hU cG cU B y
    change ((ρ₀.reindex e).affineMatrix B (y ≫ q.hom.hom)).val *ᵥ
      PrimitiveAdelicHeight.rational F _ v = _
    rw [hW, MatrixRepresentation.reindex_affineMatrix, MatrixRepresentation.reindexGL_val,
      Matrix.submatrix_mulVec_equiv]
    rw [show (wB ∘ e.symm) ∘ e.symm.symm = wB by funext i; simp [Function.comp_def], hact]
    rfl
  obtain ⟨D, hD⟩ := exists_height_le_sub_log_mulHeight ρ hv hK χ ha
  exact ⟨D, fun x => (hD x).trans (sub_le_self _ (Projectivization.logHeight_nonneg _))⟩

end Langlands.Global.RepresentationGrowth

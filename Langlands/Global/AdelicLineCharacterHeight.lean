import Langlands.Global.AdelicOrbitHeightMinimum
import Langlands.Global.AdelicGroupNormOne
import Langlands.Global.AdelicGroupNormOneFunctorial
import Langlands.GroupScheme.MatrixRepresentation.CoordinateLineCharacter

/-! # Exact height scaling by an actual stabilized-line character -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix NNReal

namespace Langlands.GroupScheme.MatrixRepresentation

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The affine coordinate-line action is the actual affine evaluation of the
algebraic character constructed from its all-test unit-scalar action. -/
theorem affine_coordinateLineCharacter_action (ρ : MatrixRepresentation G n)
    (j : n) (hline : ρ.PreservesCoordinateLine j)
    (A : CommAlgCat.{u} R) (x : (algSpec R).obj (op A) ⟶ G.X) :
    (ρ.affineMatrix A x : Matrix n n A) *ᵥ Pi.single j 1 =
      (Gm.affineUnitsEquiv R A (x ≫ (ρ.coordinateLineCharacter j hline).hom.hom) : A) •
        (Pi.single j 1 : n → A) := by
  let e := Corepresented.affineSectionsAlgEquiv A
  have hM (i l : n) :
      (ρ.pointMatrix ((algSpec R).obj (op A)) x) i l =
        e.symm ((ρ.affineMatrix A x) i l) := by
    rw [pointMatrix_eq_affineMatrix]
    rfl
  have hu :
      (Gm.affineUnitsEquiv R A (x ≫ (ρ.coordinateLineCharacter j hline).hom.hom) : A) =
        e (ρ.coordinateLineScalar j hline ((algSpec R).obj (op A)) x :
          Γ(((algSpec R).obj (op A)).left, ⊤)) := by
    rw [← coordinateLineCharacter_scalar]
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom _ = e _
    rw [← Corepresented.affineSectionsIso_hom_ringHom A]
    rfl
  have ha := ρ.coordinateLineScalar_spec j hline ((algSpec R).obj (op A)) x
  funext i
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, smul_eq_mul]
  rw [hu]
  have hi := congrArg e (congrFun ha i)
  simp only [Matrix.mulVec_single_one, Matrix.col_apply,
    Pi.smul_apply, smul_eq_mul] at hi
  rw [hM, e.apply_symm_apply, map_mul] at hi
  have hs : e ((Pi.single j 1 : n → Γ(((algSpec R).obj (op A)).left, ⊤)) i) =
      (Pi.single j 1 : n → A) i := by
    by_cases hij : i = j <;> simp [hij]
  rw [hs] at hi
  exact hi

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) {n : ℕ}

/-- The normalized adelic norm of the actual algebraic character on a preserved
coordinate line after restriction to a specified subgroup scheme. -/
def lineCharacterNorm (H : GroupScheme (Spec (CommRingCat.of F))) (z : H ⟶ G)
    (ρ : MatrixRepresentation G (Fin n)) (j : Fin n)
    (hline : (ρ.restrict z).PreservesCoordinateLine j) :
    AdelicGroupPoints F H →ₜ* ℝ≥0ˣ :=
  characterNorm F H ((ρ.restrict z).coordinateLineCharacter j hline)

/-- Right multiplication scales an actual representation-vector height by the
normalized idele norm when that point scales the vector by the specified idele. -/
theorem orbitHeight_mul_eq_of_idele_scalar
    (ρ : MatrixRepresentation G (Fin n)) (v : Fin n → F) (hv : v ≠ 0)
    (g h : AdelicGroupPoints F G) (t : Ideles F)
    (ha : (adelicMatrix F G ρ h).val *ᵥ PrimitiveAdelicHeight.rational F n v =
      t.val • PrimitiveAdelicHeight.rational F n v) :
    orbitHeight F G ρ v (g * h) =
      ((IdeleAbsoluteValue.full F t : ℝ≥0) : ℝ) * orbitHeight F G ρ v g := by
  have hx : PrimitiveAdelicHeight.IsPrimitive F n
      ((adelicMatrix F G ρ g).val *ᵥ PrimitiveAdelicHeight.rational F n v) :=
    ⟨adelicMatrix F G ρ g, v, hv, rfl⟩
  simp only [orbitHeight, PrimitiveAdelicHeight.rationalHeight, map_mul, Units.val_mul,
    ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_smul]
  exact hx.height_smul F n t

/-- On the selected coordinate vector, right translation by an actual subgroup
point scales the height by the exact normalized norm of its line character. -/
theorem orbitHeight_mul_map_eq_lineCharacterNorm
    (H : GroupScheme (Spec (CommRingCat.of F))) (z : H ⟶ G)
    (ρ : MatrixRepresentation G (Fin n)) (j : Fin n)
    (hline : (ρ.restrict z).PreservesCoordinateLine j)
    (g : AdelicGroupPoints F G) (p : AdelicGroupPoints F H) :
    orbitHeight F G ρ (Pi.single j 1) (g * map F H G z p) =
      ((lineCharacterNorm F G H z ρ j hline p : ℝ≥0) : ℝ) *
        orbitHeight F G ρ (Pi.single j 1) g := by
  have hv : (Pi.single j 1 : Fin n → F) ≠ 0 := by
    intro h
    have hj := congrFun h j
    simp at hj
  have hrat : PrimitiveAdelicHeight.rational F n (Pi.single j 1) =
      (Pi.single j 1 : Fin n → Adeles F) := by
    funext l
    by_cases hlj : l = j <;> simp [PrimitiveAdelicHeight.rational, hlj]
  apply orbitHeight_mul_eq_of_idele_scalar F G ρ (Pi.single j 1) hv g
    (map F H G z p)
    (character F H ((ρ.restrict z).coordinateLineCharacter j hline) p)
  rw [hrat]
  exact (ρ.restrict z).affine_coordinateLineCharacter_action j hline
    (CommAlgCat.of F (Adeles F)) p

/-- The subgroup's actual character-norm-one condition makes its preserved
coordinate-line height invariant under right translation. -/
theorem orbitHeight_mul_map_normOne
    (H : GroupScheme (Spec (CommRingCat.of F))) (z : H ⟶ G)
    (ρ : MatrixRepresentation G (Fin n)) (j : Fin n)
    (hline : (ρ.restrict z).PreservesCoordinateLine j)
    (g : AdelicGroupPoints F G) (p : normOneSubgroup F H) :
    orbitHeight F G ρ (Pi.single j 1) (g * map F H G z p) =
      orbitHeight F G ρ (Pi.single j 1) g := by
  have hnorm : lineCharacterNorm F G H z ρ j hline p = 1 :=
    (mem_normOneSubgroup F H p).1 p.property
      ((ρ.restrict z).coordinateLineCharacter j hline)
  rw [orbitHeight_mul_map_eq_lineCharacterNorm F G H z ρ j hline, hnorm]
  simp

/-- A height comparison against a translate in the line stabilizer is exactly
the corresponding lower bound on the normalized algebraic line character. -/
theorem orbitHeight_le_mul_map_iff
    (H : GroupScheme (Spec (CommRingCat.of F))) (z : H ⟶ G)
    (ρ : MatrixRepresentation G (Fin n)) (j : Fin n)
    (hline : (ρ.restrict z).PreservesCoordinateLine j)
    (g : AdelicGroupPoints F G) (p : AdelicGroupPoints F H) (c : ℝ) :
    orbitHeight F G ρ (Pi.single j 1) g ≤
        c * orbitHeight F G ρ (Pi.single j 1) (g * map F H G z p) ↔
      1 ≤ c * ((lineCharacterNorm F G H z ρ j hline p : ℝ≥0) : ℝ) := by
  have hv : (Pi.single j 1 : Fin n → F) ≠ 0 := by
    intro h
    have hj := congrFun h j
    simp at hj
  have hp := orbitHeight_pos F G ρ hv g
  rw [orbitHeight_mul_map_eq_lineCharacterNorm F G H z ρ j hline, ← mul_assoc]
  simpa only [one_mul] using (mul_le_mul_iff_left₀ hp :
    1 * orbitHeight F G ρ (Pi.single j 1) g ≤
        (c * ((lineCharacterNorm F G H z ρ j hline p : ℝ≥0) : ℝ)) *
          orbitHeight F G ρ (Pi.single j 1) g ↔
      1 ≤ c * ((lineCharacterNorm F G H z ρ j hline p : ℝ≥0) : ℝ))

end Langlands.Global.RepresentationGrowth

import Langlands.GroupScheme.MatrixRepresentation.CoordinateLineCocharacterDiagonalization
import Langlands.GroupScheme.MatrixRepresentation.ParabolicEigenlinePositivity
import Langlands.GroupScheme.MatrixRepresentationConjugate
import Langlands.GroupScheme.Dynamic.ParabolicCharacters

/-! # Positive actual line-character integers without a chosen diagonal basis -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G H U P : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The selected basis column is exactly the original coordinate vector. -/
def IsCoordinateLineBasis (B : GL n k) (a j : n) : Prop :=
  (B : Matrix n n k).col a = Pi.single j 1

/-- The representation in the basis whose columns are B. -/
def basisConjugate (ρ : MatrixRepresentation G n) (B : GL n k) :
    MatrixRepresentation G n :=
  ρ.conjugate (GeneralLinear.CocharacterDiagonal.rationalMatrixPoint B⁻¹)

private theorem standard_rationalMatrix_rationalMatrixPoint (B : GL n k) :
    (standard n (CommRingCat.of k)).rationalMatrix
      (GeneralLinear.CocharacterDiagonal.rationalMatrixPoint B) = B := by
  have h := (standard n (CommRingCat.of k)).affineMatrix_constantPoint
    (GeneralLinear.CocharacterDiagonal.rationalMatrixPoint B) (CommAlgCat.of k k)
  rw [standard_affineMatrix,
    GeneralLinear.CocharacterDiagonal.affinePointsEquiv_constant_rationalMatrixPoint] at h
  apply Units.ext
  ext a b
  have he := congrArg (fun M : GL n k => (M : Matrix n n k) a b) h
  exact he.symm

theorem basisConjugate_pointMatrix (ρ : MatrixRepresentation G n) (B : GL n k)
    (Z : Over (Spec (CommRingCat.of k))) (g : Z ⟶ G.X) :
    (ρ.basisConjugate B).pointMatrix Z g =
      (Matrix.GeneralLinearGroup.map (scalarMap Z) B)⁻¹ * ρ.pointMatrix Z g *
        Matrix.GeneralLinearGroup.map (scalarMap Z) B := by
  have hc := (standard n (CommRingCat.of k)).pointMatrix_constantPoint
    (GeneralLinear.CocharacterDiagonal.rationalMatrixPoint B⁻¹) Z
  rw [standard_rationalMatrix_rationalMatrixPoint] at hc
  change GeneralLinear.pointsEquiv n (CommRingCat.of k) Z
    ((GeneralLinear.groupScheme n (CommRingCat.of k)).constantPoint
      (GeneralLinear.CocharacterDiagonal.rationalMatrixPoint B⁻¹) Z) =
        Matrix.GeneralLinearGroup.map (scalarMap Z) B⁻¹ at hc
  rw [basisConjugate, conjugate_pointMatrix, hc, map_inv, inv_inv]

/-- The same scalar acts on the selected coordinate before and after the
adapted change of basis, on every scheme test. -/
theorem basisConjugate_coordinateScalar_iff
    (ρ : MatrixRepresentation G n) (B : GL n k) (a j : n)
    (hB : IsCoordinateLineBasis B a j)
    (Z : Over (Spec (CommRingCat.of k))) (g : Z ⟶ G.X) (c : Γ(Z.left, ⊤)) :
    ((ρ.basisConjugate B).pointMatrix Z g : Matrix n n Γ(Z.left, ⊤)) *ᵥ Pi.single a 1 =
        c • (Pi.single a 1 : n → Γ(Z.left, ⊤)) ↔
      (ρ.pointMatrix Z g : Matrix n n Γ(Z.left, ⊤)) *ᵥ Pi.single j 1 =
        c • (Pi.single j 1 : n → Γ(Z.left, ⊤)) := by
  let C := Matrix.GeneralLinearGroup.map (scalarMap Z) B
  have hvec : (C : Matrix n n Γ(Z.left, ⊤)) *ᵥ Pi.single a 1 =
      (Pi.single j 1 : n → Γ(Z.left, ⊤)) := by
    ext b
    simp only [Matrix.mulVec_single_one, Matrix.col_apply,
      C, Matrix.GeneralLinearGroup.map_apply]
    have hb := congrFun hB b
    change (scalarMap Z) ((B : Matrix n n k) b a) = _
    change (B : Matrix n n k) b a = ((Pi.single j (1 : k)) : n → k) b at hb
    rw [hb]
    by_cases hb : b = j <;> simp [hb]
  have hmul : C * (C⁻¹ * ρ.pointMatrix Z g * C) = ρ.pointMatrix Z g * C := by group
  have hact :
      (C : Matrix n n Γ(Z.left, ⊤)) *ᵥ
        (((ρ.basisConjugate B).pointMatrix Z g : Matrix n n Γ(Z.left, ⊤)) *ᵥ
          Pi.single a 1) =
      (ρ.pointMatrix Z g : Matrix n n Γ(Z.left, ⊤)) *ᵥ Pi.single j 1 := by
    rw [basisConjugate_pointMatrix, Matrix.mulVec_mulVec, ← Units.val_mul, hmul,
      Units.val_mul, ← Matrix.mulVec_mulVec, hvec]
  have hscalar : (C : Matrix n n Γ(Z.left, ⊤)) *ᵥ
      (c • (Pi.single a 1 : n → Γ(Z.left, ⊤))) =
        c • (Pi.single j 1 : n → Γ(Z.left, ⊤)) := by
    rw [Matrix.mulVec_smul, hvec]
  constructor
  · intro h
    have he := congrArg (fun v => (C : Matrix n n Γ(Z.left, ⊤)) *ᵥ v) h
    rwa [hact, hscalar] at he
  · intro h
    apply Matrix.mulVec_injective_of_isUnit (Units.isUnit C)
    rw [hact, hscalar]
    exact h

/-- The adapted coordinate change preserves and reflects all-test line preservation. -/
theorem basisConjugate_preservesCoordinateLine_iff
    (ρ : MatrixRepresentation G n) (B : GL n k) (a j : n)
    (hB : IsCoordinateLineBasis B a j) :
    (ρ.basisConjugate B).PreservesCoordinateLine a ↔ ρ.PreservesCoordinateLine j := by
  constructor
  · intro h Z g
    obtain ⟨c, hc⟩ := h Z g
    exact ⟨c, (ρ.basisConjugate_coordinateScalar_iff B a j hB Z g c).mp hc⟩
  · intro h Z g
    obtain ⟨c, hc⟩ := h Z g
    exact ⟨c, (ρ.basisConjugate_coordinateScalar_iff B a j hB Z g c).mpr hc⟩

/-- A parabolic coordinate eigenline is a coordinate eigenline for its defining
cocharacter, because that cocharacter actually factors through the parabolic. -/
theorem preservesCoordinateLine_cocharacter_of_parabolic
    (ρ : MatrixRepresentation G n)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (iP : P ⟶ G)
    (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
    (j : n) (hline : (ρ.restrict iP).PreservesCoordinateLine j) :
    (ρ.restrict χ).PreservesCoordinateLine j := by
  intro Z x
  obtain ⟨c, hc⟩ := hline Z (x ≫ (Dynamic.cocharacterToParabolic hP).hom.hom)
  refine ⟨c, ?_⟩
  simpa only [pointMatrix_restrict, Category.assoc, ← Grp.comp_hom_hom,
    Dynamic.cocharacterToParabolic_comp hP] using hc

/-- A reversible cocharacter has strictly positive actual line-character integer
on a proper parabolic coordinate eigenline, without a diagonal-basis premise. -/
theorem coordinateLineCocharacterWeight_pos_of_proper_parabolic_eigenline
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (ρ : MatrixRepresentation G n)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (iU : U ⟶ G) (iP : P ⟶ G)
    (hU : (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).IsRepresentedBy iU)
    (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
    (j : n) (hline : ρ.HasProperParabolicEigenline iP j)
    (hχline : (ρ.restrict χ).PreservesCoordinateLine j)
    {s : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hs : ReversesCocharacter χ s) :
    0 < (ρ.restrict χ).coordinateLineCocharacterWeight j hχline := by
  obtain ⟨B, e, a, hB, he, hdiag⟩ :=
    (ρ.restrict χ).exists_diagonalization_retaining_coordinateLine j hχline
  have hPline : ((ρ.basisConjugate B).restrict iP).PreservesCoordinateLine a := by
    change ((ρ.restrict iP).conjugate
      (GeneralLinear.CocharacterDiagonal.rationalMatrixPoint B⁻¹)).PreservesCoordinateLine a
    exact ((ρ.restrict iP).basisConjugate_preservesCoordinateLine_iff B a j hB).mpr hline.1
  have hproper : ¬(ρ.basisConjugate B).PreservesCoordinateLine a := by
    intro h
    exact hline.2 ((ρ.basisConjugate_preservesCoordinateLine_iff B a j hB).mp h)
  have hd : χ ≫ ρ.basisConjugate B =
      GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e := by
    exact (Category.assoc χ ρ _).symm.trans hdiag
  have hpos := (ρ.basisConjugate B).weight_pos_of_proper_parabolic_eigenline_of_reversesCocharacter
    χ iU iP hU hP e hd a ⟨hPline, hproper⟩ hs
  rwa [he] at hpos

end Langlands.GroupScheme.MatrixRepresentation

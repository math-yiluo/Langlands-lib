import Langlands.Shimura.Unitary.ComplexAffineMatrices
import Langlands.Shimura.Unitary.GaloisCocharacterPoints

set_option maxHeartbeats 20000
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj TensorProduct Classical

namespace Langlands.GroupScheme.Gm
universe u
variable (R T : Type u) [CommRing R] [CommRing T] [Algebra R T]

/-- The unit point on the actual relative affine test scheme. -/
def relativeAffineUnitPoint (u : Tˣ) :
    (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R T)) ⟶
      (Gm (Spec (CommRingCat.of R))).X :=
  (affinePointsEquiv (Spec.map (CommRingCat.ofHom (algebraMap R T)))).symm u

/-- The relative section normalization sends this point's global unit to its input. -/
theorem relativeAffineUnitPoint_sections (u : Tˣ) :
    Corepresented.affineSectionsAlgEquiv (R := CommRingCat.of R) (CommAlgCat.of R T)
      (pointsEquiv _ ((algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R T)))
        (relativeAffineUnitPoint R T u)).val = (u : T) := by
  have h := congrArg (fun v : Tˣ => (v : T))
    ((affinePointsEquiv (Spec.map (CommRingCat.ofHom (algebraMap R T)))).apply_symm_apply u)
  rw [affinePointsEquiv_val] at h
  exact (congrArg (fun f : Γ(Spec (CommRingCat.of T), ⊤) →+* T =>
      f (pointsEquiv _ _ (relativeAffineUnitPoint R T u)).val)
    (Corepresented.affineSectionsIso_hom_ringHom (R := CommRingCat.of R)
      (CommAlgCat.of R T))).trans h


end Langlands.GroupScheme.Gm

namespace Langlands.Shimura.ComplexMatrix

/-- Entrywise coefficient change preserves the ordered split diagonal matrices. -/
theorem splitDiagonal_map {S T : Type*} [CommRing S] [CommRing T]
    (f : S →+* T) (n r : ℕ) (p : S × S) :
    ((splitDiagonal S n r p).1.map f, (splitDiagonal S n r p).2.map f) =
      splitDiagonal T n r (f p.1, f p.2) := by
  apply Prod.ext <;> ext i j <;>
    simp only [splitDiagonal, Matrix.map_apply, Matrix.diagonal_apply] <;>
    split_ifs <;> simp_all

end Langlands.Shimura.ComplexMatrix

namespace Langlands.Shimura.CentralSimpleUnitaryData
variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (T : Type) [CommRing T] [Algebra ℂ T]

/-- Evaluate a complex Harris-group cocharacter on a unit of an affine complex algebra. -/
def complexAffineCocharacterValue
    (χ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme)
    (u : Tˣ) :
    (algSpec (CommRingCat.of ℂ)).obj (op (CommAlgCat.of ℂ T)) ⟶
      D.complexRationalGroupScheme.X :=
  GroupScheme.Gm.relativeAffineUnitPoint ℂ T u ≫ χ.hom.hom

variable [Algebra ℝ T] [IsScalarTower ℝ ℂ T]

set_option backward.isDefEq.respectTransparency false in
/-- The actual Harris cocharacter has its corrected diagonal matrices in affine coordinates. -/
theorem harrisCocharacter_affine_matrices (first : Bool) (u : Tˣ) (τ : E →+* ℝ) :
    D.complexAffinePointMatrices C T
        (D.complexAffineCocharacterValue T (D.harrisCocharacter C first) u) τ =
      ComplexMatrix.splitDiagonal T n (if τ = C.distinguished then n - 1 else n)
        (if first then ((u : T), 1) else (1, (u : T))) := by
  rw [D.complexAffinePointMatrices_sections, complexAffineCocharacterValue,
    D.harrisCocharacter_matrices]
  refine (ComplexMatrix.splitDiagonal_map
    (GroupScheme.Corepresented.affineSectionsAlgEquiv (R := CommRingCat.of ℂ)
      (CommAlgCat.of ℂ T)).toRingEquiv.toRingHom n
    (if τ = C.distinguished then n - 1 else n) _).trans ?_
  have h := GroupScheme.Gm.relativeAffineUnitPoint_sections ℂ T u
  cases first <;> congr 1 <;> apply Prod.ext <;> first | exact h | exact map_one _


end Langlands.Shimura.CentralSimpleUnitaryData

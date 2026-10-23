import Langlands.Shimura.Unitary.ComplexGroupPoints
import Langlands.Shimura.Unitary.ComplexKottwitzMatrices

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra Module
open scoped CategoryTheory.MonObj Classical
attribute [local instance 1100] Algebra.toModule

namespace Langlands.Shimura.ComplexMatrix

variable (S : Type*) [CommRing S] (n : ℕ) (I : Type*) (distinguished : I)

/-- The full split point for the Kottwitz cocharacter, including its scalar multiplier. -/
def kottwitzSplitPoint (first : Bool) (u : Sˣ) :
    (I → (Matrix (Fin n) (Fin n) S)ˣ) × Sˣ :=
  (fun τ => (MulEquiv.prodUnits (splitDiagonalUnits S n
    (if τ = distinguished then n - 1 else n)
      (if first then (1, u⁻¹) else (u⁻¹, 1)))).1, u⁻¹)

/-- The split matrix component is the first diagonal matrix in the ordered pair. -/
theorem kottwitzSplitPoint_matrix (first : Bool) (u : Sˣ) (τ : I) :
    ((kottwitzSplitPoint S n I distinguished first u).1 τ : Matrix (Fin n) (Fin n) S) =
      (splitDiagonal S n (if τ = distinguished then n - 1 else n)
        (if first then (1, ↑(u⁻¹)) else (↑(u⁻¹), 1))).1 := by
  change (splitDiagonalUnits S n _ (if first then (1, u⁻¹) else (u⁻¹, 1))).val.1 = _
  rw [splitDiagonalUnits_val]
  cases first <;> rfl

@[simp] theorem kottwitzSplitPoint_multiplier (first : Bool) (u : Sˣ) :
    (kottwitzSplitPoint S n I distinguished first u).2 = u⁻¹ := rfl

end Langlands.Shimura.ComplexMatrix

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

set_option backward.isDefEq.respectTransparency false in
/-- The multiplier of the actual Kottwitz cocharacter is the inverse scalar unit. -/
theorem kottwitzCocharacter_split_multiplier (first : Bool)
    (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).X) :
    (D.complexGroupPointsEquiv C T
      (x ≫ (D.kottwitzCocharacter C first).hom.hom)).2 =
        (GroupScheme.Gm.pointsEquiv _ T x)⁻¹ := by
  rw [D.complexGroupPointsEquiv_multiplier, Category.assoc, ← Grp.comp_hom_hom,
    D.kottwitzCocharacter_comparison]
  exact (D.realComplexHom C).conj.inverseCocharacter_multiplier
    (D.rationalBasis.baseChange ℝ) first T x

set_option backward.isDefEq.respectTransparency false in
/-- Both matrix units and the multiplier of the actual Kottwitz point have the split formula. -/
theorem kottwitzCocharacter_split_points (first : Bool)
    (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).X) :
    D.complexGroupPointsEquiv C T
      (x ≫ (D.kottwitzCocharacter C first).hom.hom) =
        ComplexMatrix.kottwitzSplitPoint (AlgebraInvolution.complexTestAlgebra T)
          n (E →+* ℝ) C.distinguished first (GroupScheme.Gm.pointsEquiv _ T x) := by
  apply Prod.ext
  · funext τ
    apply Units.ext
    rw [D.complexGroupPointsEquiv_matrix, D.kottwitzCocharacter_matrices,
      ComplexMatrix.kottwitzSplitPoint_matrix]
  · exact D.kottwitzCocharacter_split_multiplier C first T x

set_option backward.isDefEq.respectTransparency false in
/-- The inverse full point equivalence reconstructs the actual cocharacter point. -/
theorem kottwitzCocharacter_points_of_split (first : Bool)
    (T : Over (Spec (CommRingCat.of ℂ)))
    (u : (AlgebraInvolution.complexTestAlgebra T)ˣ) :
    (D.complexGroupPointsEquiv C T).symm
      (ComplexMatrix.kottwitzSplitPoint (AlgebraInvolution.complexTestAlgebra T)
        n (E →+* ℝ) C.distinguished first u) =
      (GroupScheme.Gm.pointsEquiv _ T).symm u ≫
        (D.kottwitzCocharacter C first).hom.hom := by
  apply (D.complexGroupPointsEquiv C T).injective
  rw [MulEquiv.apply_symm_apply, D.kottwitzCocharacter_split_points,
    MulEquiv.apply_symm_apply]

end Langlands.Shimura.CentralSimpleUnitaryData

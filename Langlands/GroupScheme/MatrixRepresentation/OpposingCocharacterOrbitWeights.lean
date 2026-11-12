import Langlands.GroupScheme.MatrixRepresentation.ParabolicEigenlineWeights
import Langlands.GroupScheme.MatrixRepresentation.NormalCharacterSpan
import Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterDiagonal
import Langlands.GroupScheme.Dynamic.OppositeBaseChange

/-! # Two-sided orbit bounds from an actual reversing cocharacter point -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- An actual rational point conjugates a cocharacter to its inverse. -/
def ReversesCocharacter (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) : Prop :=
  χ ≫ (G.innerIso g).hom = Dynamic.oppositeCocharacter χ

/-- The orbit has no coordinates strictly below the negative original weight. -/
def HasOrbitWeightLowerBound (ρ : MatrixRepresentation G n) (e : n → ℤ) (j : n) : Prop :=
  ∀ (Z : Over (Spec (CommRingCat.of k))) (g : Z ⟶ G.X) (a : n),
    e a < -e j → (ρ.pointMatrix Z g : Matrix n n Γ(Z.left, ⊤)) a j = 0

variable (ρ : MatrixRepresentation G n)
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  (e : n → ℤ) (hχ : χ ≫ ρ = GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e)

theorem ReversesCocharacter.inv
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hg : ReversesCocharacter χ g) : ReversesCocharacter χ g⁻¹ := by
  change χ ≫ (G.innerIso g⁻¹).hom =
    CommGroupScheme.groupHom (Gm.powerHom _ (-1)) ≫ χ
  apply (cancel_mono (G.innerIso g).hom).mp
  rw [innerIso_inv_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, hg]
  exact (Dynamic.powerHom_neg_one_comp_powerHom_neg_one χ).symm

include hχ in
private theorem affineMatrix_cocharacter
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    ρ.affineMatrix A (x ≫ χ.hom.hom) =
      GeneralLinear.diagonalUnits A e
        (Gm.affinePointsEquiv ((algSpec (CommRingCat.of k)).obj (op A)).hom x) := by
  rw [affineMatrix_apply, Category.assoc, ← Grp.comp_hom_hom, hχ,
    GeneralLinear.CocharacterDiagonal.affinePointsEquiv_diagonalCocharacter]

include hχ in
/-- A reversing rational matrix exchanges precisely opposite weight blocks. -/
theorem rationalMatrix_entry_eq_zero_of_reversesCocharacter
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hg : ReversesCocharacter χ g) {a b : n} (hab : e a ≠ -e b) :
    (ρ.rationalMatrix g : Matrix n n k) a b = 0 := by
  let A := CommAlgCat.of k (LaurentPolynomial k)
  let Z := (algSpec (CommRingCat.of k)).obj (op A)
  let x : Z ⟶ (Gm (Spec (CommRingCat.of k))).X :=
    (Gm.affinePointsEquiv Z.hom).symm (Gm.relativeCoordUnit k)
  have ht := congrArg (fun f : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G =>
    x ≫ f.hom.hom) hg
  change x ≫ (χ ≫ (G.innerIso g).hom).hom.hom =
    x ≫ (Dynamic.oppositeCocharacter χ).hom.hom at ht
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom] at ht
  change G.constantPoint g Z * (x ≫ χ.hom.hom) * (G.constantPoint g Z)⁻¹ =
    (x ≫ (CommGroupScheme.groupHom (Gm.powerHom _ (-1))).hom.hom) ≫ χ.hom.hom at ht
  rw [Dynamic.comp_powerHom, zpow_neg_one] at ht
  have hm := congrArg (ρ.affineMatrix A) ht
  rw [map_mul, map_mul, map_inv, affineMatrix_constantPoint,
    ρ.affineMatrix_cocharacter χ e hχ, ρ.affineMatrix_cocharacter χ e hχ,
    map_inv, show Gm.affinePointsEquiv Z.hom x = Gm.relativeCoordUnit k from
      MulEquiv.apply_symm_apply _ _] at hm
  have he := congrArg (fun M : GL n (LaurentPolynomial k) =>
    (M : Matrix n n (LaurentPolynomial k)) a b)
      ((mul_inv_eq_iff_eq_mul).mp hm)
  simp only [Units.val_mul, GeneralLinear.coe_diagonalUnits, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.GeneralLinearGroup.map_apply, inv_zpow'] at he
  change (algebraMap k (LaurentPolynomial k)) ((ρ.rationalMatrix g : Matrix n n k) a b) *
      ((Gm.relativeCoordUnit k ^ e b : (LaurentPolynomial k)ˣ) : LaurentPolynomial k) =
    ((Gm.relativeCoordUnit k ^ (-e a) : (LaurentPolynomial k)ˣ) : LaurentPolynomial k) *
      (algebraMap k (LaurentPolynomial k)) ((ρ.rationalMatrix g : Matrix n n k) a b) at he
  rw [Gm.relativeCoordUnit_zpow_val, Gm.relativeCoordUnit_zpow_val] at he
  change LaurentPolynomial.C ((ρ.rationalMatrix g : Matrix n n k) a b) *
      LaurentPolynomial.T (e b) =
    LaurentPolynomial.T (-e a) *
      LaurentPolynomial.C ((ρ.rationalMatrix g : Matrix n n k) a b) at he
  apply GeneralLinear.eq_zero_of_C_mul_T_eq (m := e a + e b) (by omega)
  calc
    LaurentPolynomial.C ((ρ.rationalMatrix g : Matrix n n k) a b) *
        LaurentPolynomial.T (e a + e b) =
      LaurentPolynomial.T (e a) *
        (LaurentPolynomial.C ((ρ.rationalMatrix g : Matrix n n k) a b) *
          LaurentPolynomial.T (e b)) := by rw [LaurentPolynomial.T_add]; ring
    _ = LaurentPolynomial.T (e a) *
        (LaurentPolynomial.T (-e a) *
          LaurentPolynomial.C ((ρ.rationalMatrix g : Matrix n n k) a b)) := by rw [he]
    _ = _ := by
      rw [← mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel,
        LaurentPolynomial.T_zero, one_mul]

include hχ in
/-- A reversing point transports the all-test upper bound to the opposite
all-test lower bound. -/
theorem hasOrbitWeightLowerBound_of_reversesCocharacter
    (j : n) (hupper : ρ.HasOrbitWeightUpperBound e j)
    {s : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hs : ReversesCocharacter χ s) :
    ρ.HasOrbitWeightLowerBound e j := by
  intro Z g a ha
  let t := G.constantPoint s Z
  have hdecomp : g = t⁻¹ * (t * g) := by group
  rw [hdecomp, map_mul, Units.val_mul, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hb : e j < e b
  · rw [hupper Z (t * g) b hb, mul_zero]
  · have hab : e a ≠ -e b := by omega
    have hz := ρ.rationalMatrix_entry_eq_zero_of_reversesCocharacter χ e hχ hs.inv hab
    simp only [t, ← constantPoint_inv, pointMatrix_constantPoint,
      Matrix.GeneralLinearGroup.map_apply,
      hz, map_zero, zero_mul]

include hχ in
/-- Two-sided orbit support forces the original coordinate weight to be nonnegative. -/
theorem weight_nonneg_of_orbit_upperBound_of_reversesCocharacter
    (j : n) (hupper : ρ.HasOrbitWeightUpperBound e j)
    {s : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hs : ReversesCocharacter χ s) : 0 ≤ e j := by
  by_contra hj
  have hlow := ρ.hasOrbitWeightLowerBound_of_reversesCocharacter χ e hχ j hupper hs
  have h := hlow (Over.mk (𝟙 (Spec (CommRingCat.of k)))) 1 j (by omega)
  rw [map_one, Units.val_one, Matrix.one_apply_eq] at h
  have hk : (1 : k) = 0 := by
    simpa only [map_one, map_zero] using
      congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom h
  exact one_ne_zero hk

end Langlands.GroupScheme.MatrixRepresentation

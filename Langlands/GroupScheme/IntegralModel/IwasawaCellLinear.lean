import Langlands.GroupScheme.IntegralModel.IwasawaCellDynamic
import Langlands.GroupScheme.Dynamic.GeneralLinearCell
import Langlands.GroupScheme.Dynamic.GeneralLinearCellBlock
import Langlands.GroupScheme.Dynamic.GeneralLinearRationalPoints
import Langlands.GroupScheme.Dynamic.OppositeCellEmbedding
import Langlands.GroupScheme.MatrixRepresentation

/-! # Opposite-cell integrality from an integral diagonal matrix representation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace GeneralLinear

section CellIntegrality

variable {n : Type} [Fintype n] [DecidableEq n] {A : Type*} [CommRing A] (e : n → ℤ)

omit [Fintype n] in
/-- A block triangular matrix whose diagonal blocks are identity blocks has determinant one. -/
theorem det_eq_one_of_blockTriangular {κ α : Type*} [Fintype κ] [DecidableEq κ] [LinearOrder α]
    {M : Matrix κ κ A} {b : κ → α} (hM : M.BlockTriangular b)
    (hdiag : ∀ i j, b i = b j → M i j = (1 : Matrix κ κ A) i j) : M.det = 1 := by
  rw [hM.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have h1 : M.toSquareBlock b a = 1 := by
    ext i j
    rw [toSquareBlock_def, of_apply, hdiag _ _ (i.2.trans j.2.symm)]
    simp only [one_apply, Subtype.ext_iff]
  rw [h1, det_one]

/-- The upper threshold blocks of a block unipotent matrix for `-e` have determinant one. -/
theorem det_thresholdBlock_of_unipotent_neg (c : ℤ) {u : GL n A}
    (hu : u ∈ blockUnipotentSubgroup A (-e)) :
    (thresholdBlock e c (u : Matrix n n A)).det = 1 := by
  refine det_eq_one_of_blockTriangular (b := fun l : {l // c ≤ e l} => e l) ?_ ?_
  · intro i j hij
    change (u : Matrix n n A) i j = 0
    rw [hu i j (by simp only [Pi.neg_apply]; exact neg_le_neg hij.le)]
    have hij' : e j < e i := hij
    exact one_apply_ne fun h => (ne_of_gt hij') (congrArg e h)
  · intro i j hij
    change (u : Matrix n n A) i j = _
    rw [hu i j (by simp only [Pi.neg_apply]; exact neg_le_neg hij.ge)]
    simp only [one_apply, Subtype.ext_iff]

/-- The upper threshold blocks of a block unipotent matrix for `e` have determinant one. -/
theorem det_thresholdBlock_of_unipotent (c : ℤ) {w : GL n A}
    (hw : w ∈ blockUnipotentSubgroup A e) :
    (thresholdBlock e c (w : Matrix n n A)).det = 1 := by
  refine det_eq_one_of_blockTriangular
    (b := fun l : {l // c ≤ e l} => OrderDual.toDual (e l)) ?_ ?_
  · intro i j hij
    change (w : Matrix n n A) i j = 0
    have hij' : e i < e j := hij
    rw [hw i j hij'.le]
    exact one_apply_ne fun h => (ne_of_lt hij') (congrArg e h)
  · intro i j hij
    change (w : Matrix n n A) i j = _
    have hij' : e i = e j := hij
    rw [hw i j hij'.le]
    simp only [one_apply, Subtype.ext_iff]

/-- The cell minor of `u w`, with `u` block unipotent for `-e` and `w` block unipotent for `e`,
is one. -/
theorem cellMinor_mul_eq_one {u w : GL n A} (hu : u ∈ blockUnipotentSubgroup A (-e))
    (hw : w ∈ blockUnipotentSubgroup A e) :
    cellMinor e ((u * w : GL n A) : Matrix n n A) = 1 := by
  refine Finset.prod_eq_one fun c _ => ?_
  have hp := blockUnipotentSubgroup_le_blockParabolicSubgroup e hw
  rw [Units.val_mul, thresholdBlock_mul_of_right e c
      (fun m j hm hj => (mem_blockParabolicSubgroup A e).1 hp m j (by omega)),
    det_mul, det_thresholdBlock_of_unipotent_neg e c hu, det_thresholdBlock_of_unipotent e c hw,
    mul_one]

/-- **Integrality of the right factor of an opposite cell.** Let `f : R → K` be an injective
ring homomorphism. If `u` is block unipotent for `-e`, `w` is block unipotent for `e`, and
`u w` comes from an invertible matrix over `R`, then so does `w`. -/
theorem exists_map_eq_of_mul_mem_range {R K : Type*} [CommRing R] [CommRing K] (f : R →+* K)
    (hf : Function.Injective f) {u w : GL n K} (hu : u ∈ blockUnipotentSubgroup K (-e))
    (hw : w ∈ blockUnipotentSubgroup K e)
    (huw : u * w ∈ (Matrix.GeneralLinearGroup.map (n := n) f).range) :
    w ∈ (Matrix.GeneralLinearGroup.map (n := n) f).range := by
  obtain ⟨C, hC⟩ := huw
  have hcell : IsUnit (cellMinor e (C : Matrix n n R)) := by
    have h := map_cellMinor e f (C : Matrix n n R)
    have hmap : (C : Matrix n n R).map f = ((u * w : GL n K) : Matrix n n K) := by
      rw [← hC]
      rfl
    rw [hmap, cellMinor_mul_eq_one e hu hw, ← f.map_one] at h
    rw [hf h]
    exact isUnit_one
  obtain ⟨u', hu', p, hp, rfl⟩ := exists_cell_decomposition e C hcell
  refine ⟨p, ?_⟩
  have hmul : Matrix.GeneralLinearGroup.map f u' * Matrix.GeneralLinearGroup.map f p = u * w := by
    rw [← map_mul, hC]
  have hmem : (Matrix.GeneralLinearGroup.map f u')⁻¹ * u ∈
      blockUnipotentSubgroup K (-e) ⊓ blockParabolicSubgroup K e := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _
      (map_mem_blockUnipotentSubgroup (-e) f hu')) hu, ?_⟩
    have heq : (Matrix.GeneralLinearGroup.map f u')⁻¹ * u =
        Matrix.GeneralLinearGroup.map f p * w⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hmul, mul_inv_cancel_right]
    rw [heq]
    exact Subgroup.mul_mem _ (map_mem_blockParabolicSubgroup e f hp)
      (Subgroup.inv_mem _ (blockUnipotentSubgroup_le_blockParabolicSubgroup e hw))
  rw [blockUnipotentSubgroup_neg_inf_blockParabolicSubgroup, Subgroup.mem_bot,
    inv_mul_eq_one] at hmem
  rw [← hmem] at hmul
  exact mul_left_cancel hmul

end CellIntegrality

section RationalPoints

variable {N : ℕ} {R : CommRingCat.{u}}

/-- Rational points of `U(λ_e)` for the diagonal cocharacter of `e` have block unipotent
matrices. -/
theorem rationalPointsEquiv_mem_blockUnipotentSubgroup (e : Fin N → ℤ)
    (x : Over.mk (𝟙 (Spec R)) ⟶ (groupScheme (Fin N) R).X)
    (hx : x ∈ (Dynamic.unipotent (diagonalCocharacter (Fin N) R e)).carrier
      (Over.mk (𝟙 (Spec R)))) :
    rationalPointsEquiv N R x ∈ blockUnipotentSubgroup R e := by
  rw [unipotent_diagonalCocharacter] at hx
  exact (glRingEquiv_mem_blockUnipotentSubgroup_iff e (globalSectionsEquiv R)).2 hx

end RationalPoints

end GeneralLinear

namespace IntegralModel

/-- An internal construction target: for every supplied model with connected reductive full
special fibre and every cocharacter `χ` of the model, there is a matrix representation `ρ` of
`G` over `F` that turns the generic cocharacter of `χ` into a diagonal cocharacter and whose
rational points detect integrality: `g ∈ G(F)` is integral exactly when the matrix of `ρ g`
is the image of an invertible matrix over `𝒪[F]`. -/
def IntegralDiagonalRepresentationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (_hG : IsConnectedReductive G)
    (M : IntegralModel ↥𝒪[F] F G),
    IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group) →
    ∀ χ : (Gm (Spec (CommRingCat.of ↥𝒪[F]))).toGrp ⟶ M.group,
      ∃ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)) (e : Fin N → ℤ),
        M.genericCocharacter χ ≫ ρ = GeneralLinear.diagonalCocharacter (Fin N) _ e ∧
        ∀ g : rationalPoints G, g ∈ M.integralPoints ↔
          GeneralLinear.rationalPointsEquiv N _ (rationalPoints.map ρ g) ∈
            (Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap ↥𝒪[F] F)).range

/-- An integral diagonal matrix representation for every model cocharacter gives cell
integrality. -/
theorem dynamicCellIntegralityStatement_of_integralDiagonalRepresentation
    (h : IntegralDiagonalRepresentationStatement.{u}) :
    DynamicCellIntegralityStatement.{u} := by
  intro F _ _ _ _ G hG M hspecial χ v w hv hw hvw
  obtain ⟨N, ρ, e, hρ, hint⟩ := h F G hG M hspecial χ
  have hv' : GeneralLinear.rationalPointsEquiv N _ (rationalPoints.map ρ v) ∈
      GeneralLinear.blockUnipotentSubgroup F (-e) := by
    refine GeneralLinear.rationalPointsEquiv_mem_blockUnipotentSubgroup (-e) _ ?_
    have h1 := Dynamic.unipotent_le_comap
      (Dynamic.oppositeCocharacter (M.genericCocharacter χ)) ρ _ hv
    rw [SubgroupFunctor.mem_comap] at h1
    have h2 : Dynamic.oppositeCocharacter (M.genericCocharacter χ) ≫ ρ =
        GeneralLinear.diagonalCocharacter (Fin N) (CommRingCat.of F) (-e) := by
      rw [Dynamic.oppositeCocharacter, Category.assoc, hρ,
        GeneralLinear.inv_comp_diagonalCocharacter]
    rw [h2] at h1
    exact h1
  have hw' : GeneralLinear.rationalPointsEquiv N _ (rationalPoints.map ρ w) ∈
      GeneralLinear.blockUnipotentSubgroup F e := by
    refine GeneralLinear.rationalPointsEquiv_mem_blockUnipotentSubgroup e _ ?_
    have h1 := Dynamic.unipotent_le_comap (M.genericCocharacter χ) ρ _ hw
    rw [SubgroupFunctor.mem_comap, hρ] at h1
    exact h1
  have hvw' := (hint (v * w)).1 hvw
  rw [map_mul, map_mul] at hvw'
  exact (hint w).2 (GeneralLinear.exists_map_eq_of_mul_mem_range e (algebraMap ↥𝒪[F] F)
    (IsFractionRing.injective _ _) hv' hw' hvw')

/-- An integral diagonal matrix representation for every model cocharacter, together with a
model cocharacter with Levi maximality, proves the exact published maximal-compactness
statement. -/
theorem maximalCompactStatement_of_integralDiagonalRepresentation
    (h : IntegralDiagonalRepresentationStatement.{u})
    (hlevi : LeviMaximalCocharacterStatement.{u}) :
    MaximalCompactStatement.{u} :=
  maximalCompactStatement_of_dynamic
    (dynamicCellIntegralityStatement_of_integralDiagonalRepresentation h) hlevi

end IntegralModel

end Langlands.GroupScheme

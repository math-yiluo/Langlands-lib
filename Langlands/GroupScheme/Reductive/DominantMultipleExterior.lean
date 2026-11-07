import Langlands.GroupScheme.Chevalley.MatrixExterior
import Langlands.GroupScheme.Dynamic.GeneralLinear
import Mathlib.Order.Hom.PowersetCard

/-! # Exterior powers of diagonal cocharacters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Chevalley

variable {N d : ℕ} {A : Type*} [CommRing A]

/-- The exterior power of a diagonal invertible matrix is diagonal, with the products of the
selected diagonal entries. -/
theorem exteriorGL_diagonal (g : GL (Fin N) A) (w : Fin N → A)
    (hg : (g : Matrix (Fin N) (Fin N) A) = Matrix.diagonal w) :
    (exteriorGL N d A g : Matrix (Set.powersetCard (Fin N) d) (Set.powersetCard (Fin N) d) A) =
      Matrix.diagonal (fun s : Set.powersetCard (Fin N) d => ∏ a ∈ (s : Finset (Fin N)), w a) := by
  classical
  ext s t
  rw [exteriorGL_apply, hg]
  by_cases hst : s = t
  · subst hst
    rw [Matrix.diagonal_apply_eq]
    set σ := Set.powersetCard.ofFinEmbEquiv.symm s with hσ
    have hM : (Matrix.of fun i j : Fin d => Matrix.diagonal w (σ j) (σ i)) =
        Matrix.diagonal fun j => w (σ j) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · have hne : σ j ≠ σ i := fun h => hij (σ.injective h).symm
        simp [Matrix.diagonal_apply_ne _ hne, Matrix.diagonal_apply_ne _ hij]
    rw [hM, Matrix.det_diagonal]
    have himg : Finset.image σ Finset.univ = (s : Finset (Fin N)) := by
      rw [hσ, Set.powersetCard.ofFinEmbEquiv_symm_apply]
      exact Finset.image_orderEmbOfFin_univ _ _
    rw [← himg, Finset.prod_image fun x _ y _ h => σ.injective h]
  · rw [Matrix.diagonal_apply_ne _ hst]
    obtain ⟨i, his, hit⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne s t).mp hst
    obtain ⟨k, rfl⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s i).mpr his
    apply Matrix.det_eq_zero_of_column_eq_zero k
    intro j
    rw [Matrix.of_apply, Matrix.diagonal_apply_ne]
    intro h
    apply hit
    rw [h, Set.powersetCard.ofFinEmbEquiv_symm_apply, ← Set.powersetCard.mem_coe_iff]
    exact Finset.orderEmbOfFin_mem _ _ j

theorem units_zpow_sum {B : Type*} [CommMonoid B] (x : Bˣ) {J : Type*} (s : Finset J)
    (e : J → ℤ) : x ^ (∑ a ∈ s, e a) = ∏ a ∈ s, x ^ e a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add, ih]

variable (R : CommRingCat.{u})

/-- The exterior power of a diagonal cocharacter is the diagonal cocharacter of the sums of the
selected weights. -/
theorem diagonalCocharacter_comp_exteriorGroupHom (e : Fin N → ℤ) :
    GeneralLinear.diagonalCocharacter (Fin N) R e ≫ exteriorGroupHom N d R =
      GeneralLinear.diagonalCocharacter (Set.powersetCard (Fin N) d) R
        (fun s => ∑ a ∈ (s : Finset (Fin N)), e a) := by
  apply hom_ext_points
  intro T x
  apply (GeneralLinear.pointsEquiv (Set.powersetCard (Fin N) d) R T).injective
  rw [GeneralLinear.pointsEquiv_diagonalCocharacter]
  have h := exteriorRepresentation_pointMatrix N d R
    (GeneralLinear.diagonalCocharacter (Fin N) R e) T x
  rw [MatrixRepresentation.pointMatrix_apply, MatrixRepresentation.pointMatrix_apply,
    GeneralLinear.pointsEquiv_diagonalCocharacter] at h
  change GeneralLinear.pointsEquiv _ R T
    (x ≫ (exteriorRepresentation N d R (GeneralLinear.diagonalCocharacter (Fin N) R e)).hom.hom) = _
  rw [h]
  apply Units.ext
  rw [exteriorGL_diagonal _ (fun a => ((Gm.pointsEquiv (Spec R) T x ^ e a : Γ(T.left, ⊤)ˣ) :
    Γ(T.left, ⊤))) (GeneralLinear.coe_diagonalUnits _ _ _), GeneralLinear.coe_diagonalUnits]
  congr 1
  funext s
  rw [units_zpow_sum, Units.coe_prod]

/-! ### The coordinates of top weight -/

section Top

variable (e : Fin N → ℤ) (M : ℤ)

/-- The coordinates whose weight equals `M`. -/
def topSet : Finset (Fin N) := Finset.univ.filter fun a => e a = M

/-- The number of coordinates whose weight equals `M`. -/
def topCard : ℕ := (topSet e M).card

/-- The coordinates of weight `M`, as a point of the exterior index set of their size. -/
def topPoint : Set.powersetCard (Fin N) (topCard e M) :=
  ⟨topSet e M, Set.powersetCard.mem_iff.mpr rfl⟩

theorem mem_topSet {e M} {a : Fin N} : a ∈ topSet e M ↔ e a = M := by
  simp [topSet]

theorem sum_topPoint : ∑ a ∈ ((topPoint e M : Set.powersetCard (Fin N) (topCard e M)) :
    Finset (Fin N)), e a = (topCard e M : ℤ) * M := by
  change ∑ a ∈ topSet e M, e a = _
  rw [Finset.sum_congr rfl fun a ha => mem_topSet.mp ha, Finset.sum_const, nsmul_eq_mul]
  rfl

/-- If `M` bounds every weight, the coordinates of weight `M` form the unique subset of their
size with the largest weight sum. -/
theorem sum_lt_sum_topPoint (hM : ∀ a, e a ≤ M) (s : Set.powersetCard (Fin N) (topCard e M))
    (hs : s ≠ topPoint e M) :
    ∑ a ∈ (s : Finset (Fin N)), e a <
      ∑ a ∈ ((topPoint e M : Set.powersetCard (Fin N) (topCard e M)) : Finset (Fin N)), e a := by
  rw [sum_topPoint]
  obtain ⟨a, has, hat⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne s (topPoint e M)).mp hs
  have hlt : e a < M := lt_of_le_of_ne (hM a) fun h => hat (mem_topSet.mpr h)
  calc ∑ b ∈ (s : Finset (Fin N)), e b < ∑ b ∈ (s : Finset (Fin N)), M :=
        Finset.sum_lt_sum (fun b _ => hM b) ⟨a, has, hlt⟩
    _ = (topCard e M : ℤ) * M := by
        rw [Finset.sum_const, Set.powersetCard.card_eq, nsmul_eq_mul]

end Top

end Langlands.GroupScheme.Chevalley

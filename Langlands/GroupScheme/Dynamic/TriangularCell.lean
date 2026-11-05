import Langlands.GroupScheme.Dynamic.OppositeCellEmbedding
import Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterDiagonal
import Langlands.GroupScheme.CorepresentedClosedSubgroup

/-! # Upper triangular points in the opposite cell -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace GeneralLinear

variable {N : ℕ} {A : Type*} [CommRing A]

/-- A matrix in the block parabolic subgroup for the decreasing weights `i ↦ -i` is upper
triangular. -/
theorem isUpperTriangular_of_mem_blockParabolicSubgroup {g : GL (Fin N) A}
    (hg : g ∈ blockParabolicSubgroup A (fun i => -(i.val : ℤ))) :
    (g : Matrix (Fin N) (Fin N) A).IsUpperTriangular := by
  intro i j hij
  refine (mem_blockParabolicSubgroup A _).1 hg i j ?_
  have : (j : ℕ) < i := hij
  omega

/-- The diagonal entries of an invertible upper triangular matrix are units. -/
theorem isUnit_diag_of_mem_blockParabolicSubgroup {g : GL (Fin N) A}
    (hg : g ∈ blockParabolicSubgroup A (fun i => -(i.val : ℤ))) (i : Fin N) :
    IsUnit ((g : Matrix (Fin N) (Fin N) A) i i) := by
  have h := Matrix.isUnits_det_units g
  rw [det_of_isUpperTriangular (isUpperTriangular_of_mem_blockParabolicSubgroup hg)] at h
  exact IsUnit.prod_iff.1 h i (Finset.mem_univ i)

/-- Every invertible upper triangular matrix has invertible cell minor, for every weight
vector `e`: each threshold block is again upper triangular with unit diagonal. -/
theorem isUnit_cellMinor_of_mem_blockParabolicSubgroup (e : Fin N → ℤ) {g : GL (Fin N) A}
    (hg : g ∈ blockParabolicSubgroup A (fun i => -(i.val : ℤ))) :
    IsUnit (cellMinor e (g : Matrix (Fin N) (Fin N) A)) := by
  refine IsUnit.prod_iff.2 fun c _ => ?_
  have hT : (thresholdBlock e c (g : Matrix (Fin N) (Fin N) A)).IsUpperTriangular := by
    intro i j hij
    exact isUpperTriangular_of_mem_blockParabolicSubgroup hg hij
  rw [det_of_isUpperTriangular hT]
  exact IsUnit.prod_iff.2 fun i _ => isUnit_diag_of_mem_blockParabolicSubgroup hg i.1

end GeneralLinear

namespace Dynamic

open _root_.Langlands.GroupScheme.GeneralLinear

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]
  {G : GroupScheme (Spec (CommRingCat.of k))} {ρ : G ⟶ groupScheme n (CommRingCat.of k)}
  {χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G} {e : n → ℤ}

attribute [local instance] sectionsAlgebra

/-- **Pointwise opposite-cell decomposition.** Let `ρ` be a closed subgroup of `GL_n` and `χ` a
cocharacter with `χ ≫ ρ` diagonal for the weights `e`. A point `x` of `G` whose matrix has
invertible cell minor is a product `u p` of points `u` of `U(χ⁻¹)` and `p` of `P(χ)`. -/
theorem exists_mem_parabolic_of_isUnit_cellMinor [IsClosedImmersion ρ.hom.hom.left]
    (hχ : χ ≫ ρ = diagonalCocharacter n (CommRingCat.of k) e)
    {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ G.X)
    (hx : IsUnit (cellMinor e (pointsEquiv n _ T (x ≫ ρ.hom.hom) : Matrix n n Γ(T.left, ⊤)))) :
    ∃ p : T ⟶ G.X, p ∈ (parabolic χ).carrier T ∧
      x * p⁻¹ ∈ (unipotent (CommGroupScheme.groupHom
        (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)).carrier T := by
  obtain ⟨u', hu', p', hp', hup⟩ := exists_cell_decomposition e _ hx
  have hp'Z : p' ∈ zeroLocus Γ(T.left, ⊤) (embeddingIdeal ρ) :=
    mem_zeroLocus_of_mul_mem e ideal_le_embeddingIdeal zeroLocusMulClosed_embeddingIdeal
      one_mem_zeroLocus_embeddingIdeal (diagonalUnits_mem_zeroLocus_embeddingIdeal hχ) hu' hp'
      (hup ▸ pointsEquiv_comp_mem_zeroLocus x)
  obtain ⟨p₀, hp₀⟩ := exists_comp_eq_of_mem_zeroLocus ((pointsEquiv n _ T).symm p')
    (by rw [MulEquiv.apply_symm_apply]; exact hp'Z)
  refine ⟨p₀, ?_, ?_⟩
  · rw [mem_parabolic_iff_of_diagonal hχ, hp₀, MulEquiv.apply_symm_apply]
    exact hp'
  · rw [mem_unipotent_iff_of_diagonal hχ, MonObj.mul_comp, GrpObj.inv_comp, pointsEquiv_mul,
      map_inv, hp₀, MulEquiv.apply_symm_apply, hup, mul_inv_cancel_right]
    exact hu'

end Dynamic

end Langlands.GroupScheme

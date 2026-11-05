import Langlands.Group.WeightedPolarIwasawa
import Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterDiagonal
import Langlands.GroupScheme.Dynamic.GeneralLinearRationalPoints
import Langlands.GroupScheme.Dynamic.OppositeCellEmbedding
import Langlands.GroupScheme.GeneralLinearPointTopology

/-! # Dynamic parabolic coverage from Hermitian right remainders -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Filter
open scoped CategoryTheory.MonObj Pointwise Topology

namespace Langlands.GroupScheme.Dynamic

open _root_.Langlands.GroupScheme.GeneralLinear Langlands.Group.WeightedPolarIwasawa

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
variable {G : GroupScheme (Spec (CommRingCat.of k))}
variable {n : Type} [Fintype n] [DecidableEq n]

/-- Evaluation of an actual cocharacter on units of the coefficient algebra. -/
def cocharacterPointHom
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (A : CommAlgCat.{u} (CommRingCat.of k)) : Aˣ →* G.affinePoints A :=
  (GroupScheme.affinePointsTarget (Gm (Spec (CommRingCat.of k))).toGrp χ A).comp
    (Gm.affinePointsEquiv ((algSpec (CommRingCat.of k)).obj (op A)).hom).symm.toMonoidHom

variable (ρ : MatrixRepresentation G n)
variable {χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G} {e : n → ℤ}

/-- A diagonal represented cocharacter has its specified matrix on every affine point. -/
theorem affineMatrix_cocharacterPointHom
    (hχ : χ ≫ ρ = diagonalCocharacter n (CommRingCat.of k) e)
    (A : CommAlgCat.{u} (CommRingCat.of k)) (t : Aˣ) :
    ρ.affineMatrix A (cocharacterPointHom χ A t) = diagonalUnits A e t := by
  change affinePointsEquiv n _ A
    (((Gm.affinePointsEquiv ((algSpec (CommRingCat.of k)).obj (op A)).hom).symm t ≫ χ.hom.hom) ≫ ρ.hom.hom) = _
  rw [Category.assoc, ← Grp.comp_hom_hom, hχ,
    CocharacterDiagonal.affinePointsEquiv_diagonalCocharacter]
  erw [MulEquiv.apply_symm_apply]

/-- On affine points the diagonal dynamic parabolic is the existing matrix block comap. -/
theorem parabolic_carrier_eq_blockComap
    [IsClosedImmersion ρ.hom.hom.left]
    (hχ : χ ≫ ρ = diagonalCocharacter n (CommRingCat.of k) e)
    (S : CommAlgCat.{u} (CommRingCat.of k)) :
    (parabolic χ).carrier ((algSpec (CommRingCat.of k)).obj (op S)) =
      (blockParabolicSubgroup S e).comap (ρ.affineMatrix S) := by
  ext x
  rw [mem_parabolic_iff_of_diagonal hχ]
  change ρ.pointMatrix ((algSpec (CommRingCat.of k)).obj (op S)) x ∈ _ ↔ _
  rw [ρ.pointMatrix_eq_affineMatrix S x]
  change glRingEquiv (Corepresented.affineSectionsAlgEquiv S).symm.toRingEquiv
      (ρ.affineMatrix S x) ∈ blockParabolicSubgroup _ e ↔
    ρ.affineMatrix S x ∈ blockParabolicSubgroup S e
  exact glRingEquiv_mem_blockParabolicSubgroup_iff e
    (Corepresented.affineSectionsAlgEquiv S).symm.toRingEquiv

variable {A : Type u} [RCLike A] [Algebra k A]

local instance : TopologicalSpace (G.affinePoints (CommAlgCat.of (CommRingCat.of k) A)) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of (CommRingCat.of k) A)

/-- Hermitian right remainders give coverage by the actual dynamic parabolic and the
supplied compact subgroup. The diagonal sequence is obtained by evaluating the cocharacter. -/
theorem parabolic_mul_compact_eq_univ_of_hermitian
    [IsClosedImmersion ρ.hom.hom.left]
    (hχ : χ ≫ ρ = diagonalCocharacter n (CommRingCat.of k) e)
    (K : Subgroup (G.affinePoints (CommAlgCat.of (CommRingCat.of k) A)))
    (hK : IsCompact (K : Set (G.affinePoints (CommAlgCat.of (CommRingCat.of k) A))))
    (hh : ∀ x : G.affinePoints (CommAlgCat.of (CommRingCat.of k) A), ∃ z ∈ K,
      (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) A) (x * z⁻¹) : Matrix n n A).IsHermitian) :
    ((parabolic χ).carrier (affineTest k A) : Set (G.affinePoints (CommAlgCat.of (CommRingCat.of k) A))) *
      (K : Set (G.affinePoints (CommAlgCat.of (CommRingCat.of k) A))) = Set.univ := by
  let t : ℕ → ℝ := fun m => (1 / 2 : ℝ) ^ m
  have ht0 (m : ℕ) : t m ≠ 0 := pow_ne_zero m (by norm_num)
  have ht : Tendsto t atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  let D : ℕ → G.affinePoints (CommAlgCat.of (CommRingCat.of k) A) := fun m =>
    cocharacterPointHom χ (CommAlgCat.of (CommRingCat.of k) A)
      (Units.mk0 (t m : A) (RCLike.ofReal_ne_zero.mpr (ht0 m)))
  have hD (m : ℕ) :
      (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) A) (D m) : Matrix n n A) =
        Matrix.diagonal (fun i => (t m : A) ^ e i) := by
    dsimp only [D]
    rw [affineMatrix_cocharacterPointHom ρ hχ, coe_diagonalUnits]
    simp
  rw [parabolic_carrier_eq_blockComap ρ hχ (CommAlgCat.of (CommRingCat.of k) A)]
  exact mul_compact_eq_univ_of_hermitian (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) A))
    ((continuous_affinePointsEquiv n (CommRingCat.of k) (CommAlgCat.of (CommRingCat.of k) A)).comp
      (G.continuous_affinePointsTarget (CommAlgCat.of (CommRingCat.of k) A) ρ))
    K hK hh e t ht0 ht D hD

/-- If an actual subgroup represents the dynamic parabolic, its literal point-map
range has the ordered covering supplied by the Hermitian argument. -/
theorem range_mul_compact_eq_univ_of_hermitian
    [IsClosedImmersion ρ.hom.hom.left]
    (hχ : χ ≫ ρ = diagonalCocharacter n (CommRingCat.of k) e)
    {P : GroupScheme (Spec (CommRingCat.of k))} (p : P ⟶ G)
    (hP : (parabolic χ).IsRepresentedBy p)
    (K : Subgroup (G.affinePoints (CommAlgCat.of (CommRingCat.of k) A)))
    (hK : IsCompact (K : Set (G.affinePoints (CommAlgCat.of (CommRingCat.of k) A))))
    (hh : ∀ x : G.affinePoints (CommAlgCat.of (CommRingCat.of k) A), ∃ z ∈ K,
      (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) A) (x * z⁻¹) : Matrix n n A).IsHermitian) :
    Set.range (P.affinePointsTarget p (CommAlgCat.of (CommRingCat.of k) A)) *
      (K : Set (G.affinePoints (CommAlgCat.of (CommRingCat.of k) A))) = Set.univ := by
  change ((SubgroupFunctor.range p).carrier (affineTest k A) :
    Set (G.affinePoints (CommAlgCat.of (CommRingCat.of k) A))) * _ = _
  rw [hP.2]
  exact parabolic_mul_compact_eq_univ_of_hermitian ρ hχ K hK hh

end Langlands.GroupScheme.Dynamic

import Langlands.GroupScheme.MatrixRepresentationConjugate
import Langlands.Group.ConjugatedWeightedPolarIwasawa
import Langlands.GroupScheme.Dynamic.ParabolicPolarCover

/-! # Dynamic parabolic coverage without a compatible diagonalizing basis -/

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
variable (ρ : MatrixRepresentation G n)
variable {A : Type u} [RCLike A] [Algebra k A]

local instance conjugatedParabolicPolarPointTopology : TopologicalSpace (G.affinePoints (CommAlgCat.of (CommRingCat.of k) A)) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of (CommRingCat.of k) A)

/-- Every actual cocharacter has ordered parabolic coverage from an adjoint-stable
closed representation and a compact subgroup with Hermitian right remainders. -/
theorem parabolic_mul_compact_eq_univ_of_star_hermitian
    [IsClosedImmersion ρ.hom.hom.left]
    (hstar : ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) A)).range,
      star q ∈ (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) A)).range)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (K : Subgroup (G.affinePoints (CommAlgCat.of (CommRingCat.of k) A)))
    (hK : IsCompact (K : Set (G.affinePoints (CommAlgCat.of (CommRingCat.of k) A))))
    (hh : ∀ x : G.affinePoints (CommAlgCat.of (CommRingCat.of k) A), ∃ z ∈ K,
      (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) A) (x * z⁻¹) : Matrix n n A).IsHermitian) :
    ((parabolic χ).carrier (affineTest k A) :
      Set (G.affinePoints (CommAlgCat.of (CommRingCat.of k) A))) *
      (K : Set (G.affinePoints (CommAlgCat.of (CommRingCat.of k) A))) = Set.univ := by
  classical
  let S := CommAlgCat.of (CommRingCat.of k) A
  obtain ⟨g, e, hg⟩ := exists_innerIso_comp_eq_diagonalCocharacter k (χ ≫ ρ)
  let ρ' := ρ.conjugate g
  have hχ : χ ≫ ρ' = diagonalCocharacter n (CommRingCat.of k) e := by
    simpa only [ρ', MatrixRepresentation.conjugate, Category.assoc] using hg
  let : IsClosedImmersion ρ'.hom.hom.left := by
    change IsClosedImmersion
      (ρ.hom.hom.left ≫ ((groupScheme n (CommRingCat.of k)).innerIso g).hom.hom.hom.left)
    infer_instance
  let C : GL n A := affinePointsEquiv n (CommRingCat.of k) S
    ((groupScheme n (CommRingCat.of k)).constantPoint g (affineTest k A))
  let B : GL n A := C⁻¹
  have hm : ρ'.affineMatrix S = conjugatedRepresentation (ρ.affineMatrix S) B := by
    apply MonoidHom.ext
    intro x
    rw [conjugatedRepresentation_apply]
    change (ρ.conjugate g).affineMatrix S x = (C⁻¹)⁻¹ * ρ.affineMatrix S x * C⁻¹
    rw [ρ.conjugate_affineMatrix, MatrixRepresentation.standard_affineMatrix]
    simp only [inv_inv]
    rfl
  let t : ℕ → ℝ := fun m => (1 / 2 : ℝ) ^ m
  have ht0 (m : ℕ) : t m ≠ 0 := pow_ne_zero m (by norm_num)
  have ht : Tendsto t atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  let D : ℕ → G.affinePoints S := fun m => cocharacterPointHom χ S
    (Units.mk0 (t m : A) (RCLike.ofReal_ne_zero.mpr (ht0 m)))
  have hD (m : ℕ) : (B⁻¹ * ρ.affineMatrix S (D m) * B : Matrix n n A) =
      Matrix.diagonal (fun i => (t m : A) ^ e i) := by
    change (conjugatedRepresentation (ρ.affineMatrix S) B (D m) : Matrix n n A) = _
    rw [← hm]
    dsimp only [D]
    rw [affineMatrix_cocharacterPointHom ρ' hχ, coe_diagonalUnits]
    simp
  rw [parabolic_carrier_eq_blockComap ρ' hχ S, hm]
  exact conjugated_mul_compact_eq_univ_of_hermitian (ρ.affineMatrix S)
    ((continuous_affinePointsEquiv n (CommRingCat.of k) S).comp
      (G.continuous_affinePointsTarget S ρ))
    hstar K hK hh B e t ht0 ht D hD

/-- The literal point-map range of any representative of an actual dynamic parabolic
has the ordered covering, without a compatible-diagonalization premise. -/
theorem range_mul_compact_eq_univ_of_star_hermitian
    [IsClosedImmersion ρ.hom.hom.left]
    (hstar : ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) A)).range,
      star q ∈ (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) A)).range)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
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
  exact parabolic_mul_compact_eq_univ_of_star_hermitian ρ hstar χ K hK hh

end Langlands.GroupScheme.Dynamic

import Langlands.GroupScheme.Dynamic.UnitaryCocharacterDiagonal
import Langlands.GroupScheme.Dynamic.LeviCompatiblePolarIwasawa
import Langlands.GroupScheme.MatrixRepresentationConjugate

/-! # Levi-compatible polar Iwasawa from Hermitian weight data -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {𝕜 : Type u} [RCLike 𝕜]
  {G : GroupScheme (Spec (CommRingCat.of 𝕜))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Conjugating the representation by an actual base matrix acts by that same
matrix on its base-field affine points. -/
theorem conjugate_baseOfMatrix_affineMatrix
    (ρ : MatrixRepresentation G n) (g : GL n 𝕜)
    (x : G.affinePoints (CommAlgCat.of 𝕜 𝕜)) :
    (ρ.conjugate (GeneralLinear.baseOfMatrix (CommRingCat.of 𝕜) g)).affineMatrix
        (CommAlgCat.of 𝕜 𝕜) x =
      g * ρ.affineMatrix (CommAlgCat.of 𝕜 𝕜) x * g⁻¹ := by
  rw [conjugate_affineMatrix]
  rw [standard_affineMatrix,
    GeneralLinear.affinePointsEquiv_constantPoint_baseOfMatrix]
  have hmap : Matrix.GeneralLinearGroup.map (algebraMap 𝕜 𝕜) g = g := by
    ext i j
    simp
  rw [hmap]

/-- A unitary change of coordinates preserves star stability of the actual
base-field point image. -/
theorem conjugate_baseOfMatrix_star_stable
    (ρ : MatrixRepresentation G n) (g : GL n 𝕜)
    (hg : (g : Matrix n n 𝕜) ∈ Matrix.unitaryGroup n 𝕜)
    (hstar : ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of 𝕜 𝕜)).range,
      star q ∈ (ρ.affineMatrix (CommAlgCat.of 𝕜 𝕜)).range) :
    ∀ q ∈ ((ρ.conjugate (GeneralLinear.baseOfMatrix (CommRingCat.of 𝕜) g)).affineMatrix
      (CommAlgCat.of 𝕜 𝕜)).range,
      star q ∈ ((ρ.conjugate (GeneralLinear.baseOfMatrix (CommRingCat.of 𝕜) g)).affineMatrix
        (CommAlgCat.of 𝕜 𝕜)).range := by
  have hu : g ∈ unitary (GL n 𝕜) := by
    simpa only [Units.unitary_eq, Submonoid.mem_comap, Units.coeHom_apply] using hg
  have hgs : star g = g⁻¹ := eq_inv_of_mul_eq_one_left hu.1
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hstar _ ⟨x, rfl⟩
  refine ⟨y, ?_⟩
  rw [conjugate_baseOfMatrix_affineMatrix, conjugate_baseOfMatrix_affineMatrix]
  simp only [star_mul, star_inv, hgs, inv_inv]
  rw [hy, mul_assoc]

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.Dynamic

variable {𝕜 : Type u} [RCLike 𝕜]
  {G P M : GroupScheme (Spec (CommRingCat.of 𝕜))}

/-- Closed star-stable realization with a common cocharacter for the supplied
pair and Hermitian Laurent weight projectors. -/
def HasHermitianStarLeviRealization (p : P ⟶ G) (m : M ⟶ G) : Prop :=
  ∃ (d : ℕ) (ρ : MatrixRepresentation G (Fin d))
    (χ : (Gm (Spec (CommRingCat.of 𝕜))).toGrp ⟶ G),
    IsClosedSubgroup ρ ∧
      GeneralLinear.HasHermitianWeightProjectors (χ ≫ ρ) ∧
      (parabolic χ).IsRepresentedBy p ∧ (centralizer χ).IsRepresentedBy m ∧
      ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of 𝕜 𝕜)).range,
        star q ∈ (ρ.affineMatrix (CommAlgCat.of 𝕜 𝕜)).range

/-- Unitary weight diagonalization converts Hermitian realization into the
compatible diagonal data required by the polar construction. -/
theorem HasHermitianStarLeviRealization.hasDiagonalStarLeviRealization
    {p : P ⟶ G} {m : M ⟶ G} (h : HasHermitianStarLeviRealization p m) :
    HasDiagonalStarLeviRealization p m := by
  obtain ⟨d, ρ, χ, hc, hχ, hp, hm, hs⟩ := h
  obtain ⟨g, e, hg, he⟩ :=
    GeneralLinear.exists_unitary_innerIso_comp_eq_diagonalCocharacter (χ ≫ ρ) hχ
  let σ := ρ.conjugate (GeneralLinear.baseOfMatrix (CommRingCat.of 𝕜) g)
  have hsc : IsClosedSubgroup σ := by
    let : IsClosedImmersion ρ.hom.hom.left := hc
    change IsClosedImmersion (ρ.hom.hom.left ≫ _)
    infer_instance
  have hsd : χ ≫ σ = GeneralLinear.diagonalCocharacter (Fin d) (CommRingCat.of 𝕜) e := by
    simpa only [σ, MatrixRepresentation.conjugate, Category.assoc] using he
  exact ⟨d, σ, χ, e, ⟨hsc, hsd, hp, hm⟩,
    ρ.conjugate_baseOfMatrix_star_stable g hg hs⟩

local instance hermitianLeviIwasawaPointTopology (H : GroupScheme (Spec (CommRingCat.of 𝕜))) :
    TopologicalSpace (H.affinePoints (CommAlgCat.of 𝕜 𝕜)) :=
  H.affinePointsTopologicalSpace (CommAlgCat.of 𝕜 𝕜)

/-- Hermitian realization constructs a compact satisfying all four actual
Levi-compatible Iwasawa conclusions. -/
theorem HasHermitianStarLeviRealization.hasLeviCompatibleDecomposition
    [IsAffine G.X.left] {p : P ⟶ G} {m : M ⟶ G}
    (h : HasHermitianStarLeviRealization p m) :
    CompactIwasawa.HasLeviCompatibleDecomposition
      (P.affinePointsTarget p (CommAlgCat.of 𝕜 𝕜))
      (M.affinePointsTarget m (CommAlgCat.of 𝕜 𝕜)) :=
  h.hasDiagonalStarLeviRealization.hasLeviCompatibleDecomposition

end Langlands.GroupScheme.Dynamic

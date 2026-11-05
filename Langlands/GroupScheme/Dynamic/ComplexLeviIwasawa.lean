import Langlands.GroupScheme.Dynamic.TwoPowerCocharacter

/-! # Complex Levi-compatible Iwasawa from ambient star realization -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {𝕜 : Type u} [RCLike 𝕜]

/-- A closed representation of the actual group with star-stable base-field
point image. This condition involves only the ambient group. -/
def HasClosedStarRealization (G : GroupScheme (Spec (CommRingCat.of 𝕜))) : Prop :=
  ∃ (d : ℕ) (ρ : MatrixRepresentation G (Fin d)),
    IsClosedSubgroup ρ ∧
      ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of 𝕜 𝕜)).range,
        star q ∈ (ρ.affineMatrix (CommAlgCat.of 𝕜 𝕜)).range

variable [IsAlgClosed 𝕜]
  {G P M : GroupScheme (Spec (CommRingCat.of 𝕜))}

/-- Internal conjugation makes a supplied common dynamic cocharacter
Hermitian while preserving the ambient star-stable image. -/
theorem HasClosedStarRealization.hasHermitianStarLeviRealization
    (h : HasClosedStarRealization G)
    (χ : (Gm (Spec (CommRingCat.of 𝕜))).toGrp ⟶ G)
    {p : P ⟶ G} {m : M ⟶ G}
    (hp : (Dynamic.parabolic χ).IsRepresentedBy p)
    (hm : (Dynamic.centralizer χ).IsRepresentedBy m) :
    Dynamic.HasHermitianStarLeviRealization p m := by
  obtain ⟨d, ρ, hρ, hs⟩ := h
  obtain ⟨g, hg, hχ⟩ := ρ.exists_internal_conjugate_hermitian hρ hs χ
  let σ := ρ.conjugate (GeneralLinear.baseOfMatrix (CommRingCat.of 𝕜) g)
  have hσ : IsClosedSubgroup σ := by
    let : IsClosedImmersion ρ.hom.hom.left := hρ
    change IsClosedImmersion (ρ.hom.hom.left ≫ _)
    infer_instance
  have hr := ρ.conjugate_baseOfMatrix_range_eq_of_mem g hg
  have hσs : ∀ q ∈ (σ.affineMatrix (CommAlgCat.of 𝕜 𝕜)).range,
      star q ∈ (σ.affineMatrix (CommAlgCat.of 𝕜 𝕜)).range := by
    simpa only [σ, hr] using hs
  exact ⟨d, σ, χ, hσ, hχ, hp, hm, hσs⟩

/-- An ambient closed star realization suffices for compatible diagonal data
over algebraically closed `RCLike` coefficients. -/
theorem HasClosedStarRealization.hasDiagonalStarLeviRealization
    (h : HasClosedStarRealization G)
    (χ : (Gm (Spec (CommRingCat.of 𝕜))).toGrp ⟶ G)
    {p : P ⟶ G} {m : M ⟶ G}
    (hp : (Dynamic.parabolic χ).IsRepresentedBy p)
    (hm : (Dynamic.centralizer χ).IsRepresentedBy m) :
    Dynamic.HasDiagonalStarLeviRealization p m :=
  (h.hasHermitianStarLeviRealization χ hp hm).hasDiagonalStarLeviRealization

local instance complexLeviIwasawaPointTopology
    (H : GroupScheme (Spec (CommRingCat.of 𝕜))) :
    TopologicalSpace (H.affinePoints (CommAlgCat.of 𝕜 𝕜)) :=
  H.affinePointsTopologicalSpace (CommAlgCat.of 𝕜 𝕜)

/-- Construct all four actual-point Levi-compatible Iwasawa conclusions from
an ambient star realization and a supplied common dynamic cocharacter. -/
theorem HasClosedStarRealization.hasLeviCompatibleDecomposition
    [IsAffine G.X.left] (h : HasClosedStarRealization G)
    (χ : (Gm (Spec (CommRingCat.of 𝕜))).toGrp ⟶ G)
    {p : P ⟶ G} {m : M ⟶ G}
    (hp : (Dynamic.parabolic χ).IsRepresentedBy p)
    (hm : (Dynamic.centralizer χ).IsRepresentedBy m) :
    CompactIwasawa.HasLeviCompatibleDecomposition
      (P.affinePointsTarget p (CommAlgCat.of 𝕜 𝕜))
      (M.affinePointsTarget m (CommAlgCat.of 𝕜 𝕜)) :=
  (h.hasDiagonalStarLeviRealization χ hp hm).hasLeviCompatibleDecomposition

end Langlands.GroupScheme.MatrixRepresentation

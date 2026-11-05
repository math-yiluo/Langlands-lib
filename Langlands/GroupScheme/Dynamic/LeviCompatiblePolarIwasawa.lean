import Langlands.GroupScheme.Dynamic.UnitaryLeviIntersection
import Langlands.GroupScheme.Dynamic.ParabolicPolarCover
import Langlands.GroupScheme.Dynamic.RepresentedStructure
import Langlands.GroupScheme.AffinePolarCompact
import Langlands.Global.InfinitePlaceLeviIwasawaBaseChange

/-! # All four Iwasawa conclusions from a compatible diagonal star realization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise Matrix ComplexOrder

namespace Langlands.GroupScheme.Dynamic

set_option backward.isDefEq.respectTransparency false

variable {𝕜 : Type u} [RCLike 𝕜]
  {G P M : GroupScheme (Spec (CommRingCat.of 𝕜))}

local instance leviCompatiblePolarIwasawaInst1 (H : GroupScheme (Spec (CommRingCat.of 𝕜))) :
    TopologicalSpace (H.affinePoints (CommAlgCat.of 𝕜 𝕜)) :=
  H.affinePointsTopologicalSpace (CommAlgCat.of 𝕜 𝕜)

/-- Existence of a closed star-stable representation in which a single
diagonal cocharacter realizes both of the specified subgroup morphisms.
No general existence assertion is made by this definition. -/
def HasDiagonalStarLeviRealization (p : P ⟶ G) (m : M ⟶ G) : Prop :=
  ∃ (d : ℕ) (ρ : MatrixRepresentation G (Fin d))
    (χ : (Gm (Spec (CommRingCat.of 𝕜))).toGrp ⟶ G) (e : Fin d → ℤ),
    IsDiagonalLeviPair ρ χ e p m ∧
      ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of 𝕜 𝕜)).range,
        star q ∈ (ρ.affineMatrix (CommAlgCat.of 𝕜 𝕜)).range

variable [IsAffine G.X.left]
  {d : ℕ} {ρ : MatrixRepresentation G (Fin d)}
  {χ : (Gm (Spec (CommRingCat.of 𝕜))).toGrp ⟶ G}
  {e : Fin d → ℤ} {p : P ⟶ G} {m : M ⟶ G}

/-- The unitary inverse image of compatible star-stable diagonal data satisfies
ambient maximal compactness, ordered coverage, the exact intersection identity,
and maximal compactness on the specified Levi's actual point carrier. -/
theorem IsDiagonalLeviPair.isLeviCompatibleDecomposition_affineUnitarySubgroup
    (h : IsDiagonalLeviPair ρ χ e p m)
    (hstar : ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of 𝕜 𝕜)).range,
      star q ∈ (ρ.affineMatrix (CommAlgCat.of 𝕜 𝕜)).range) :
    CompactIwasawa.IsLeviCompatibleDecomposition
      (P.affinePointsTarget p (CommAlgCat.of 𝕜 𝕜))
      (M.affinePointsTarget m (CommAlgCat.of 𝕜 𝕜))
      (ρ.affineUnitarySubgroup (S := 𝕜)) := by
  have hK : CompactIwasawa.IsMaximalCompact (ρ.affineUnitarySubgroup (S := 𝕜)) :=
    (ρ.affineMaximalCompact h.1 hstar).property
  refine ⟨hK, ?_, ?_, ?_⟩
  · let : IsClosedImmersion ρ.hom.hom.left := h.1
    apply range_mul_compact_eq_univ_of_hermitian ρ h.2.1 p h.2.2.1
      (ρ.affineUnitarySubgroup (S := 𝕜)) hK.1
    intro x
    obtain ⟨z, hz, hpos⟩ := ρ.exists_affineUnitary_right_quotient_posDef h.1 hstar x
    exact ⟨z, hz, hpos.isHermitian⟩
  · exact congrArg (fun H : Subgroup (G.affinePoints (CommAlgCat.of 𝕜 𝕜)) =>
      (H : Set (G.affinePoints (CommAlgCat.of 𝕜 𝕜))))
      h.range_inf_unitarySubgroup
  · have hm : IsClosedSubgroup m :=
      Affine.isClosedSubgroup_of_isRepresentedBy_centralizer χ h.2.2.2
    let : IsClosedImmersion m.hom.hom.left := hm
    let : IsAffine M.X.left := isAffine_of_isAffineHom m.hom.hom.left
    have hr : IsClosedSubgroup (ρ.restrict m) := by
      change IsClosedImmersion (m.hom.hom.left ≫ ρ.hom.hom.left)
      let : IsClosedImmersion ρ.hom.hom.left := h.1
      infer_instance
    have hs : ∀ x : G.affinePoints (CommAlgCat.of 𝕜 𝕜),
        ∃ y : G.affinePoints (CommAlgCat.of 𝕜 𝕜),
          (ρ.affineMatrix _ y : Matrix (Fin d) (Fin d) 𝕜) =
            star (ρ.affineMatrix _ x : Matrix (Fin d) (Fin d) 𝕜) := by
      intro x
      obtain ⟨y, hy⟩ := hstar _ ⟨x, rfl⟩
      exact ⟨y, congrArg Units.val hy⟩
    have hrs : ∀ q ∈ ((ρ.restrict m).affineMatrix (CommAlgCat.of 𝕜 𝕜)).range,
        star q ∈ ((ρ.restrict m).affineMatrix (CommAlgCat.of 𝕜 𝕜)).range := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := h.restrict_star_stable hs x
      exact ⟨y, Units.ext hy⟩
    have hKM : CompactIwasawa.IsMaximalCompact
        ((ρ.restrict m).affineUnitarySubgroup (S := 𝕜)) :=
      ((ρ.restrict m).affineMaximalCompact hr hrs).property
    exact hKM

/-- Compatible diagonal star realization constructs the compact subgroup and
all four conclusions, without a supplied compact or decomposition. -/
theorem HasDiagonalStarLeviRealization.hasLeviCompatibleDecomposition
    (h : HasDiagonalStarLeviRealization p m) :
    CompactIwasawa.HasLeviCompatibleDecomposition
      (P.affinePointsTarget p (CommAlgCat.of 𝕜 𝕜))
      (M.affinePointsTarget m (CommAlgCat.of 𝕜 𝕜)) := by
  obtain ⟨d, ρ, χ, e, hpair, hstar⟩ := h
  exact ⟨_, hpair.isLeviCompatibleDecomposition_affineUnitarySubgroup hstar⟩

end Langlands.GroupScheme.Dynamic

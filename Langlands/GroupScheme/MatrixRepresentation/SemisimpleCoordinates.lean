import Langlands.GroupScheme.MatrixRepresentation.DirectSumCoordinates
import Langlands.GroupScheme.MatrixRepresentation.AffineSemisimpleModules

/-! # Coordinates for simple stable subspaces and semisimple decompositions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Actual finite representation coordinates for a supplied stable subspace. -/
structure StableSubspaceRepresentation (ρ : MatrixRepresentation G n)
    (W : Submodule k (n → k)) where
  dimension : ℕ
  representation : MatrixRepresentation G (Fin dimension)
  inclusion : Matrix n (Fin dimension) k
  intertwines : representation.Intertwines ρ inclusion
  injective : Function.Injective inclusion.mulVecLin
  range_eq : LinearMap.range inclusion.mulVecLin = W

/-- Every all-affine-test stable subspace has actual finite representation coordinates. -/
theorem IsStableSubspace.nonempty_representationCoordinates [IsAffineHom G.X.hom]
    {ρ : MatrixRepresentation G n} {W : Submodule k (n → k)}
    (hW : ρ.IsStableSubspace W) : Nonempty (StableSubspaceRepresentation ρ W) := by
  classical
  obtain ⟨d, B, C, hCB, hcols, hproj⟩ := exists_subspace_split_coordinates W
  have hs := hW.isStableCoordinates B C hcols hproj
  exact ⟨{
    dimension := d
    representation := restrictCoordinates ρ B C hCB hs
    inclusion := B
    intertwines := intertwines_restrictCoordinates ρ B C hCB hs
    injective := coordinateInclusion_injective (R := CommRingCat.of k) B C hCB
    range_eq := range_coordinateInclusion_eq W B C hcols hproj
  }⟩

/-- Choose an actual coordinate representation of a stable subspace. -/
def IsStableSubspace.representationCoordinates [IsAffineHom G.X.hom]
    {ρ : MatrixRepresentation G n} {W : Submodule k (n → k)}
    (hW : ρ.IsStableSubspace W) : StableSubspaceRepresentation ρ W :=
  Classical.choice hW.nonempty_representationCoordinates

/-- Coordinates of a simple stable subspace give an irreducible actual representation. -/
theorem IsSimpleStableSubspace.isIrreducible_coordinates
    {ρ : MatrixRepresentation G n} {W : Submodule k (n → k)}
    (hW : ρ.IsSimpleStableSubspace W) (D : StableSubspaceRepresentation ρ W) :
    D.representation.IsIrreducible := by
  have hn : Nontrivial (Fin D.dimension → k) := by
    by_contra h
    have : Subsingleton (Fin D.dimension → k) := not_nontrivial_iff_subsingleton.mp h
    apply hW.2.1
    rw [← D.range_eq]
    apply LinearMap.range_eq_bot.mpr
    apply LinearMap.ext
    intro v
    have hv : v = 0 := Subsingleton.elim _ _
    rw [hv, map_zero, LinearMap.zero_apply]
  refine ⟨hn, ?_⟩
  intro U hU
  have hmap := hU.map D.intertwines
  have hle : U.map D.inclusion.mulVecLin ≤ W := by
    exact LinearMap.map_le_range.trans (le_of_eq D.range_eq)
  have hmapinj := Submodule.map_injective_of_injective D.injective
  rcases hW.2.2 _ hmap hle with h | h
  · left
    apply hmapinj
    simpa only [Submodule.map_bot] using h
  · right
    apply hmapinj
    simpa only [Submodule.map_top, D.range_eq] using h

/-- A supplied finite independent simple-subspace decomposition has actual
direct-sum coordinates. -/
theorem exists_directSum_coordinates_of_simple_decomposition [IsAffineHom G.X.hom]
    (ρ : MatrixRepresentation G n) {r : ℕ}
    (W : Fin r → Submodule k (n → k))
    (hW : ∀ i, ρ.IsSimpleStableSubspace (W i))
    (hind : iSupIndep W) (hspan : iSup W = ⊤) :
    ∃ (d : Fin r → ℕ) (τ : ∀ i, MatrixRepresentation G (Fin (d i)))
      (C : Matrix n (Σ i, Fin (d i)) k),
      (∀ i, (τ i).IsIrreducible) ∧ (directSum τ).Intertwines ρ C ∧
        Function.Bijective C.mulVecLin := by
  classical
  let D := fun i => (hW i).1.representationCoordinates
  let B := fun i => (D i).inclusion
  have hrange : (fun i => LinearMap.range (B i).mulVecLin) = W := by
    funext i
    exact (D i).range_eq
  refine ⟨(fun i => (D i).dimension), (fun i => (D i).representation),
    directSumMap (R := CommRingCat.of k) B, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hW i).isIrreducible_coordinates (D i)
  · exact intertwines_directSumMap B (fun i => (D i).intertwines)
  · apply directSumMap_injective B (fun i => (D i).injective)
    rwa [hrange]
  · apply directSumMap_surjective B
    rwa [hrange]

/-- A semisimple actual representation is a finite direct sum of irreducible
actual representations, up to a bijective actual intertwiner. -/
theorem IsSemisimple.exists_directSum_coordinates [IsAffineHom G.X.hom]
    {ρ : MatrixRepresentation G n} (hρ : ρ.IsSemisimple) :
    ∃ (r : ℕ) (d : Fin r → ℕ) (τ : ∀ i, MatrixRepresentation G (Fin (d i)))
      (C : Matrix n (Σ i, Fin (d i)) k),
      (∀ i, (τ i).IsIrreducible) ∧ (directSum τ).Intertwines ρ C ∧
        Function.Bijective C.mulVecLin := by
  obtain ⟨r, W, hW, hind, hspan⟩ :=
    AffineSemisimpleModules.exists_finite_simple_decomposition ρ hρ
  obtain ⟨d, τ, C, hτ, hC, hbij⟩ :=
    exists_directSum_coordinates_of_simple_decomposition ρ W hW hind hspan
  exact ⟨r, d, τ, C, hτ, hC, hbij⟩

end Langlands.GroupScheme.MatrixRepresentation

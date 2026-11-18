import Langlands.GroupScheme.Rational.FiniteIndexPolynomialVanishing
import Langlands.GroupScheme.AffinePointTopologicalGroup
import Langlands.GroupScheme.AffinePolarCompact
import Langlands.GroupScheme.Reductive.SelfAdjointRealizationProof
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Compact real points of connected reductive groups are connected (Borel–Tits 14.3) -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme.GeneralLinear
open Langlands.Group.CompactMatrixZariski

namespace Langlands.GroupScheme.RealCompactPoints

variable (G : GroupScheme (Spec (CommRingCat.of ℝ))) [IsAffine G.X.left]

local instance : TopologicalSpace (G.affinePoints (CommAlgCat.of ℝ ℝ)) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of ℝ ℝ)

local instance : IsTopologicalGroup (G.affinePoints (CommAlgCat.of ℝ ℝ)) :=
  affinePointsIsTopologicalGroup G (CommAlgCat.of ℝ ℝ)

/-- If the real points of a connected reductive group over `ℝ` are compact and locally
connected, they are connected. -/
theorem connectedSpace_of_compactSpace (hG : IsConnectedReductive G)
    [LocallyConnectedSpace (G.affinePoints (CommAlgCat.of ℝ ℝ))]
    [CompactSpace (G.affinePoints (CommAlgCat.of ℝ ℝ))] :
    ConnectedSpace (G.affinePoints (CommAlgCat.of ℝ ℝ)) := by
  obtain ⟨d, ρ, hρ, -⟩ :=
    SelfAdjointRealization.connectedReductiveSelfAdjointRealizationStatement.{0} ℝ G hG
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  set r := ρ.affineMatrix (CommAlgCat.of ℝ ℝ)
  have hemb : IsClosedEmbedding r := ρ.isClosedEmbedding_affineMatrix _ hρ
  let H : Subgroup (G.affinePoints (CommAlgCat.of ℝ ℝ)) := Subgroup.connectedComponentOfOne _
  have hHset : (H : Set (G.affinePoints (CommAlgCat.of ℝ ℝ))) = connectedComponent 1 := rfl
  have hHopen : IsOpen (H : Set (G.affinePoints (CommAlgCat.of ℝ ℝ))) := by
    rw [hHset]
    exact isOpen_connectedComponent
  have : Finite (G.affinePoints (CommAlgCat.of ℝ ℝ) ⧸ H) :=
    Subgroup.quotient_finite_of_isOpen H hHopen
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let C : Subgroup (GL (Fin d) ℝ) := H.map r
  have hC : IsCompact (C : Set (GL (Fin d) ℝ)) := by
    rw [Subgroup.coe_map, hHset]
    exact isClosed_connectedComponent.isCompact.image hemb.continuous
  have hall : ∀ g : G.affinePoints (CommAlgCat.of ℝ ℝ), g ∈ H := by
    intro g
    by_contra hg
    have hrg : r g ∉ C := by
      rintro ⟨h, hh, he⟩
      exact hg (hemb.injective he ▸ hh)
    obtain ⟨p, hp₀, hp₁⟩ := exists_polynomial_separating C hC hrg
    exact hp₁ (ρ.eval_eq_zero_of_finiteIndex hG H p (fun h hh => hp₀ _ ⟨h, hh, rfl⟩) g)
  rw [connectedSpace_iff_connectedComponent]
  exact ⟨1, Set.eq_univ_of_forall fun g => hall g⟩

end Langlands.GroupScheme.RealCompactPoints

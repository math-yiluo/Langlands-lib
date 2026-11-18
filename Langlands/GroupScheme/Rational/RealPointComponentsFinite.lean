import Langlands.GroupScheme.Reductive.SelfAdjointRealizationProof
import Langlands.GroupScheme.AffinePolarCompact
import Langlands.GroupScheme.AffinePointRingPointComparison
import Langlands.GroupScheme.SmoothAffinePointLieGroup
import Langlands.Group.AlgebraicPolar
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof

/-! # Finitely many components of real points of connected reductive groups -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj Matrix ComplexOrder

namespace Langlands.Group.AlgebraicPolar

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type} [Fintype n] [DecidableEq n]

/-- The spectral positive powers depend continuously on the real exponent. -/
theorem continuous_positivePower (g : GL n 𝕜) (hg : g.val.PosDef) :
    Continuous (fun t : ℝ => positivePower g hg t) := by
  have hx := hg.eigenvalues_pos
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun t : ℝ =>
      ((Unitary.toUnits hg.isHermitian.eigenvectorUnitary : GL n 𝕜) *
        AlgebraicMatrixPowers.diagonalPower hg.isHermitian.eigenvalues hx t *
        (Unitary.toUnits hg.isHermitian.eigenvectorUnitary : GL n 𝕜)⁻¹).val
    simp only [Units.val_mul, AlgebraicMatrixPowers.diagonalPower_val]
    refine (continuous_const.mul (Continuous.matrix_diagonal ?_)).mul continuous_const
    refine continuous_pi fun i => ?_
    exact RCLike.continuous_ofReal.comp
      (continuous_const.rpow continuous_id fun _ => Or.inl (hx i).ne')
  · change Continuous fun t : ℝ =>
      (((Unitary.toUnits hg.isHermitian.eigenvectorUnitary : GL n 𝕜) *
        AlgebraicMatrixPowers.diagonalPower hg.isHermitian.eigenvalues hx t *
        (Unitary.toUnits hg.isHermitian.eigenvectorUnitary : GL n 𝕜)⁻¹)⁻¹).val
    simp only [mul_inv_rev, inv_inv, Units.val_mul,
      AlgebraicMatrixPowers.diagonalPower_inv_val]
    refine continuous_const.mul ((Continuous.matrix_diagonal (n := n) ?_).mul continuous_const)
    refine continuous_pi fun i => ?_
    refine (RCLike.continuous_ofReal.comp
      (continuous_const.rpow continuous_id fun _ => Or.inl (hx i).ne')).inv₀ fun t => ?_
    exact RCLike.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (hx i) t).ne'

/-- The exponent zero gives the identity. -/
theorem positivePower_zero (g : GL n 𝕜) (hg : g.val.PosDef) :
    positivePower g hg 0 = 1 :=
  Langlands.Group.FormSelfAdjointMean.positivePower_zero g hg

end Langlands.Group.AlgebraicPolar

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.AlgebraicGeometry.PointManifold
open Langlands.Group.AlgebraicPolar

namespace RealPointComponents

variable (G : GroupScheme (Spec (CommRingCat.of ℝ))) [IsAffine G.X.left]

local instance : TopologicalSpace (G.affinePoints (CommAlgCat.of ℝ ℝ)) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of ℝ ℝ)

/-- For a closed matrix representation with adjoint-stable real image, every real point is
joined by a continuous path of real points to a point of the unitary inverse image. -/
theorem exists_unitary_mem_connectedComponent {d : ℕ} (ρ : MatrixRepresentation G (Fin d))
    (hρ : IsClosedSubgroup ρ)
    (hstar : ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of ℝ ℝ)).range,
      star q ∈ (ρ.affineMatrix (CommAlgCat.of ℝ ℝ)).range)
    (g : G.affinePoints (CommAlgCat.of ℝ ℝ)) :
    ∃ a ∈ ρ.affineUnitarySubgroup (S := ℝ),
      G.affinePointsRingPointHomeomorph (CommAlgCat.of ℝ ℝ) g ∈
        connectedComponent (G.affinePointsRingPointHomeomorph (CommAlgCat.of ℝ ℝ) a) := by
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  set e := G.affinePointsRingPointHomeomorph (CommAlgCat.of ℝ ℝ)
  set r := ρ.affineMatrix (CommAlgCat.of ℝ ℝ)
  have hemb : IsClosedEmbedding r := ρ.isClosedEmbedding_affineMatrix _ hρ
  obtain ⟨a, haK, hP⟩ := ρ.exists_affineUnitary_right_quotient_posDef (S := ℝ) hρ hstar g
  refine ⟨a, haK, ?_⟩
  set P := r (g * a⁻¹)
  let f : ℝ → GL (Fin d) ℝ := fun t => positivePower (𝕜 := ℝ) P hP t * r a
  have hfmem : ∀ t, f t ∈ r.range := fun t =>
    r.range.mul_mem
      (positivePower_mem r.range (ρ.affineMatrix_range_isPolynomiallyDefined ℝ) P hP
        ⟨_, rfl⟩ t) ⟨a, rfl⟩
  choose h hh using hfmem
  have hfc : Continuous f := (continuous_positivePower P hP).mul continuous_const
  have hhc : Continuous h := by
    rw [hemb.isEmbedding.continuous_iff]
    convert hfc using 1
    funext t
    exact hh t
  have h0 : h 0 = a := hemb.injective (by rw [hh]; simp [f, positivePower_zero])
  have h1 : h 1 = g := hemb.injective (by
    rw [hh]
    simp only [f, positivePower_one, P, ← map_mul, inv_mul_cancel_right])
  have hconn := (isPreconnected_range (e.continuous.comp hhc)).subset_connectedComponent
    (x := e a) ⟨0, by simp [h0]⟩
  exact hconn ⟨1, by simp [h1]⟩

end RealPointComponents

set_option linter.defProp false in
/-- **Milne, Corollary 25.55.** The real points of a connected reductive group over `ℝ`, with
the evaluation topology, have only finitely many connected components. -/
@[instance_reducible]
def finite_connectedComponents_of_isConnectedReductive
    (G : GroupScheme (Spec (CommRingCat.of ℝ))) [IsAffine G.X.left]
    (hG : IsConnectedReductive G) :
    Finite (ConnectedComponents (RingPoint ℝ G.X ℝ)) := by
  obtain ⟨n, hn⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    G.X.left _ G.X.hom hG.smooth hG.connectedSpace
  let := realSmoothAffineChartedSpace G.X n hn
  have : LocallyConnectedSpace (RingPoint ℝ G.X ℝ) :=
    ChartedSpace.locallyConnectedSpace (Fin n → ℝ) _
  obtain ⟨d, ρ, hρ, hstar⟩ :=
    SelfAdjointRealization.connectedReductiveSelfAdjointRealizationStatement.{0} ℝ G hG
  let : TopologicalSpace (G.affinePoints (CommAlgCat.of ℝ ℝ)) :=
    G.affinePointsTopologicalSpace (CommAlgCat.of ℝ ℝ)
  set e := G.affinePointsRingPointHomeomorph (CommAlgCat.of ℝ ℝ)
  set K : Set (G.affinePoints (CommAlgCat.of ℝ ℝ)) :=
    (ρ.affineUnitarySubgroup (S := ℝ) : Set (G.affinePoints (CommAlgCat.of ℝ ℝ)))
  have hK : IsCompact K := ρ.isCompact_affineUnitarySubgroup (S := ℝ) hρ
  have himage : IsCompact
      ((fun x => (e x : ConnectedComponents (RingPoint ℝ G.X ℝ))) '' K) :=
    hK.image (ConnectedComponents.continuous_coe.comp e.continuous)
  have huniv : (fun x => (e x : ConnectedComponents (RingPoint ℝ G.X ℝ))) '' K =
      Set.univ := by
    refine Set.eq_univ_of_forall fun c => ?_
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨a, haK, ha⟩ :=
      RealPointComponents.exists_unitary_mem_connectedComponent G ρ hρ hstar (e.symm x)
    refine ⟨a, haK, ?_⟩
    rw [Homeomorph.apply_symm_apply] at ha
    exact (ConnectedComponents.coe_eq_coe'.mpr ha).symm
  have hfin := himage.finite_of_discrete
  rw [huniv] at hfin
  exact Set.finite_univ_iff.mp hfin

end Langlands.GroupScheme

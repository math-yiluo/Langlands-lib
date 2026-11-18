import Langlands.GroupScheme.Rational.RealPolarEigenvalueBound
import Langlands.GroupScheme.AffinePolarCompact
import Langlands.GroupScheme.Reductive.SelfAdjointRealizationProof
import Langlands.GroupScheme.GaloisPointRational

/-! # Compactness of real points from bounded torus factors -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.RealPolar

variable {n : Type} [Fintype n] [DecidableEq n]

/-- A positive definite invertible matrix such that every nonnegative eigenvalue of it and of
its inverse is at most one is the identity. -/
theorem posDef_eq_one {P : GL n ℝ} (hP : (P : Matrix n n ℝ).PosDef)
    (h₁ : ∀ (ev : ℝ) (v : n → ℝ), v ≠ 0 → 0 ≤ ev → (P : Matrix n n ℝ) *ᵥ v = ev • v → ev ≤ 1)
    (h₂ : ∀ (ev : ℝ) (v : n → ℝ), v ≠ 0 → 0 ≤ ev →
      ((P⁻¹ : GL n ℝ) : Matrix n n ℝ) *ᵥ v = ev • v → ev ≤ 1) :
    P = 1 := by
  have hH := hP.isHermitian
  have hev : ∀ i, hH.eigenvalues i = 1 := by
    intro i
    have hpos := hP.eigenvalues_pos i
    have hv : (⇑(hH.eigenvectorBasis i) : n → ℝ) ≠ 0 := by
      intro h0
      have := (hH.eigenvectorBasis).orthonormal.ne_zero i
      apply this
      ext j
      exact congrFun h0 j
    have hPv := hH.mulVec_eigenvectorBasis i
    have hle := h₁ _ _ hv hpos.le hPv
    have hinv : ((P⁻¹ : GL n ℝ) : Matrix n n ℝ) *ᵥ ⇑(hH.eigenvectorBasis i) =
        (hH.eigenvalues i)⁻¹ • ⇑(hH.eigenvectorBasis i) := by
      have hback : ((P⁻¹ : GL n ℝ) : Matrix n n ℝ) *ᵥ ((P : Matrix n n ℝ) *ᵥ
          ⇑(hH.eigenvectorBasis i)) = ⇑(hH.eigenvectorBasis i) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
      rw [hPv, Matrix.mulVec_smul] at hback
      calc ((P⁻¹ : GL n ℝ) : Matrix n n ℝ) *ᵥ ⇑(hH.eigenvectorBasis i)
          = (hH.eigenvalues i)⁻¹ • (hH.eigenvalues i •
              ((P⁻¹ : GL n ℝ) : Matrix n n ℝ) *ᵥ ⇑(hH.eigenvectorBasis i)) := by
            rw [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
        _ = (hH.eigenvalues i)⁻¹ • ⇑(hH.eigenvectorBasis i) := by rw [hback]
    have hge := h₂ _ _ hv (inv_nonneg.mpr hpos.le) hinv
    rw [inv_le_one₀ hpos] at hge
    linarith
  apply Units.ext
  rw [Units.val_one, hH.spectral_theorem]
  have hd : (RCLike.ofReal ∘ hH.eigenvalues : n → ℝ) = fun _ => 1 :=
    funext fun i => by simp [hev i]
  rw [hd, Matrix.diagonal_one, map_one]

/-- If every closed torus of a connected reductive group over `ℝ` has bounded matrices in every
representation, then the real points of the group are compact. -/
theorem compactSpace_of_torusBound (G : GroupScheme (Spec (CommRingCat.of ℝ)))
    [IsAffine G.X.left] (hG : IsConnectedReductive G)
    (hbound : ∀ (d : ℕ) (ρ : MatrixRepresentation G (Fin d))
      (T : CommGroupScheme (Spec (CommRingCat.of ℝ))) (i : T.toGrp ⟶ G),
      IsTorus T.toGrp → IsClosedSubgroup i → ∃ α : ℝ, ∀ (s : rationalPoints T.toGrp)
        (j l : Fin d), |(ρ.rationalMatrix (rationalPoints.map i s) :
          Matrix (Fin d) (Fin d) ℝ) j l| ≤ α) :
    @CompactSpace (G.affinePoints (CommAlgCat.of ℝ ℝ))
      (G.affinePointsTopologicalSpace (CommAlgCat.of ℝ ℝ)) := by
  let : TopologicalSpace (G.affinePoints (CommAlgCat.of ℝ ℝ)) :=
    G.affinePointsTopologicalSpace (CommAlgCat.of ℝ ℝ)
  obtain ⟨d, ρ, hρ, hstar⟩ :=
    SelfAdjointRealization.connectedReductiveSelfAdjointRealizationStatement.{0} ℝ G hG
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  set r := ρ.affineMatrix (CommAlgCat.of ℝ ℝ)
  have hemb : IsClosedEmbedding r := ρ.isClosedEmbedding_affineMatrix _ hρ
  have hK := ρ.isCompact_affineUnitarySubgroup (S := ℝ) hρ
  have heig : ∀ (h : G.affinePoints (CommAlgCat.of ℝ ℝ)) (ev : ℝ) (v : Fin d → ℝ), v ≠ 0 →
      0 ≤ ev → ((r h : GL (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ) *ᵥ v = ev • v → ev ≤ 1 := by
    intro h ev v hv hev hhv
    have hx : ρ.rationalMatrix ((GaloisPointComparison.rationalCoeffEquiv ℝ G).symm h) = r h := by
      rw [Langlands.Plancherel.rationalMatrix_eq_affineMatrix,
        ← GaloisPointComparison.rationalCoeffEquiv_eq, MulEquiv.apply_symm_apply]
    exact eigenvalue_le_one ρ (hbound d ρ) _ hev hv (by rw [hx]; exact hhv)
  have hall : ∀ g : G.affinePoints (CommAlgCat.of ℝ ℝ), g ∈ ρ.affineUnitarySubgroup (S := ℝ) := by
    intro g
    obtain ⟨a, haK, hP⟩ := ρ.exists_affineUnitary_right_quotient_posDef (S := ℝ) hρ hstar g
    have h1 : r (g * a⁻¹) = 1 := posDef_eq_one hP (heig _)
      (fun ev v hv hev hh => heig (g * a⁻¹)⁻¹ ev v hv hev (by rwa [map_inv]))
    have hga : g * a⁻¹ = 1 := hemb.injective (by rw [h1, map_one])
    rw [mul_inv_eq_one] at hga
    rw [hga]
    exact haK
  refine ⟨?_⟩
  have huniv : (ρ.affineUnitarySubgroup (S := ℝ) : Set (G.affinePoints (CommAlgCat.of ℝ ℝ))) =
      Set.univ := Set.eq_univ_of_forall hall
  rw [← huniv]
  exact hK

end Langlands.GroupScheme.RealPolar

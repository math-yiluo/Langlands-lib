import Langlands.GroupScheme.MatrixRepresentation.NormalOrbitEigenlines
import Langlands.GroupScheme.MatrixRepresentation.NormalKernelTensor
import Langlands.GroupScheme.AffineQuotientReduction

/-! # Exact kernels for smooth affine groups over algebraically closed fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffineQuotient

open MatrixRepresentation

/-- Every closed normal subgroup of a smooth affine algebraic group over an
algebraically closed field is the scheme-theoretic kernel of a finite matrix
representation, including on nonreduced scheme tests. -/
theorem smoothNormalKernel : SmoothNormalKernelInput.{u} := by
  intro k _ _ G _ _ _ H i hc hN
  classical
  have : IsClosedImmersion i.hom.hom.left := hc
  have : IsAffineHom H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k _ G.X.hom
  obtain ⟨n, j, ρ, hline⟩ := Chevalley.exists_line_stabilizer k G H i hc
  obtain ⟨d, B, C, hCB, hcols, hstable, s₀, hs₀⟩ :=
    ρ.exists_rationalOrbit_coordinates j
  let σ := restrictCoordinates ρ B C hCB hstable
  have hfixed : ((ρ.tensor σ.dual).restrict i).IsFixedVector
      (Pi.single (j, s₀) 1) := by
    apply isFixedVector_tensor_single
    intro T h
    have he : ∀ s, ∃ a : Γ(T.left, ⊤)ˣ,
        (ρ.pointMatrix T (h ≫ i.hom.hom) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T.left, ⊤)) *ᵥ
            (fun r => scalarMap T (B r s)) =
          (a : Γ(T.left, ⊤)) • (fun r => scalarMap T (B r s)) := by
      intro s
      simpa only [pointMatrix_restrict] using
        normal_rationalOrbit_column_eigenvector ρ i hN j
          (fun T x hx => (hline T x).mp hx) (hcols s) T h
    choose a ha using he
    have hdiag : (σ.pointMatrix T (h ≫ i.hom.hom) :
        Matrix (Fin d) (Fin d) Γ(T.left, ⊤)) =
          Matrix.diagonal (fun s => (a s : Γ(T.left, ⊤))) :=
      restrictCoordinates_eq_diagonal_of_column_eigenvectors
        ρ B C hCB hstable T (h ≫ i.hom.hom) a ha
    refine ⟨a s₀, ?_,
      dual_pointMatrix_mulVec_single_of_diagonal σ T (h ≫ i.hom.hom) a hdiag s₀⟩
    have hs : (fun r => scalarMap T (B r s₀)) = Pi.single j 1 := by
      change (fun r => scalarMap T ((fun r => B r s₀) r)) = _
      rw [hs₀]
      exact scalarMap_single T j
    simpa only [hs] using ha s₀
  let D := normalFixedSubrepresentation (ρ.tensor σ.dual) i hN
  refine ⟨D.dimension, D.representation, D.range_kernel_eq hfixed ?_⟩
  exact mem_range_of_tensor_fixes_single ρ σ.dual i j s₀
    (fun T x hx => (hline T x).mpr hx)

end Langlands.GroupScheme.AffineQuotient

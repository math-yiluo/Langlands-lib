import Langlands.Global.ArchimedeanBlockEvaluationDifferential

/-! # Local parabolic curves with prescribed upper triangular tangent -/

noncomputable section

open scoped Classical Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanCompactBlocks

open _root_.Langlands.Archimedean GeneralLinear

variable (𝕜 : Type) [RCLike 𝕜] {n : ℕ} (B : BlockShape n)

local notation "M" => Matrix (Fin n) (Fin n) 𝕜

private theorem upperTriangular_one_add_smul {X : M} (hX : X.IsUpperTriangular) (t : ℝ) :
    (1 + t • X).IsUpperTriangular := by
  intro i j hij
  change j < i at hij
  rw [Matrix.add_apply, Matrix.one_apply, ite_eq_right (ne_of_gt hij), Matrix.smul_apply, hX hij,
    smul_zero, add_zero]

/-- The matrix line through the identity in an upper triangular direction,
viewed in the block parabolic wherever its matrices are invertible. -/
def parabolicLine (X : M) (hX : X.IsUpperTriangular) (t : ℝ) : B.parabolic 𝕜 :=
  if h : IsUnit (1 + t • X) then
    ⟨h.unit, B.mem_parabolic_of_isUpperTriangular h.unit
      (by simpa only [IsUnit.unit_spec] using upperTriangular_one_add_smul 𝕜 hX t)⟩
  else 1

theorem parabolicLine_zero (X : M) (hX : X.IsUpperTriangular) :
    parabolicLine 𝕜 B X hX 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp [parabolicLine]

theorem parabolicLine_val_eventually (X : M) (hX : X.IsUpperTriangular) :
    ∀ᶠ t in 𝓝 (0 : ℝ), (parabolicLine 𝕜 B X hX t).val.val = 1 + t • X := by
  have hcont : Continuous (fun t : ℝ => 1 + t • X) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have h₀ : IsUnit (1 + (0 : ℝ) • X) := by simp
  have hmem : ∀ᶠ x in 𝓝 (1 + (0 : ℝ) • X), IsUnit x :=
    isOpen_setOf_isUnit_matrix.mem_nhds h₀
  exact (hcont.continuousAt.eventually hmem).mono fun t ht => by
    simp only [parabolicLine, dite_eq_left ht, IsUnit.unit_spec]

theorem parabolicLine_hasDerivAt (X : M) (hX : X.IsUpperTriangular) :
    HasDerivAt (fun t => (parabolicLine 𝕜 B X hX t).val.val) X 0 := by
  have h : HasDerivAt (fun t : ℝ => 1 + t • X) X 0 := by
    simpa only [one_smul] using ((hasDerivAt_id' (x := (0 : ℝ))).smul_const X).const_add (1 : M)
  exact h.congr_of_eventuallyEq (parabolicLine_val_eventually 𝕜 B X hX)

/-- Matrix extraction of the diagonal block is real continuous linear. -/
def localDiagonalBlock (i : Fin B.length) : M →L[ℝ] Matrix (Fin (B.size i)) (Fin (B.size i)) 𝕜 :=
  (show M →ₗ[ℝ] Matrix (Fin (B.size i)) (Fin (B.size i)) 𝕜 from
    { toFun := fun X a b => X (B.index i a) (B.index i b)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toContinuousLinearMap

theorem leviProjection_hasDerivAt (p : ℝ → B.parabolic 𝕜) (X : M)
    (hp : HasDerivAt (fun t => (p t).val.val) X 0) (i : Fin B.length) :
    HasDerivAt (fun t => (B.leviProjection 𝕜 (p t) i).val) (localDiagonalBlock 𝕜 B i X) 0 :=
  (localDiagonalBlock 𝕜 B i).hasFDerivAt.comp_hasDerivAt 0 hp

end Langlands.Global.ArchimedeanCompactBlocks

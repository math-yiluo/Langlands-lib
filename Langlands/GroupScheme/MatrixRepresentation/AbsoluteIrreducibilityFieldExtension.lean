import Langlands.GroupScheme.MatrixRepresentation.AffineOperatorDensity
import Langlands.GroupScheme.MatrixRepresentation.AffineCoefficientBaseChange
import Mathlib.Data.Matrix.Basis

/-! # Absolute irreducibility from scalar self-intertwiners -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Actual irreducibility after every extension field in the base universe. -/
def IsAbsolutelyIrreducible (ρ : MatrixRepresentation G n) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K],
    (ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).IsIrreducible

variable [IsAffineHom G.X.hom]

open AffineCoefficients AffineCoefficientAlgebra AffineCoefficientBaseChange

/-- Full original operator algebra forces irreducibility after every field extension. -/
theorem isIrreducible_baseChange_of_operatorAlgebra_eq_top
    {K : Type u} [Field K] [Algebra k K]
    (ρ : MatrixRepresentation G n) (hn : Nonempty n)
    (hfull : operatorAlgebra ρ = ⊤) :
    (ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).IsIrreducible := by
  classical
  let := hn
  refine ⟨inferInstance, fun W hW => ?_⟩
  by_cases hW0 : W = ⊥
  · exact Or.inl hW0
  right
  obtain ⟨v, hv, hv0⟩ := W.ne_bot_iff.mp hW0
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv0
  change v j ≠ 0 at hj
  have he (i : n) : Pi.single i (1 : K) ∈ W := by
    have hm : (Matrix.single i j (1 : k)).mulVecLin ∈ operatorAlgebra ρ := by
      rw [hfull]
      trivial
    have h := operator_preserves ρ hW hm v hv
    rw [extensionHom_mulVecLin] at h
    change ((Matrix.single i j (1 : k)).map (algebraMap k K)) *ᵥ v ∈ W at h
    simp only [Matrix.map_single, map_one, Matrix.single_mulVec_eq, one_mul] at h
    simpa only [smul_smul, inv_mul_cancel₀ hj, one_smul] using
      W.smul_mem (v j)⁻¹ h
  apply top_unique
  intro w _
  rw [← Finset.univ_sum_single w]
  apply W.sum_mem
  intro i _
  convert W.smul_mem (w i) (he i) using 1
  ext r
  by_cases hir : r = i <;> simp [hir]

/-- Milne 4.19(b), with actual all-affine-test self-intertwiners. -/
theorem IsIrreducible.baseChange_of_scalar_intertwiners
    {K : Type u} [Field K] [Algebra k K]
    {ρ : MatrixRepresentation G n} (hρ : ρ.IsIrreducible)
    (hscalar : ∀ C : Matrix n n k, Intertwines ρ ρ C →
      ∃ c : k, C = Matrix.scalar n c) :
    (ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).IsIrreducible :=
  isIrreducible_baseChange_of_operatorAlgebra_eq_top ρ hρ.nonempty_coordinates
    (operatorAlgebra_eq_top ρ hρ hscalar)

/-- A simple actual representation with scalar endomorphisms is absolutely irreducible. -/
theorem IsIrreducible.isAbsolutelyIrreducible_of_scalar_intertwiners
    {ρ : MatrixRepresentation G n} (hρ : ρ.IsIrreducible)
    (hscalar : ∀ C : Matrix n n k, Intertwines ρ ρ C →
      ∃ c : k, C = Matrix.scalar n c) : ρ.IsAbsolutelyIrreducible := by
  intro K _ _
  exact hρ.baseChange_of_scalar_intertwiners hscalar

end Langlands.GroupScheme.MatrixRepresentation

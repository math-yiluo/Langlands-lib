import Langlands.GroupScheme.MatrixRepresentation.ScalarExtensionStableSubspaces
import Langlands.GroupScheme.MatrixRepresentation.StableProjection
import Langlands.GroupScheme.MatrixRepresentation.StableComplements

/-! # Descent of actual equivariant projections and semisimplicity -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.LinearAlgebra.GaloisPiDescent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

private local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k K)))

/-- A projection onto an extended original subspace descends to an original
equivariant projection by a coefficient functional taking one to one. -/
theorem exists_equivariantProjection_of_baseChange (ρ : MatrixRepresentation G n)
    (V : Submodule k (n → k))
    (P₁ : Module.End K (n → K))
    (hP₁ : (ρ.baseChange (algebraBaseMap k K)).IsEquivariantProjection
      (scalarExtension (K := K) V) P₁) :
    ∃ P : Module.End k (n → k), ρ.IsEquivariantProjection V P := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k (one_ne_zero (α := K))
  let C := LinearMap.toMatrix' P₁
  let P : Module.End k (n → k) := Matrix.toLin' (C.map φ)
  have hmul (b : K) (a : k) : φ (b * algebraMap k K a) = φ b * a := by
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have hvec (v : n → k) : P v = fun i => φ (P₁ (extend v) i) := by
    change (C.map φ *ᵥ v) = _
    have hC : C *ᵥ extend (K := K) v = P₁ (extend v) :=
      LinearMap.toMatrix'_mulVec P₁ _
    rw [← hC]
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, extend_apply, map_sum, hmul]
  refine ⟨P, ?_, ?_, ?_⟩
  · have hi := hP₁.1.linearFunctional_descent φ
    change ρ.Intertwines ρ (LinearMap.toMatrix' (Matrix.toLin' (C.map φ)))
    rwa [LinearMap.toMatrix'_toLin']
  · intro v
    rw [hvec]
    exact linearFunctional_mem_scalarExtension (hP₁.2.1 (extend v)) φ
  · intro v hv
    rw [hvec, hP₁.2.2 (extend v) (Submodule.subset_span ⟨v, hv, rfl⟩)]
    ext i
    have hh := φ.map_smul (v i) (1 : K)
    simpa only [extend_apply, Algebra.smul_def, Algebra.algebraMap_self_apply,
      mul_one, hφ] using hh

/-- Actual representation semisimplicity descends along every field extension. -/
theorem isSemisimple_of_baseChange (ρ : MatrixRepresentation G n)
    (hρ : (ρ.baseChange (algebraBaseMap k K)).IsSemisimple) : ρ.IsSemisimple := by
  apply (isSemisimple_iff_exists_stable_complement ρ).mpr
  intro V hV
  have hV₁ := hV.scalarExtension (K := K)
  obtain ⟨W, hW, hVW⟩ :=
    (isSemisimple_iff_exists_stable_complement _).mp hρ (scalarExtension V) hV₁
  let P₁ := (scalarExtension (K := K) V).projection W hVW
  have hP₁ := isEquivariantProjection_of_isCompl hV₁ hW hVW
  obtain ⟨P, hP⟩ := exists_equivariantProjection_of_baseChange ρ V P₁ hP₁
  exact ⟨LinearMap.ker P, hP.stable_complement⟩


end Langlands.GroupScheme.MatrixRepresentation

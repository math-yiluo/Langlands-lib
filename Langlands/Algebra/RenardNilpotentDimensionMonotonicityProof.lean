import Langlands.Algebra.RenardNilpotentDimensionMonotonicityStatement
import Langlands.Algebra.RenardNilpotentDimensionTransportProof
import Mathlib.Algebra.Algebra.Prod
import Mathlib.LinearAlgebra.Prod

/-! Monotonicity of Renard's actual nilpotent-generated dimension maximum. -/

noncomputable section

universe u v

namespace Langlands.Renard

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
  {U : Type v} [AddCommGroup U] [Module ℂ U]

private theorem prodMapAlgHom_injective :
    Function.Injective (LinearMap.prodMapAlgHom ℂ V U) := by
  intro f g h
  apply Prod.ext
  · apply LinearMap.ext
    intro x
    exact congrArg Prod.fst (LinearMap.congr_fun h (x, 0))
  · apply LinearMap.ext
    intro y
    exact congrArg Prod.snd (LinearMap.congr_fun h (0, y))

variable [FiniteDimensional ℂ V] [FiniteDimensional ℂ U]

private theorem finrank_adjoin_prod_zero_le (l : ℕ)
    (a : Fin l → Module.End ℂ V) :
    Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
      Module.finrank ℂ (Algebra.adjoin ℂ
        (Set.range (fun i => (LinearMap.prodMapAlgHom ℂ V U)
          (a i, (0 : Module.End ℂ U))))) := by
  let b : Fin l → Module.End ℂ V × Module.End ℂ U := fun i => (a i, 0)
  let p := AlgHom.fst ℂ (Module.End ℂ V) (Module.End ℂ U)
  have h := Submodule.finrank_map_le p.toLinearMap
    (Algebra.adjoin ℂ (Set.range b)).toSubmodule
  rw [← Subalgebra.map_toSubmodule] at h
  change Module.finrank ℂ ((Algebra.adjoin ℂ (Set.range b)).map p) ≤
    Module.finrank ℂ (Algebra.adjoin ℂ (Set.range b)) at h
  rw [AlgHom.map_adjoin, ← Set.range_comp] at h
  change Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
    Module.finrank ℂ (Algebra.adjoin ℂ (Set.range b)) at h
  exact h.trans_eq (Langlands.CommutingDimension.finrank_adjoin_map
    ℂ b (LinearMap.prodMapAlgHom ℂ V U) prodMapAlgHom_injective)

/-- Extending an attaining tuple by zero on a product factor cannot lower the maximum. -/
theorem nilpotentGeneratedMaxDimension_le_prod (l : ℕ) :
    nilpotentGeneratedMaxDimension l V ≤ nilpotentGeneratedMaxDimension l (V × U) := by
  obtain ⟨a, hcomm, hnil, ha⟩ := nilpotentGeneratedMaxDimension_attained l V
  let b : Fin l → Module.End ℂ V × Module.End ℂ U := fun i => (a i, 0)
  let f := LinearMap.prodMapAlgHom ℂ V U
  have hbcomm (i j : Fin l) : Commute (b i) (b j) := by
    show b i * b j = b j * b i
    exact Prod.ext (hcomm i j).eq (by simp [b])
  have hbnil (i : Fin l) : IsNilpotent (b i) := by
    obtain ⟨n, hn⟩ := hnil i
    refine ⟨n + 1, ?_⟩
    change ((a i) ^ (n + 1), (0 : Module.End ℂ U) ^ (n + 1)) = (0, 0)
    simp [pow_succ, hn]
  rw [← ha]
  exact (finrank_adjoin_prod_zero_le (U := U) l a).trans
    (finrank_adjoin_le_nilpotentGeneratedMaxDimension l (V × U)
      (fun i => f (b i)) (fun i j => (hbcomm i j).map f)
      (fun i => (hbnil i).map f))

/-- The actual maximum is nondecreasing under a comparison of carrier dimensions. -/
theorem nilpotentGeneratedMaxDimension_mono_finrank
    (l : ℕ) {W : Type v} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (hVW : Module.finrank ℂ V ≤ Module.finrank ℂ W) :
    nilpotentGeneratedMaxDimension l V ≤ nilpotentGeneratedMaxDimension l W := by
  let C := Fin (Module.finrank ℂ W - Module.finrank ℂ V) → ℂ
  have hdim : Module.finrank ℂ (V × C) = Module.finrank ℂ W := by
    simp only [Module.finrank_prod, Module.finrank_fin_fun, C]
    omega
  let e : (V × C) ≃ₗ[ℂ] W := LinearEquiv.ofFinrankEq _ _ hdim
  exact (nilpotentGeneratedMaxDimension_le_prod (V := V) (U := C) l).trans_eq
    (nilpotentGeneratedMaxDimension_eq_of_linearEquiv l e)

/-- Renard C.I monotonicity, with independent universes and every boundary case. -/
theorem nilpotentDimensionMonotonicity : NilpotentDimensionMonotonicityStatement.{u, v} := by
  constructor
  · intro l V _ _ _ W _ _ _ hVW
    exact nilpotentGeneratedMaxDimension_mono_finrank l hVW
  · intro l k m hkm
    apply nilpotentGeneratedMaxDimension_mono_finrank
    simpa using hkm

end Langlands.Renard

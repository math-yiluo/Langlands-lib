import Langlands.Analysis.FiniteSpanIntegral
import Mathlib.Algebra.Algebra.Bilinear

/-! # Finite continuous spans under bilinear operations -/

noncomputable section
universe uX uV uW uU uI
set_option autoImplicit false

namespace Langlands.Analysis.FiniteSpanIntegral

open scoped BigOperators

variable {X : Type uX} [TopologicalSpace X]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {U : Type uU} [AddCommGroup U] [Module ℂ U]

/-- A finite sum with continuous scalar coefficients has finite continuous span. -/
theorem HasFiniteContinuousSpan.of_expansion {ι : Type uI} [Fintype ι]
    (v : ι → V) (c : ι → X → ℂ) (hc : ∀ i, Continuous (c i))
    {F : X → V} (hF : ∀ x, F x = ∑ i, c i x • v i) : HasFiniteContinuousSpan F := by
  refine ⟨(Submodule.fg_span (Set.finite_range v)).of_le (Submodule.span_le.mpr ?_), ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [hF x]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩))
  · intro l
    have heq : (fun x => l (F x)) = fun x => ∑ i, c i x * l (v i) := by
      funext x
      simp only [hF, map_sum, map_smul, smul_eq_mul]
    rw [heq]
    exact continuous_finsetSum _ (fun i _ => (hc i).mul continuous_const)

/-- Every finite continuous span has a finite continuous scalar expansion. -/
theorem HasFiniteContinuousSpan.exists_expansion {F : X → V}
    (hF : HasFiniteContinuousSpan F) :
    ∃ (d : ℕ) (v : Fin d → V) (c : Fin d → X → ℂ),
      (∀ i, Continuous (c i)) ∧ ∀ x, F x = ∑ i, c i x • v i := by
  classical
  let P := Submodule.span ℂ (Set.range F)
  let : Module.Finite ℂ P := Module.Finite.of_fg hF.1
  let b := Module.finBasis ℂ P
  let F' (x : X) : P := ⟨F x, Submodule.subset_span ⟨x, rfl⟩⟩
  have hq (i : Fin (Module.finrank ℂ P)) :
      ∃ q : Module.Dual ℂ V, q.comp P.subtype = b.coord i :=
    (b.coord i).exists_extend
  choose q hq using hq
  have hqF (i : Fin (Module.finrank ℂ P)) (x : X) :
      q i (F x) = b.repr (F' x) i := LinearMap.congr_fun (hq i) (F' x)
  refine ⟨Module.finrank ℂ P, (fun i => (b i : V)), (fun i x => q i (F x)),
    (fun i => hF.2 (q i)), ?_⟩
  intro x
  have h := congrArg P.subtype (b.sum_repr (F' x))
  simpa only [map_sum, map_smul, F', Submodule.subtype_apply, hqF] using h.symm

/-- Bilinear maps preserve finite continuous spans without carrier topologies. -/
theorem HasFiniteContinuousSpan.bilinear {F : X → V} {H : X → W}
    (hF : HasFiniteContinuousSpan F) (hH : HasFiniteContinuousSpan H)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] U) : HasFiniteContinuousSpan (fun x => B (F x) (H x)) := by
  obtain ⟨d, v, c, hc, hF⟩ := hF.exists_expansion
  obtain ⟨e, w, a, ha, hH⟩ := hH.exists_expansion
  refine HasFiniteContinuousSpan.of_expansion (fun ij : Fin d × Fin e => B (v ij.1) (w ij.2))
    (fun ij x => c ij.1 x * a ij.2 x) (fun ij => (hc ij.1).mul (ha ij.2)) ?_
  intro x
  rw [hF x, hH x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.smul_sum, smul_smul, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [mul_comm]

/-- Multiplication in a complex algebra preserves finite continuous spans. -/
theorem HasFiniteContinuousSpan.mul {A : Type uU} [Ring A] [Algebra ℂ A]
    {F H : X → A} (hF : HasFiniteContinuousSpan F) (hH : HasFiniteContinuousSpan H) :
    HasFiniteContinuousSpan (fun x => F x * H x) :=
  hF.bilinear hH (LinearMap.mul ℂ A)

end Langlands.Analysis.FiniteSpanIntegral

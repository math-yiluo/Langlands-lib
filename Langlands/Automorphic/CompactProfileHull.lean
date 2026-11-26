import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Common right-stable bounds for compact profiles -/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false

namespace Langlands.Automorphic

variable {G : Type*} [Group G] (H : Subgroup G)

/-- The profile of a function at `x` along the right action of `H`. -/
def rightCompactProfile (x : G) : (G → ℂ) →ₗ[ℂ] (H → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun k : H => x * k.val

/-- The common space of functions with all profiles in the supplied subspace. -/
def functionsWithCompactProfiles (E : Submodule ℂ (H → ℂ)) : Submodule ℂ (G → ℂ) :=
  ⨅ x : G, E.comap (rightCompactProfile H x)

@[simp]
theorem mem_functionsWithCompactProfiles (E : Submodule ℂ (H → ℂ)) (f : G → ℂ) :
    f ∈ functionsWithCompactProfiles H E ↔ ∀ x, rightCompactProfile H x f ∈ E := by
  simp only [functionsWithCompactProfiles, Submodule.mem_iInf, Submodule.mem_comap]

variable (E : Submodule ℂ (H → ℂ))

private def profileSpan : Submodule ℂ (H → ℂ) :=
  Submodule.span ℂ {p | ∃ f ∈ functionsWithCompactProfiles H E, ∃ x, rightCompactProfile H x f = p}

private theorem profileSpan_le : profileSpan H E ≤ E := by
  apply Submodule.span_le.mpr
  rintro _ ⟨f, hf, x, rfl⟩
  exact (mem_functionsWithCompactProfiles H E f).mp hf x

private def leftTranslate (k : H) : (H → ℂ) →ₗ[ℂ] (H → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun h => k * h

private theorem leftTranslate_mem (k : H) {p : H → ℂ} (hp : p ∈ profileSpan H E) :
    leftTranslate H k p ∈ profileSpan H E := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨f, hf, x, rfl⟩ := hp
    apply Submodule.subset_span
    refine ⟨f, hf, x * k.val, ?_⟩
    funext h
    exact congrArg f (mul_assoc x k.val h.val)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add p q _ _ hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq
  | smul c p _ hp => rw [map_smul]; exact Submodule.smul_mem _ c hp

/-- The span of right translates of the profiles of all functions with original profiles in `E`.
It gives a right-translation-stable profile bound for the entire family. -/
def rightCompactProfileHull : Submodule ℂ (H → ℂ) :=
  Submodule.span ℂ {p | ∃ (v : profileSpan H E) (k : H), (fun h : H => v.val (h * k)) = p}

/-- The new profile bound includes every actual profile in the original family. -/
theorem rightCompactProfile_mem_hull {f : G → ℂ} (hf : ∀ x, rightCompactProfile H x f ∈ E)
    (x : G) : rightCompactProfile H x f ∈ rightCompactProfileHull H E := by
  apply Submodule.subset_span
  refine ⟨⟨_, Submodule.subset_span ⟨f, (mem_functionsWithCompactProfiles H E f).mpr hf, x, rfl⟩⟩,
    1, ?_⟩
  funext h
  rw [mul_one]

/-- The hull is stable under every right translation on `H`. -/
theorem rightTranslate_mem_rightCompactProfileHull (k : H) {p : H → ℂ}
    (hp : p ∈ rightCompactProfileHull H E) :
    (fun h : H => p (h * k)) ∈ rightCompactProfileHull H E := by
  let R : (H → ℂ) →ₗ[ℂ] (H → ℂ) := LinearMap.funLeft ℂ ℂ fun h => h * k
  change R p ∈ rightCompactProfileHull H E
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨v, l, rfl⟩ := hp
    apply Submodule.subset_span
    refine ⟨v, k * l, ?_⟩
    funext h
    exact congrArg v.val (mul_assoc h k l).symm
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add p q _ _ hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq
  | smul c p _ hp => rw [map_smul]; exact Submodule.smul_mem _ c hp

instance finiteDimensional_rightCompactProfileHull [FiniteDimensional ℂ E] :
    FiniteDimensional ℂ (rightCompactProfileHull H E) := by
  let W := profileSpan H E
  let : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le (profileSpan_le H E)
  let L (h : H) : W →ₗ[ℂ] W :=
    ((leftTranslate H h).comp W.subtype).codRestrict W
      (fun v => leftTranslate_mem H E h v.property)
  let C : W →ₗ[ℂ] Module.Dual ℂ W →ₗ[ℂ] (H → ℂ) :=
    { toFun := fun v =>
        { toFun := fun l h => l (L h v)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_add' := by
        intro v w
        ext l h
        change l (L h (v + w)) = l (L h v) + l (L h w)
        rw [map_add, map_add]
      map_smul' := by
        intro c v
        ext l h
        change l (L h (c • v)) = c • l (L h v)
        rw [map_smul, map_smul] }
  let T : W ⊗[ℂ] Module.Dual ℂ W →ₗ[ℂ] (H → ℂ) := TensorProduct.lift C
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T)
  apply Submodule.span_le.mpr
  rintro _ ⟨v, k, rfl⟩
  let l : Module.Dual ℂ W := (LinearMap.proj k).comp W.subtype
  refine ⟨v ⊗ₜ[ℂ] l, ?_⟩
  change TensorProduct.lift C (v ⊗ₜ[ℂ] l) = _
  rw [TensorProduct.lift.tmul]
  rfl

end Langlands.Automorphic

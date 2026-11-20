import Langlands.Representation.FiniteVectors
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.Star
import Mathlib.RingTheory.Finiteness.Subalgebra

/-! # Dense scalar weights with finite left-translation orbit -/

noncomputable section
set_option autoImplicit false

namespace Langlands.CompactRepresentativeWeights

open Set
open FiniteVectors

universe uK uι

variable {K : Type uK} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- The left regular action uses the inverse in its argument. -/
def leftRegular : Representation ℂ K C(K, ℂ) where
  toFun g :=
    { toFun := fun f => ⟨fun k => f (g⁻¹ * k),
        f.continuous.comp (continuous_const.mul continuous_id)⟩
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
  map_one' := by ext f k; simp
  map_mul' g h := by
    ext f k
    change f ((g * h)⁻¹ * k) = f (h⁻¹ * (g⁻¹ * k))
    simp only [mul_inv_rev, mul_assoc]

@[simp]
theorem leftRegular_apply (g : K) (f : C(K, ℂ)) (k : K) :
    leftRegular g f k = f (g⁻¹ * k) := rfl

/-- Finite translation orbit is retained under pointwise multiplication. -/
theorem finite_mul {f h : C(K, ℂ)}
    (hf : IsFiniteVector leftRegular f) (hh : IsFiniteVector leftRegular h) :
    IsFiniteVector leftRegular (f * h) := by
  have : Module.Finite ℂ (orbitSpan leftRegular f) := hf
  have : Module.Finite ℂ (orbitSpan leftRegular h) := hh
  have hfg : (orbitSpan leftRegular f * orbitSpan leftRegular h).FG :=
    (Module.Finite.iff_fg.mp hf).mul (Module.Finite.iff_fg.mp hh)
  have : Module.Finite ℂ (orbitSpan leftRegular f * orbitSpan leftRegular h) :=
    (Submodule.fg_iff_finiteDimensional _).mp hfg
  apply Submodule.finiteDimensional_of_le (S₂ := orbitSpan leftRegular f * orbitSpan leftRegular h)
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  have he : leftRegular g (f * h) = leftRegular g f * leftRegular g h := by
    ext; rfl
  change leftRegular g (f * h) ∈ _
  rw [he]
  exact Submodule.mul_mem_mul (action_mem_orbitSpan leftRegular g f)
    (action_mem_orbitSpan leftRegular g h)

/-- Pointwise complex conjugation retains finite translation orbit. -/
theorem finite_star {f : C(K, ℂ)} (hf : IsFiniteVector leftRegular f) :
    IsFiniteVector leftRegular (star f) := by
  have : Module.Finite ℂ (orbitSpan leftRegular f) := hf
  let c : C(K, ℂ) →ₗ⋆[ℂ] C(K, ℂ) := (starLinearEquiv ℂ).toLinearMap
  have hc : ((orbitSpan leftRegular f).map c).FG :=
    (Module.Finite.iff_fg.mp hf).map c
  have : Module.Finite ℂ ((orbitSpan leftRegular f).map c) :=
    (Submodule.fg_iff_finiteDimensional _).mp hc
  apply Submodule.finiteDimensional_of_le (S₂ := (orbitSpan leftRegular f).map c)
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  exact ⟨leftRegular g f, action_mem_orbitSpan leftRegular g f, by ext; rfl⟩

theorem finite_one : IsFiniteVector (leftRegular (K := K)) 1 := by
  have : Module.Finite ℂ (ℂ ∙ (1 : C(K, ℂ))) := inferInstance
  apply Submodule.finiteDimensional_of_le (S₂ := ℂ ∙ (1 : C(K, ℂ)))
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  have he : leftRegular g (1 : C(K, ℂ)) = 1 := by ext; rfl
  change leftRegular g (1 : C(K, ℂ)) ∈ _
  rw [he]
  exact Submodule.mem_span_singleton_self _

/-- Continuous functions whose actual left-translation orbit spans a finite
dimensional space, with their pointwise star-algebra operations. -/
def finiteWeights : StarSubalgebra ℂ C(K, ℂ) where
  carrier := {f | IsFiniteVector leftRegular f}
  zero_mem' := isFiniteVector_zero leftRegular
  add_mem' := fun hf hh => hf.add hh
  one_mem' := finite_one
  mul_mem' := finite_mul
  algebraMap_mem' c := by
    change IsFiniteVector leftRegular (algebraMap ℂ C(K, ℂ) c)
    simpa only [Algebra.algebraMap_eq_smul_one] using finite_one.smul c
  star_mem' := finite_star

@[simp]
theorem mem_finiteWeights (f : C(K, ℂ)) :
    f ∈ finiteWeights ↔ IsFiniteVector leftRegular f := Iff.rfl

variable {ι : Type uι} [Fintype ι]
  (τ : Representation ℂ K (ι → ℂ))
  (hτ : ∀ v, Continuous (fun k => τ k v))

/-- Inverse matrix coefficients of an original finite dimensional representation. -/
def coefficientWeight (j : ι) (v : ι → ℂ) : C(K, ℂ) :=
  ⟨fun k => τ k⁻¹ v j, (continuous_apply j).comp ((hτ v).comp continuous_inv)⟩

/-- The coefficient weight map is an actual algebraic intertwiner. -/
def coefficientIntertwiner (j : ι) : τ.IntertwiningMap leftRegular where
  toLinearMap :=
    { toFun := coefficientWeight τ hτ j
      map_add' := by intros; ext; simp [coefficientWeight]
      map_smul' := by intros; ext; simp [coefficientWeight] }
  isIntertwining' g := by
    ext v k
    simp [coefficientWeight, mul_inv_rev, map_mul, Module.End.mul_apply]

/-- Every original matrix coefficient has finite left-translation orbit. -/
theorem coefficientWeight_mem (j : ι) (v : ι → ℂ) :
    coefficientWeight τ hτ j v ∈ finiteWeights := by
  change IsFiniteVector leftRegular (coefficientIntertwiner τ hτ j v)
  apply IsFiniteVector.map
  exact isFiniteVector_of_mem τ ⊤ (by trivial)

include hτ in
/-- A faithful continuous finite dimensional representation supplies separating
finite-orbit coefficients. -/
theorem finiteWeights_separatesPoints (hinj : Function.Injective τ) :
    (finiteWeights (K := K)).toSubalgebra.SeparatesPoints := by
  classical
  intro x y hxy
  have hne : ∃ (v : ι → ℂ) (j : ι), τ x⁻¹ v j ≠ τ y⁻¹ v j := by
    by_contra h
    push Not at h
    apply hxy
    apply inv_injective
    apply hinj
    apply LinearMap.ext
    intro v
    funext j
    exact h v j
  obtain ⟨v, j, hvj⟩ := hne
  exact ⟨coefficientWeight τ hτ j v,
    ⟨coefficientWeight τ hτ j v, coefficientWeight_mem τ hτ j v, rfl⟩, hvj⟩

include hτ in
/-- Stone-Weierstrass makes finite-orbit scalar weights uniformly dense. -/
theorem dense_finiteWeights [CompactSpace K] (hinj : Function.Injective τ) :
    Dense (finiteWeights (K := K) : Set C(K, ℂ)) := by
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (finiteWeights (K := K)) (finiteWeights_separatesPoints τ hτ hinj)
  rw [dense_iff_closure_eq]
  exact congrArg (fun A : StarSubalgebra ℂ C(K, ℂ) => (A : Set C(K, ℂ))) htop

/-- Finite left-translation scalar weights are uniformly dense on any compact
group with a supplied faithful continuous finite dimensional representation. -/
def CompactRepresentativeWeightsStatement : Prop :=
  ∀ (K : Type uK) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    (ι : Type uι) [Fintype ι] (τ : Representation ℂ K (ι → ℂ)),
    (∀ v, Continuous (fun k => τ k v)) → Function.Injective τ →
      Dense (finiteWeights (K := K) : Set C(K, ℂ))

theorem compactRepresentativeWeights :
    CompactRepresentativeWeightsStatement.{uK,uι} := by
  intro K _ _ _ _ ι _ τ hτ hinj
  exact dense_finiteWeights τ hτ hinj

end Langlands.CompactRepresentativeWeights

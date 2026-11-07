import Langlands.Global.HeckeCharacter
import Langlands.Representation.Twist.ContinuousCharacterProof

/-! # Finite ramification of actual Hecke characters -/

noncomputable section

open Filter Topology

namespace Langlands.Global.HeckeFunctionalEquation

universe u v

/-- A continuous complex character of a product is trivial on every single
factor outside a finite set. No local compactness hypothesis is required. -/
theorem exists_finset_trivial_mulSingle {ι : Type u} {G : ι → Type v}
    [DecidableEq ι] [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    (θ : (∀ i, G i) →ₜ* ℂˣ) :
    ∃ S : Finset ι, ∀ i ∉ S, ∀ x : G i, θ (Pi.mulSingle i x) = 1 := by
  classical
  let U : Set (∀ i, G i) := {x | ‖(θ x : ℂ) - 1‖ < (1 / 2 : ℝ)}
  have hU : U ∈ 𝓝 (1 : ∀ i, G i) := by
    apply (isOpen_lt ((Units.continuous_val.comp θ.continuous).sub
      continuous_const).norm continuous_const).mem_nhds
    simp
  simp only [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨S, t, ht, hSU⟩ := hU
  refine ⟨S, fun i hi x => ?_⟩
  apply Units.ext
  apply Langlands.complex_eq_one_of_forall_norm_pow_sub_one_lt
  intro n
  have hx : Pi.mulSingle i (x ^ n) ∈ U := by
    apply hSU
    intro j hj
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    simpa only [Pi.mulSingle_eq_of_ne hji, Pi.one_apply] using mem_of_mem_nhds (ht j)
  change ‖(θ (Pi.mulSingle i (x ^ n)) : ℂ) - 1‖ < (1 / 2 : ℝ) at hx
  simpa only [Pi.mulSingle_pow, map_pow, Units.val_pow_eq_pow_val] using hx

variable (K : Type u) [Field K] [NumberField K]

local instance : DecidableEq (FinitePlace K) := Classical.decEq _

/-- The literal inclusion of the product of all completed integer rings into
finite adeles. -/
def integralProductMap : (∀ v : FinitePlace K, v.adicCompletionIntegers K) →+*
    FiniteAdeles K where
  toFun := RestrictedProduct.structureMap _ _ Filter.cofinite
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem continuous_integralProductMap : Continuous (integralProductMap K) :=
  RestrictedProduct.isEmbedding_structureMap.continuous

/-- Insert the product of local integral units in the actual full idele group,
with infinite coordinates equal to one. -/
def integralUnitIdeles : (∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) →ₜ*
    Ideles K where
  toMonoidHom := (finiteIdelesInclusion K).toMonoidHom.comp
    ((Units.map (integralProductMap K).toMonoidHom).comp
      (ContinuousMulEquiv.piUnits.symm.toMonoidHom))
  continuous_toFun := (finiteIdelesInclusion K).continuous.comp
    (((continuous_integralProductMap K).units_map _).comp
      ContinuousMulEquiv.piUnits.symm.continuous)

/-- Inserting one local integral unit through the product agrees with the
published local idele insertion. -/
theorem integralUnitIdeles_mulSingle (v : FinitePlace K)
    (x : (v.adicCompletionIntegers K)ˣ) :
    integralUnitIdeles K (Pi.mulSingle v x) =
      finiteIdeleInclusion K v (Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom x) := by
  classical
  apply Units.ext
  apply Prod.ext
  · rfl
  · apply RestrictedProduct.ext
    intro w
    change (((Pi.mulSingle v x : ∀ w : FinitePlace K,
      (w.adicCompletionIntegers K)ˣ) w).val : FiniteCompletion K w) =
      (Pi.mulSingle v (x.val : FiniteCompletion K v) :
        ∀ w : FinitePlace K, FiniteCompletion K w) w
    by_cases h : w = v
    · subst w
      simp
    · simp [Pi.mulSingle_eq_of_ne h]

/-- Every actual Hecke character is unramified outside a finite set. -/
theorem exists_finset_isUnramifiedAt (χ : HeckeCharacter K) :
    ∃ S : Finset (FinitePlace K), ∀ v ∉ S, χ.IsUnramifiedAt v := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_trivial_mulSingle
    (χ.onIdeles.comp (integralUnitIdeles K))
  refine ⟨S, fun v hv x hx => ?_⟩
  let y : (v.adicCompletionIntegers K)ˣ :=
    { val := ⟨x.val, hx.1⟩
      inv := ⟨x.inv, hx.2⟩
      val_inv := Subtype.ext x.val_inv
      inv_val := Subtype.ext x.inv_val }
  have hy : Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom y = x := by
    apply Units.ext
    rfl
  have h := hS v hv y
  change χ.onIdeles (integralUnitIdeles K (Pi.mulSingle v y)) = 1 at h
  rw [integralUnitIdeles_mulSingle, hy] at h
  exact h

end Langlands.Global.HeckeFunctionalEquation

import Langlands.Global.Factors.HeckeLocalNontrivial
import Mathlib.Algebra.BigOperators.Pi

/-! # Actual local product formulas for adelic characters -/

noncomputable section

open Filter Topology

namespace Langlands.Global.HeckeFunctionalEquation

universe u v

/-- A continuous product character kills the entire subgroup whose controlled
coordinates equal one, including elements with infinitely many nontrivial coordinates. -/
theorem exists_finset_mul_kernel {ι : Type u} {G : ι → Type v}
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    (θ : (∀ i, G i) →ₜ* ℂˣ) :
    ∃ S : Finset ι, ∀ x : ∀ i, G i, (∀ i ∈ S, x i = 1) → θ x = 1 := by
  classical
  let U : Set (∀ i, G i) := {x | ‖(θ x : ℂ) - 1‖ < (1 / 2 : ℝ)}
  have hU : U ∈ 𝓝 (1 : ∀ i, G i) := by
    apply (isOpen_lt ((Units.continuous_val.comp θ.continuous).sub
      continuous_const).norm continuous_const).mem_nhds
    simp
  simp only [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨S, t, ht, hSU⟩ := hU
  refine ⟨S, fun x hx => ?_⟩
  apply Units.ext
  apply Langlands.complex_eq_one_of_forall_norm_pow_sub_one_lt
  intro n
  have hxn : x ^ n ∈ U := by
    apply hSU
    intro i hi
    simpa [hx i hi] using mem_of_mem_nhds (ht i)
  change ‖(θ (x ^ n) : ℂ) - 1‖ < (1 / 2 : ℝ) at hxn
  simpa only [map_pow, Units.val_pow_eq_pow_val] using hxn

/-- The additive analogue kills the entire subgroup with zero controlled coordinates. -/
theorem exists_finset_add_kernel {ι : Type u} {G : ι → Type v}
    [∀ i, AddGroup (G i)] [∀ i, TopologicalSpace (G i)]
    (θ : AddChar (∀ i, G i) Circle) (hθ : Continuous θ) :
    ∃ S : Finset ι, ∀ x : ∀ i, G i, (∀ i ∈ S, x i = 0) → θ x = 1 := by
  classical
  let U : Set (∀ i, G i) := {x | ‖(θ x : ℂ) - 1‖ < (1 / 2 : ℝ)}
  have hU : U ∈ 𝓝 (0 : ∀ i, G i) := by
    apply (isOpen_lt ((continuous_subtype_val.comp hθ).sub
      continuous_const).norm continuous_const).mem_nhds
    change ‖(θ 0 : ℂ) - 1‖ < (1 / 2 : ℝ)
    simp
  simp only [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨S, t, ht, hSU⟩ := hU
  refine ⟨S, fun x hx => ?_⟩
  apply Subtype.ext
  apply Langlands.complex_eq_one_of_forall_norm_pow_sub_one_lt
  intro n
  have hxn : n • x ∈ U := by
    apply hSU
    intro i hi
    simpa [hx i hi] using mem_of_mem_nhds (ht i)
  change ‖(θ (n • x) : ℂ) - 1‖ < (1 / 2 : ℝ) at hxn
  simpa only [AddChar.map_nsmul_eq_pow, Circle.coe_pow] using hxn

theorem addChar_sum {A M ι : Type*} [AddCommMonoid A] [CommMonoid M]
    (θ : AddChar A M) (S : Finset ι) (f : ι → A) :
    θ (∑ i ∈ S, f i) = ∏ i ∈ S, θ (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi, AddChar.map_add_eq_mul, ih]

variable {K : Type u} [Field K] [NumberField K]

local instance : DecidableEq (FinitePlace K) := Classical.decEq _
local instance : DecidableEq (InfinitePlace K) := Classical.decEq _

/-- A finite set controlling the global character on the full product of local integers. -/
def additiveIntegralControl (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K)) :
    Finset (FinitePlace K) :=
  Classical.choose (exists_finset_add_kernel
    (ψ.toAddChar.compAddMonoidHom (integralAdditiveInclusion K))
    (ψ.continuous_toFun.comp (continuous_integralAdditiveInclusion K)))

theorem additiveIntegralControl_spec
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (x : ∀ v : FinitePlace K, v.adicCompletionIntegers K)
    (hx : ∀ v ∈ additiveIntegralControl ψ, x v = 0) :
    ψ (integralAdditiveInclusion K x) = 1 :=
  Classical.choose_spec (exists_finset_add_kernel
    (ψ.toAddChar.compAddMonoidHom (integralAdditiveInclusion K))
    (ψ.continuous_toFun.comp (continuous_integralAdditiveInclusion K))) x hx

/-- Exactly the finitely many places where a finite adele is not integral. -/
def nonintegralPlaces (x : FiniteAdeles K) : Finset (FinitePlace K) :=
  (Filter.eventually_cofinite.mp x.2).toFinset

theorem integral_of_not_mem_nonintegralPlaces (x : FiniteAdeles K) (v : FinitePlace K)
    (hv : v ∉ nonintegralPlaces x) : x v ∈ v.adicCompletionIntegers K := by
  change ¬ v ∈ (Filter.eventually_cofinite.mp x.2).toFinset at hv
  rw [Set.Finite.mem_toFinset] at hv
  exact not_not.mp hv

/-- Keep a finite set of actual additive coordinates, with all others zero. -/
def finiteAdditivePartialSum (S : Finset (FinitePlace K)) (x : FiniteAdeles K) : Adeles K :=
  ∑ v ∈ S, finiteAdditiveInclusion K v (x v)

theorem finiteProjection_finiteAdditivePartialSum
    (S : Finset (FinitePlace K)) (x : FiniteAdeles K) (v : FinitePlace K) :
    finiteProjection K v (finiteAdditivePartialSum S x) =
      if v ∈ S then x v else 0 := by
  classical
  rw [finiteAdditivePartialSum, map_sum]
  change (∑ w ∈ S, (Pi.single w (x w)) v) = _
  by_cases hv : v ∈ S
  · simp only [hv, ↓reduceIte]
    rw [Finset.sum_eq_single v]
    · exact Pi.single_eq_same v (x v)
    · intro w _ hw
      exact Pi.single_eq_of_ne (Ne.symm hw) _
    · exact fun h => False.elim (h hv)
  · simp only [hv, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro w hw
    have hvw : v ≠ w := by
      intro h
      subst w
      exact hv hw
    exact Pi.single_eq_of_ne hvw _

theorem infiniteProjection_finiteAdditivePartialSum
    (S : Finset (FinitePlace K)) (x : FiniteAdeles K) (v : InfinitePlace K) :
    infiniteProjection K v (finiteAdditivePartialSum S x) = 0 := by
  rw [finiteAdditivePartialSum, map_sum]
  change (∑ w ∈ S, (0 : InfiniteCompletion K v)) = 0
  simp

/-- On a finite adele, the character is exactly a finite product of its actual
local restrictions; the set contains its integral control and all nonintegral places. -/
theorem finite_additive_product
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (x : FiniteAdeles K) (S : Finset (FinitePlace K))
    (hψ : additiveIntegralControl ψ ⊆ S) (hx : nonintegralPlaces x ⊆ S) :
    ψ (0, x) = ∏ v ∈ S, finiteAdditiveRestriction ψ v (x v) := by
  classical
  let r : ∀ v : FinitePlace K, v.adicCompletionIntegers K :=
    fun v => if hv : v ∈ S then 0 else
      ⟨x v, integral_of_not_mem_nonintegralPlaces x v (fun h => hv (hx h))⟩
  have hr : ψ (integralAdditiveInclusion K r) = 1 := by
    apply additiveIntegralControl_spec
    intro v hv
    simp [r, hψ hv]
  have hdecomp : (0, x) =
      finiteAdditivePartialSum S x + integralAdditiveInclusion K r := by
    apply Prod.ext
    · funext v
      change 0 = infiniteProjection K v (finiteAdditivePartialSum S x) + 0
      rw [infiniteProjection_finiteAdditivePartialSum, add_zero]
    · apply RestrictedProduct.ext
      intro v
      change x v = finiteProjection K v (finiteAdditivePartialSum S x) + (r v : _)
      rw [finiteProjection_finiteAdditivePartialSum]
      by_cases hv : v ∈ S <;> simp [r, hv]
  rw [hdecomp, AddChar.map_add_eq_mul, hr, mul_one]
  exact addChar_sum ψ.toAddChar S (fun v => finiteAdditiveInclusion K v (x v))

/-- The sum of all infinite single-coordinate inclusions is the actual
archimedean adele with zero finite part. -/
theorem infinite_additive_sum (x : InfiniteAdeles K) :
    (∑ v : InfinitePlace K, infiniteAdditiveInclusion K v (x v)) =
      (x, (0 : FiniteAdeles K)) := by
  classical
  change (∑ v : InfinitePlace K, (Pi.single v (x v), (0 : FiniteAdeles K))) = _
  rw [← prod_mk_sum]
  apply Prod.ext
  · exact Finset.univ_sum_single x
  · exact Finset.sum_const_zero

/-- The archimedean restriction is the finite product of its actual local
restrictions. -/
theorem infinite_additive_product
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K)) (x : InfiniteAdeles K) :
    ψ (x, (0 : FiniteAdeles K)) =
      ∏ v : InfinitePlace K, infiniteAdditiveRestriction ψ v (x v) := by
  rw [← infinite_additive_sum]
  exact addChar_sum ψ.toAddChar Finset.univ (fun v => infiniteAdditiveInclusion K v (x v))

/-- Every actual adele has the local product expansion at any finite set
containing the integral control and its nonintegral places. -/
theorem additive_product
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (x : Adeles K) (S : Finset (FinitePlace K))
    (hψ : additiveIntegralControl ψ ⊆ S) (hx : nonintegralPlaces x.2 ⊆ S) :
    ψ x = (∏ v : InfinitePlace K, infiniteAdditiveRestriction ψ v (x.1 v)) *
      ∏ v ∈ S, finiteAdditiveRestriction ψ v (x.2 v) := by
  have hdecomp : x = (x.1, (0 : FiniteAdeles K)) + ((0 : InfiniteAdeles K), x.2) := by
    apply Prod.ext
    · exact (add_zero x.1).symm
    · exact (zero_add x.2).symm
  calc
    ψ x = ψ ((x.1, (0 : FiniteAdeles K)) + ((0 : InfiniteAdeles K), x.2)) :=
      congrArg ψ hdecomp
    _ = ψ (x.1, (0 : FiniteAdeles K)) * ψ ((0 : InfiniteAdeles K), x.2) :=
      ψ.toAddChar.map_add_eq_mul _ _
    _ = _ := by
      rw [infinite_additive_product, finite_additive_product ψ x.2 S hψ hx]

set_option backward.isDefEq.respectTransparency false in
/-- Diagonal triviality gives the additive product formula on the original
number field, with the actual local restrictions and no self-duality premise. -/
theorem diagonal_additive_product
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (hdiag : ∀ a : K, ψ (diagonal K a) = 1)
    (a : K) (S : Finset (FinitePlace K))
    (hψ : additiveIntegralControl ψ ⊆ S)
    (ha : nonintegralPlaces (diagonal K a).2 ⊆ S) :
    (∏ v : InfinitePlace K,
      infiniteAdditiveRestriction ψ v (algebraMap K (InfiniteCompletion K v) a)) *
      (∏ v ∈ S,
        finiteAdditiveRestriction ψ v (algebraMap K (FiniteCompletion K v) a)) = 1 := by
  exact (additive_product ψ (diagonal K a) S hψ ha).symm.trans (hdiag a)

end Langlands.Global.HeckeFunctionalEquation

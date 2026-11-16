import Langlands.Global.RankinSelberg.SchwartzBruhatProof.Lattice
import Langlands.Global.RankinSelberg.EqualAnalyticFourierDominated
import Langlands.Global.Factors.HeckeConductorSupport
import Langlands.Global.Factors.HeckeLocalData
import Langlands.HarmonicAnalysis.PadicLatticeFourierProof

/-! # Duality of the finite-adelic lattices under a standard character

For a standard additive character `ψ` of `𝔸` let `ψ_f(t) = ψ(0, t)` on `𝔸_f`. With the
conductor divisor `n_ψ` of the local components of `ψ`, the annihilator of the lattice
`L_m = ∏_v π_v^(-m_v) 𝒪_v` under `(t, η) ↦ ψ_f(t η)` is `L_(n_ψ - m)`, and the annihilator
of `L_m^n` under `(u, η) ↦ ψ_f(∑_j u_j η_j)` is `L_(n_ψ - m)^n`. The character `ψ_f` is
trivial on `L_(n_ψ)`, hence locally constant.
-/

noncomputable section
universe u
open NumberField Langlands.Global.CompletionPadic Langlands.HarmonicAnalysis
open Langlands.Global.RankinSelbergGlobal.EqualAnalytic (finiteCharacter finiteAdele
  finiteCharacter_add norm_finiteCharacter)
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.SchwartzBruhatProof

variable {F : Type u} [Field F] [NumberField F]

section Character

variable (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)

/-- A standard additive character as a unitary additive character. -/
def standardUnitary : UnitaryAdditiveCharacter (Adeles F) where
  toFun x := ⟨ψ x, mem_sphere_zero_iff_norm.2 (hψ.2.2.2 x)⟩
  map_zero_eq_one' := Circle.ext (by simp)
  map_add_eq_mul' a b := Circle.ext (AddChar.map_add_eq_mul ψ a b)
  continuous_toFun := hψ.1.subtype_mk _
  nontrivial h := hψ.2.1 (by
    ext x
    have := congrArg (fun χ : AddChar (Adeles F) Circle => ((χ x : Circle) : ℂ)) h
    simp only [AddChar.one_apply, Circle.coe_one] at this
    rw [AddChar.one_apply]
    exact this)

theorem coe_standardUnitary_apply (x : Adeles F) :
    ((standardUnitary ψ hψ x : Circle) : ℂ) = ψ x := rfl

theorem standardUnitary_diagonal (k : F) : standardUnitary ψ hψ (diagonal F k) = 1 :=
  Circle.ext (by simpa [coe_standardUnitary_apply] using hψ.2.2.1 k)

/-- The local component of `ψ` at a finite place. -/
abbrev localComponent (v : FinitePlace F) :
    @UnitaryAdditiveCharacter (padicField v).Carrier _ (topologicalData v).topology :=
  HeckeFunctionalEquation.globalFiniteAdditiveComponent (standardUnitary ψ hψ)
    (standardUnitary_diagonal ψ hψ) v

theorem coe_localComponent_apply (v : FinitePlace F) (s : FiniteCompletion F v) :
    ((localComponent ψ hψ v s : Circle) : ℂ) =
      ψ (HeckeFunctionalEquation.finiteAdditiveInclusion F v s) := rfl

/-- The conductor divisor `n_ψ = (n(ψ_v))_v`. -/
def conductorDivisor : FinitePlace F →₀ ℤ :=
  HeckeFunctionalEquation.additiveConductorDivisor (standardUnitary ψ hψ)
    (standardUnitary_diagonal ψ hψ) (localComponent ψ hψ)
    (fun v => HeckeFunctionalEquation.isFiniteAdditiveComponent_globalFiniteAdditiveComponent
      _ _ v)
    (fun v => HeckeFunctionalEquation.realCompletionAdditiveScale (standardUnitary ψ hψ) v.2
      (HeckeFunctionalEquation.infiniteAdditiveRestriction_ne_one _
        (standardUnitary_diagonal ψ hψ) v.1))
    (fun v => HeckeFunctionalEquation.isRealAdditiveComponent_realCompletionAdditiveScale _ v.2
      _)
    (fun v => HeckeFunctionalEquation.complexCompletionAdditiveScale (standardUnitary ψ hψ) v.2
      (HeckeFunctionalEquation.infiniteAdditiveRestriction_ne_one _
        (standardUnitary_diagonal ψ hψ) v.1))
    (fun v =>
      HeckeFunctionalEquation.isComplexAdditiveComponent_complexCompletionAdditiveScale _ v.2 _)

theorem conductorDivisor_apply (v : FinitePlace F) :
    conductorDivisor ψ hψ v = (topologicalData v).additiveConductor (localComponent ψ hψ v) :=
  rfl

theorem finiteCharacter_zero : finiteCharacter F ψ 0 = 1 := by
  unfold finiteCharacter
  exact AddChar.map_zero_eq_one ψ

include hψ in
theorem continuous_finiteCharacter : Continuous (finiteCharacter F ψ) :=
  hψ.1.comp (continuous_const.prodMk continuous_id)

theorem finiteCharacter_sum {ι : Type*} (s : Finset ι) (f : ι → FiniteAdeles F) :
    finiteCharacter F ψ (∑ i ∈ s, f i) = ∏ i ∈ s, finiteCharacter F ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [finiteCharacter_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, finiteCharacter_add, ih]

/-- `ψ_f` on the image of a single local coordinate is the local component. -/
theorem finiteCharacter_inclusion (v : FinitePlace F) (s : FiniteCompletion F v) :
    finiteCharacter F ψ (HeckeFunctionalEquation.finiteAdditiveInclusion F v s).2 =
      ((localComponent ψ hψ v s : Circle) : ℂ) := by
  rw [coe_localComponent_apply]
  rfl

/-- `ψ_f` is the product of the local components over a large finite set of places. -/
theorem finiteCharacter_eq_prod (t : FiniteAdeles F) (S : Finset (FinitePlace F))
    (hS : HeckeFunctionalEquation.additiveIntegralControl (standardUnitary ψ hψ) ⊆ S)
    (ht : HeckeFunctionalEquation.nonintegralPlaces t ⊆ S) :
    finiteCharacter F ψ t = ∏ v ∈ S, ((localComponent ψ hψ v (t v) : Circle) : ℂ) := by
  have h := congrArg Circle.coeHom
    (HeckeFunctionalEquation.finite_additive_product (standardUnitary ψ hψ) t S hS ht)
  rw [map_prod] at h
  exact h

/-- **Lattice duality in `𝔸_f`**: `{η | ψ_f(L_m η) = 1} = L_(n_ψ - m)`. -/
theorem forall_finiteCharacter_eq_one_iff (m : FinitePlace F →₀ ℤ) (η : FiniteAdeles F) :
    (∀ t ∈ finiteLattice m, finiteCharacter F ψ (t * η) = 1) ↔
      η ∈ finiteLattice (conductorDivisor ψ hψ - m) := by
  classical
  constructor
  · intro h v
    rw [Finsupp.sub_apply, conductorDivisor_apply]
    refine ((topologicalData v).forall_mul_eq_one_iff_mem_additiveLattice
      (localComponent ψ hψ v) (m v) (η v)).mp fun s hs => ?_
    let t : FiniteAdeles F := (HeckeFunctionalEquation.finiteAdditiveInclusion F v s).2
    have hsingle : ∀ w, t w = (Pi.single v s : ∀ w, FiniteCompletion F w) w := fun w => rfl
    have ht : t ∈ finiteLattice m := by
      intro w
      rw [hsingle]
      by_cases hw : w = v
      · subst hw
        rw [Pi.single_eq_same]
        exact hs
      · rw [Pi.single_eq_of_ne hw]
        exact zero_mem _
    have h1 := h t ht
    have heq : t * η = (HeckeFunctionalEquation.finiteAdditiveInclusion F v (s * η v)).2 := by
      have := RestrictedProduct.single_mul
        (fun w : FinitePlace F => w.adicCompletionIntegers F) v s η
      exact this.symm
    rw [heq, finiteCharacter_inclusion ψ hψ] at h1
    exact Circle.ext (by simpa using h1)
  · intro hη t ht
    rw [finiteCharacter_eq_prod ψ hψ (t * η)
      (HeckeFunctionalEquation.additiveIntegralControl (standardUnitary ψ hψ) ∪
        HeckeFunctionalEquation.nonintegralPlaces (t * η))
      Finset.subset_union_left Finset.subset_union_right]
    refine Finset.prod_eq_one fun v _ => ?_
    have hv := hη v
    rw [Finsupp.sub_apply, conductorDivisor_apply] at hv
    have := ((topologicalData v).forall_mul_eq_one_iff_mem_additiveLattice
      (localComponent ψ hψ v) (m v) (η v)).mpr hv (t v) (ht v)
    rw [show (t * η) v = t v * η v from rfl, this]
    rfl

/-- `ψ_f` is trivial on `L_(n_ψ)`. -/
theorem finiteCharacter_eq_one_of_mem (t : FiniteAdeles F)
    (ht : t ∈ finiteLattice (conductorDivisor ψ hψ)) : finiteCharacter F ψ t = 1 := by
  have h1 : (1 : FiniteAdeles F) ∈ finiteLattice (conductorDivisor ψ hψ -
      conductorDivisor ψ hψ) := by
    rw [sub_self]
    intro v
    rw [Finsupp.coe_zero, Pi.zero_apply, Hecke.mem_additiveLattice_zero_iff]
    exact (v.adicCompletionIntegers F).one_mem
  have := (forall_finiteCharacter_eq_one_iff ψ hψ (conductorDivisor ψ hψ) 1).mpr h1 t ht
  rwa [mul_one] at this

include hψ in
theorem isLocallyConstant_finiteCharacter : IsLocallyConstant (finiteCharacter F ψ) :=
  isLocallyConstant_of_add_invariant (finiteLattice (conductorDivisor ψ hψ))
    (isOpen_finiteLattice _) fun x h hh => by
      rw [finiteCharacter_add, finiteCharacter_eq_one_of_mem ψ hψ h hh, mul_one]

variable (n : ℕ)

/-- **Lattice duality in `𝔸_f^n`**: the annihilator of `L_m^n` under
`(u, η) ↦ ψ_f(∑_j u_j η_j)` is `L_(n_ψ - m)^n`. -/
theorem forall_finiteCharacter_sum_eq_one_iff (m : FinitePlace F →₀ ℤ)
    (η : Fin n → FiniteAdeles F) :
    (∀ u ∈ latticeVec n m, finiteCharacter F ψ (∑ j, u j * η j) = 1) ↔
      η ∈ latticeVec n (conductorDivisor ψ hψ - m) := by
  classical
  rw [mem_latticeVec]
  constructor
  · intro h j
    refine (forall_finiteCharacter_eq_one_iff ψ hψ m (η j)).mp fun t ht => ?_
    have hu : (Pi.single j t : Fin n → FiniteAdeles F) ∈ latticeVec n m := by
      rw [mem_latticeVec]
      intro i
      by_cases hi : i = j
      · subst hi
        simpa using ht
      · simp only [Pi.single_eq_of_ne hi]
        exact zero_mem _
    have := h _ hu
    rwa [Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_eq_of_ne hi])
      (by simp), Pi.single_eq_same] at this
  · intro hη u hu
    rw [finiteCharacter_sum]
    exact Finset.prod_eq_one fun j _ =>
      (forall_finiteCharacter_eq_one_iff ψ hψ m (η j)).mpr (hη j) (u j)
        ((mem_latticeVec n).mp hu j)

end Character

end Langlands.Global.RankinSelbergGlobal.SchwartzBruhatProof

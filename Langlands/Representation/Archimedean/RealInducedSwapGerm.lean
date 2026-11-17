import Langlands.Representation.Archimedean.RealInducedSwapRegularization

/-!
# Target-valued regular families and specialization of inverses

An algebraic retraction supplies target-valued families at every parameter.
They agree with the actual generic shifted maps on the generic path.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean
namespace RealInducedSwapGerm

open Langlands.LocalFactor.Archimedean
open RealInducedSwapGeneric RealInducedSwapRegularizedFamily
open RealInducedSwapRegularization RealInducedSwapInverse
open RealBlockMultiplierAnalytic RealFiniteLayerRegularization
open RealCharacterInducedSwap RealCharacterInducedPushforward
open scoped Topology

section Algebra

variable {U V : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]

theorem weaklyAnalyticAt_neg {f : ℂ → V} (hf : IsWeaklyAnalyticAt f 0) :
    IsWeaklyAnalyticAt (fun z => f (-z)) 0 := by
  intro ℓ
  exact (hf ℓ).fun_comp_of_eq analyticAt_id.neg (neg_zero : -(0 : ℂ) = 0)

/-- Analyticity and finite-dimensional ranges specialize an eventual inverse
identity along any nontrivial path approaching zero. -/
theorem leftInverse_at_zero (T : ℂ → U →ₗ[ℂ] V) (R : ℂ → V →ₗ[ℂ] U)
    (hT : ∀ u, IsWeaklyAnalyticAt (fun z => T z u) 0)
    (hR : ∀ v, IsWeaklyAnalyticAt (fun z => R z v) 0)
    (hfinite : ∀ u, ∃ S : Submodule ℂ V,
      FiniteDimensional ℂ S ∧ ∀ z, T z u ∈ S)
    {L : Filter ℂ} [L.NeBot] (hL : L ≤ 𝓝 0)
    (hinv : ∀ᶠ z in L, Function.LeftInverse (R z) (T z)) :
    Function.LeftInverse (R 0) (T 0) := by
  intro u
  obtain ⟨S, hS, huS⟩ := hfinite u
  let := hS
  exact eq_of_weaklyAnalyticAt_eventuallyEq
    (weaklyAnalyticAt_apply R hR (hT u) S huS)
    (IsWeaklyAnalyticAt.const u 0) hL (hinv.mono fun _ hz => hz u)

end Algebra

variable (d e : ComplexCharacterData) (c : Choices)

/-- Either no division is needed, or one removed denominator has a cancelled
residue on the actual source induction subspace. -/
def Admissible : Prop :=
  totalOrder c = 0 ∨ (totalOrder c = 1 ∧ Cancels d e c)

/-- Use the raw analytic family in order zero and its simple quotient otherwise. -/
def regularMap (hc : Valid d e c) (z : ℂ) :
    KF 4 (source d e) →ₗ[ℂ] KF 4 (expanded e d) :=
  if totalOrder c = 0 then RealInducedSwapRegularizedFamily.rawMap d e c z
  else normalizedMap d e c hc z

theorem regularMap_analytic (hc : Valid d e c) (hreg : Admissible d e c)
    (f : KF 4 (source d e)) :
    IsWeaklyAnalyticAt (fun z => regularMap d e c hc z f) 0 := by
  unfold regularMap
  split_ifs with hzero
  · exact rawMap_analytic d e c hc f
  · rcases hreg with hreg | ⟨_, hcan⟩
    · exact (hzero hreg).elim
    · exact normalizedMap_analytic d e c hc hcan f

theorem regularMap_exists_finite_range (hc : Valid d e c)
    (f : KF 4 (source d e)) :
    ∃ S : Submodule ℂ (KF 4 (expanded e d)),
      FiniteDimensional ℂ S ∧ ∀ z, regularMap d e c hc z f ∈ S := by
  unfold regularMap
  split_ifs
  · exact rawMap_exists_finite_range d e c f
  · exact normalizedMap_exists_finite_range d e c hc f

theorem regularMap_eq_generic (hc : Valid d e c) (hreg : Admissible d e c)
    {z : ℂ} (hz : z ≠ 0) (hg : IsGenericShift d e z) :
    regularMap d e c hc z =
      RealInducedSwapShifted.rawMap d e (genericFourCrossings hg) := by
  unfold regularMap
  split_ifs with hzero
  · rw [rawMap_eq_scaled_generic d e c hc hz hg, hzero, pow_zero, one_smul]
  · rcases hreg with hreg | ⟨horder, _⟩
    · exact (hzero hreg).elim
    · exact normalizedMap_eq_generic d e c hc horder hz hg

/-- A fixed algebraic retraction of the target inclusion. It is the identity
on vectors already belonging to the actual target module. -/
def targetRetraction :
    KF 4 (expanded e d) →ₗ[ℂ] KF 4 (target d e) :=
  (Submodule.inclusion (source_le_expanded e d)).leftInverse

theorem targetRetraction_inclusion (f : KF 4 (target d e)) :
    targetRetraction d e (Submodule.inclusion (source_le_expanded e d) f) = f :=
  LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (Submodule.inclusion_injective _)) f

/-- The target-valued family. Off the generic path the retraction is an
algebraic choice; on that path it leaves the actual shifted map unchanged. -/
def regularTargetMap (hc : Valid d e c) (z : ℂ) :
    KF 4 (source d e) →ₗ[ℂ] KF 4 (target d e) :=
  targetRetraction d e ∘ₗ regularMap d e c hc z

theorem regularTargetMap_analytic (hc : Valid d e c) (hreg : Admissible d e c)
    (f : KF 4 (source d e)) :
    IsWeaklyAnalyticAt (fun z => regularTargetMap d e c hc z f) 0 :=
  (regularMap_analytic d e c hc hreg f).map (targetRetraction d e)

theorem regularTargetMap_exists_finite_range (hc : Valid d e c)
    (f : KF 4 (source d e)) :
    ∃ S : Submodule ℂ (KF 4 (target d e)),
      FiniteDimensional ℂ S ∧ ∀ z, regularTargetMap d e c hc z f ∈ S := by
  obtain ⟨S, hS, hfS⟩ := regularMap_exists_finite_range d e c hc f
  let := hS
  exact ⟨S.map (targetRetraction d e), inferInstance,
    fun z => Submodule.mem_map_of_mem (hfS z)⟩

theorem regularTargetMap_eq_generic (hc : Valid d e c) (hreg : Admissible d e c)
    {z : ℂ} (hz : z ≠ 0) (hg : IsGenericShift d e z) :
    regularTargetMap d e c hc z =
      RealInducedSwapShifted.shiftedMap d e (genericFourCrossings hg) := by
  ext f : 1
  change targetRetraction d e (regularMap d e c hc z f) = _
  rw [regularMap_eq_generic d e c hc hreg hz hg]
  exact targetRetraction_inclusion d e
    (RealInducedSwapShifted.shiftedMap d e (genericFourCrossings hg) f)

/-- Specialization of the generic opposite-shift inverse on the actual modules. -/
theorem regularTargetMap_leftInverse
    (hc : Valid d e c) (hreg : Admissible d e c)
    (b : Choices) (hb : Valid e d b) (hregb : Admissible e d b)
    {L : Filter ℂ} [L.NeBot] (hL : L ≤ 𝓝 0)
    (hpath : ∀ᶠ z in L, z ≠ 0 ∧ IsGenericShift d e z) :
    Function.LeftInverse (regularTargetMap e d b hb 0) (regularTargetMap d e c hc 0) := by
  have hinv : ∀ᶠ z in L, Function.LeftInverse
      (regularTargetMap e d b hb (-z)) (regularTargetMap d e c hc z) := by
    filter_upwards [hpath] with z hz
    rw [regularTargetMap_eq_generic d e c hc hreg hz.1 hz.2,
      regularTargetMap_eq_generic e d b hb hregb (neg_ne_zero.mpr hz.1) hz.2.reverse]
    exact shiftedMap_leftInverse (genericFourCrossings hz.2)
      (genericFourCrossings hz.2.reverse) (genericFourCrossings_areInverse hz.2)
  have h := leftInverse_at_zero (regularTargetMap d e c hc)
    (fun z => regularTargetMap e d b hb (-z))
    (regularTargetMap_analytic d e c hc hreg)
    (fun f => weaklyAnalyticAt_neg (regularTargetMap_analytic e d b hb hregb f))
    (regularTargetMap_exists_finite_range d e c hc) hL hinv
  simpa only [neg_zero] using h

theorem regularTargetMap_rightInverse
    (hc : Valid d e c) (hreg : Admissible d e c)
    (b : Choices) (hb : Valid e d b) (hregb : Admissible e d b)
    {L : Filter ℂ} [L.NeBot] (hL : L ≤ 𝓝 0)
    (hpath : ∀ᶠ z in L, z ≠ 0 ∧ IsGenericShift d e z) :
    Function.RightInverse (regularTargetMap e d b hb 0) (regularTargetMap d e c hc 0) := by
  have hinv : ∀ᶠ z in L, Function.LeftInverse
      (regularTargetMap d e c hc z) (regularTargetMap e d b hb (-z)) := by
    filter_upwards [hpath] with z hz
    rw [regularTargetMap_eq_generic d e c hc hreg hz.1 hz.2,
      regularTargetMap_eq_generic e d b hb hregb (neg_ne_zero.mpr hz.1) hz.2.reverse]
    exact shiftedMap_leftInverse (genericFourCrossings hz.2.reverse)
      (genericFourCrossings hz.2) (genericFourCrossings_areInverse hz.2).symm
  have hfinite : ∀ f, ∃ S : Submodule ℂ (KF 4 (source d e)),
      FiniteDimensional ℂ S ∧ ∀ z, regularTargetMap e d b hb (-z) f ∈ S := by
    intro f
    obtain ⟨S, hS, hfS⟩ := regularTargetMap_exists_finite_range e d b hb f
    exact ⟨S, hS, fun z => hfS (-z)⟩
  have h := leftInverse_at_zero (fun z => regularTargetMap e d b hb (-z))
    (regularTargetMap d e c hc)
    (fun f => weaklyAnalyticAt_neg (regularTargetMap_analytic e d b hb hregb f))
    (regularTargetMap_analytic d e c hc hreg) hfinite hL hinv
  simpa only [neg_zero] using h.rightInverse

/-- The limiting linear equivalence, conditional on valid regularizing choices
in both directions and a nontrivial generic path. -/
def regularEquiv
    (hc : Valid d e c) (hreg : Admissible d e c)
    (b : Choices) (hb : Valid e d b) (hregb : Admissible e d b)
    {L : Filter ℂ} [L.NeBot] (hL : L ≤ 𝓝 0)
    (hpath : ∀ᶠ z in L, z ≠ 0 ∧ IsGenericShift d e z) :
    KF 4 (source d e) ≃ₗ[ℂ] KF 4 (target d e) :=
  { regularTargetMap d e c hc 0 with
    invFun := regularTargetMap e d b hb 0
    left_inv := regularTargetMap_leftInverse d e c hc hreg b hb hregb hL hpath
    right_inv := regularTargetMap_rightInverse d e c hc hreg b hb hregb hL hpath }

end RealInducedSwapGerm
end Langlands.Archimedean

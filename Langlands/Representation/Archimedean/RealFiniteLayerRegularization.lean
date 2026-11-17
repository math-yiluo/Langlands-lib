import Langlands.Representation.Archimedean.RealBlockMultiplierAnalytic
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Removing a simple pole in an algebraically finite family

These internal results use scalar coordinates and finite-dimensional subspaces.
No topology on the ambient vector space is required.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealFiniteLayerRegularization

open RealBlockMultiplierAnalytic
open scoped Topology

variable {U V W : Type*}
  [AddCommGroup U] [Module ℂ U]
  [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- Every algebraic scalar coordinate has the specified derivative. -/
def HasWeakDerivAt (f : ℂ → V) (v : V) (z₀ : ℂ) : Prop :=
  ∀ ℓ : V →ₗ[ℂ] ℂ, HasDerivAt (fun z => ℓ (f z)) (ℓ v) z₀

theorem eq_of_dual_eq {v w : V} (h : ∀ ℓ : V →ₗ[ℂ] ℂ, ℓ v = ℓ w) : v = w := by
  let : Module.Free ℂ V := Module.Free.of_divisionRing ℂ V
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ (v - w)).mp
  intro ℓ
  rw [map_sub, h ℓ, sub_self]

theorem HasWeakDerivAt.unique {f : ℂ → V} {v w : V} {z₀ : ℂ}
    (hv : HasWeakDerivAt f v z₀) (hw : HasWeakDerivAt f w z₀) : v = w :=
  eq_of_dual_eq fun ℓ => (hv ℓ).unique (hw ℓ)

theorem HasWeakDerivAt.add {f g : ℂ → V} {v w : V} {z₀ : ℂ}
    (hf : HasWeakDerivAt f v z₀) (hg : HasWeakDerivAt g w z₀) :
    HasWeakDerivAt (fun z => f z + g z) (v + w) z₀ := by
  intro ℓ
  simpa only [map_add] using (hf ℓ).fun_add (hg ℓ)

theorem HasWeakDerivAt.smul {f : ℂ → V} {v : V} {z₀ : ℂ}
    (hf : HasWeakDerivAt f v z₀) (c : ℂ) :
    HasWeakDerivAt (fun z => c • f z) (c • v) z₀ := by
  intro ℓ
  simpa only [map_smul, smul_eq_mul] using (hf ℓ).const_mul c

/-- Weak analyticity passes to a subspace containing every value. Coordinate
functionals on that subspace extend algebraically to the whole space. -/
theorem weaklyAnalyticAt_codRestrict {f : ℂ → V} {z₀ : ℂ}
    (hf : IsWeaklyAnalyticAt f z₀) (S : Submodule ℂ V) (hS : ∀ z, f z ∈ S) :
    IsWeaklyAnalyticAt (fun z => (⟨f z, hS z⟩ : S)) z₀ := by
  intro ℓ
  obtain ⟨L, hL⟩ := ℓ.exists_extend
  have heq : (fun z => ℓ (⟨f z, hS z⟩ : S)) = fun z => L (f z) := by
    funext z
    exact (LinearMap.congr_fun hL ⟨f z, hS z⟩).symm
  rw [heq]
  exact hf L

/-- A weakly analytic family contained in one finite-dimensional subspace has
an actual derivative vector, and this vector belongs to the same subspace. -/
theorem exists_weakDerivAt_mem {f : ℂ → V} {z₀ : ℂ}
    (hf : IsWeaklyAnalyticAt f z₀)
    (S : Submodule ℂ V) [FiniteDimensional ℂ S] (hS : ∀ z, f z ∈ S) :
    ∃ v ∈ S, HasWeakDerivAt f v z₀ := by
  classical
  let : Module.Free ℂ S := Module.Free.of_divisionRing ℂ S
  let b := Module.finBasis ℂ S
  let fs : ℂ → S := fun z => ⟨f z, hS z⟩
  have ha : ∀ i, AnalyticAt ℂ (fun z => b.repr (fs z) i) z₀ :=
    fun i => weaklyAnalyticAt_codRestrict hf S hS (b.coord i)
  let v : S := ∑ i, deriv (fun z => b.repr (fs z) i) z₀ • b i
  refine ⟨v, v.property, fun ℓ => ?_⟩
  have heq : (fun z => ℓ (f z)) =
      fun z => ∑ i, b.repr (fs z) i * ℓ (b i : V) := by
    funext z
    have hb := congrArg (ℓ.comp S.subtype) (b.sum_repr (fs z))
    simpa only [map_sum, map_smul, LinearMap.comp_apply, Submodule.subtype_apply,
      smul_eq_mul] using hb.symm
  rw [heq]
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (ha i).differentiableAt.hasDerivAt.mul_const (ℓ (b i : V)))
  simpa only [v, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
    smul_eq_mul] using hd

/-- The derivative of a linear-operator family, assuming derivative vectors
exist for all its inputs. Uniqueness makes the choice linear. -/
def derivativeMap (T : ℂ → U →ₗ[ℂ] V) (z₀ : ℂ)
    (h : ∀ u, ∃ v, HasWeakDerivAt (fun z => T z u) v z₀) : U →ₗ[ℂ] V where
  toFun u := Classical.choose (h u)
  map_add' u u' := by
    apply (Classical.choose_spec (h (u + u'))).unique
    simpa only [map_add] using
      (Classical.choose_spec (h u)).add (Classical.choose_spec (h u'))
  map_smul' c u := by
    apply (Classical.choose_spec (h (c • u))).unique
    simpa only [map_smul, RingHom.id_apply] using (Classical.choose_spec (h u)).smul c

theorem hasWeakDerivAt_derivativeMap (T : ℂ → U →ₗ[ℂ] V) (z₀ : ℂ)
    (h : ∀ u, ∃ v, HasWeakDerivAt (fun z => T z u) v z₀) (u : U) :
    HasWeakDerivAt (fun z => T z u) (derivativeMap T z₀ h u) z₀ :=
  Classical.choose_spec (h u)

theorem derivativeMap_mem (T : ℂ → U →ₗ[ℂ] V) (z₀ : ℂ)
    (h : ∀ u, ∃ v, HasWeakDerivAt (fun z => T z u) v z₀) (u : U)
    (ha : IsWeaklyAnalyticAt (fun z => T z u) z₀)
    (S : Submodule ℂ V) [FiniteDimensional ℂ S] (hS : ∀ z, T z u ∈ S) :
    derivativeMap T z₀ h u ∈ S := by
  obtain ⟨v, hvS, hv⟩ := exists_weakDerivAt_mem ha S hS
  rw [(hasWeakDerivAt_derivativeMap T z₀ h u).unique hv]
  exact hvS

/-- Divide a vanishing family by the parameter, with the derivative as value
at zero. The result is a linear operator at every parameter. -/
def removeSimplePole (T : ℂ → U →ₗ[ℂ] V)
    (h : ∀ u, ∃ v, HasWeakDerivAt (fun z => T z u) v 0) (z : ℂ) : U →ₗ[ℂ] V :=
  if z = 0 then derivativeMap T 0 h else z⁻¹ • T z

theorem removeSimplePole_of_ne (T : ℂ → U →ₗ[ℂ] V)
    (h : ∀ u, ∃ v, HasWeakDerivAt (fun z => T z u) v 0)
    {z : ℂ} (hz : z ≠ 0) :
    removeSimplePole T h z = z⁻¹ • T z := by
  simp only [removeSimplePole, hz, ↓reduceIte]

theorem removeSimplePole_zero (T : ℂ → U →ₗ[ℂ] V)
    (h : ∀ u, ∃ v, HasWeakDerivAt (fun z => T z u) v 0) :
    removeSimplePole T h 0 = derivativeMap T 0 h := by
  simp only [removeSimplePole, ↓reduceIte]

/-- Scalar power-series division proves analytic extension of the quotient. -/
theorem weaklyAnalyticAt_removeSimplePole (T : ℂ → U →ₗ[ℂ] V)
    (h : ∀ u, ∃ v, HasWeakDerivAt (fun z => T z u) v 0)
    (hzero : T 0 = 0) (u : U)
    (ha : IsWeaklyAnalyticAt (fun z => T z u) 0) :
    IsWeaklyAnalyticAt (fun z => removeSimplePole T h z u) 0 := by
  intro ℓ
  have heq : (fun z => ℓ (removeSimplePole T h z u)) =
      dslope (fun z => ℓ (T z u)) 0 := by
    funext z
    by_cases hz : z = 0
    · subst z
      rw [removeSimplePole_zero, dslope_same]
      exact (hasWeakDerivAt_derivativeMap T 0 h u ℓ).deriv.symm
    · rw [removeSimplePole_of_ne T h hz, dslope_of_ne _ hz]
      simp only [LinearMap.smul_apply, map_smul, slope_def_module, sub_zero,
        hzero, LinearMap.zero_apply, map_zero]
  rw [heq]
  obtain ⟨p, hp⟩ := ha ℓ
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

theorem removeSimplePole_mem (T : ℂ → U →ₗ[ℂ] V)
    (h : ∀ u, ∃ v, HasWeakDerivAt (fun z => T z u) v 0) (u : U)
    (ha : IsWeaklyAnalyticAt (fun z => T z u) 0)
    (S : Submodule ℂ V) [FiniteDimensional ℂ S] (hS : ∀ z, T z u ∈ S)
    (z : ℂ) : removeSimplePole T h z u ∈ S := by
  by_cases hz : z = 0
  · subst z
    rw [removeSimplePole_zero]
    exact derivativeMap_mem T 0 h u ha S hS
  · rw [removeSimplePole_of_ne T h hz]
    exact S.smul_mem _ (hS z)

/-- Pointwise weak analyticity of an operator family suffices for its action
on a weakly analytic input family in one finite-dimensional subspace. -/
theorem weaklyAnalyticAt_apply (T : ℂ → U →ₗ[ℂ] V)
    {f : ℂ → U} {z₀ : ℂ}
    (hT : ∀ u, IsWeaklyAnalyticAt (fun z => T z u) z₀)
    (hf : IsWeaklyAnalyticAt f z₀)
    (S : Submodule ℂ U) [FiniteDimensional ℂ S] (hS : ∀ z, f z ∈ S) :
    IsWeaklyAnalyticAt (fun z => T z (f z)) z₀ := by
  classical
  let : Module.Free ℂ S := Module.Free.of_divisionRing ℂ S
  let b := Module.finBasis ℂ S
  let fs : ℂ → S := fun z => ⟨f z, hS z⟩
  intro ℓ
  have heq : (fun z => ℓ (T z (f z))) =
      fun z => ∑ i, b.repr (fs z) i * ℓ (T z (b i : U)) := by
    funext z
    have hb := congrArg ((ℓ.comp (T z)).comp S.subtype) (b.sum_repr (fs z))
    simpa only [map_sum, map_smul, LinearMap.comp_apply, Submodule.subtype_apply,
      smul_eq_mul] using hb.symm
  rw [heq]
  apply Finset.analyticAt_fun_sum
  intro i _
  exact (weaklyAnalyticAt_codRestrict hf S hS (b.coord i)).mul (hT (b i : U) ℓ)

/-- Equality on a nontrivial filter approaching the parameter implies equality
of the analytic values. This also applies to a punctured or restricted path. -/
theorem eq_of_weaklyAnalyticAt_eventuallyEq {f g : ℂ → V} {z₀ : ℂ}
    (hf : IsWeaklyAnalyticAt f z₀) (hg : IsWeaklyAnalyticAt g z₀)
    {L : Filter ℂ} [L.NeBot] (hL : L ≤ 𝓝 z₀) (heq : f =ᶠ[L] g) :
    f z₀ = g z₀ := by
  apply eq_of_dual_eq
  intro ℓ
  exact tendsto_nhds_unique_of_eventuallyEq
    ((hf ℓ).continuousAt.mono_left hL)
    ((hg ℓ).continuousAt.mono_left hL) (heq.fun_comp ℓ)

end Langlands.Archimedean.RealFiniteLayerRegularization

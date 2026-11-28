import Langlands.BaseChange.SupercuspidalCutoffCoefficient
import Langlands.Representation.Character.Basic
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.CompactCoefficient.SemisimplicityProof
import Mathlib.RepresentationTheory.Irreducible

/-!
# Traces of cut-off supercuspidal coefficients

For an irreducible supercuspidal representation `π` of `GL_n(F)` with central character `χ`
and the cut-off coefficients `f_x = cutoff π ℓ x` of the module
`Langlands.BaseChange.SupercuspidalCutoffCoefficient`:

* `integratedAction_cutoff_rho`: `ρ(f_{π(h) x}) = ρ(h) ∘ ρ(f_x)` for every smooth `ρ` with
  central character `χ`;
* `integratedAction_cutoff_eq_zero`: `ρ(f_x) = 0` for every irreducible admissible `ρ ≇ π`
  with central character `χ`;
* `exists_integratedAction_cutoff_self`, `distribution_cutoff_self`: `π(f_x) w = c(w) x`, so
  `tr π(f_x) = c(x)`;
* `exists_cuspForm_pseudoCoefficient`: for a suitable `ℓ` and `x`, `c(x) ≠ 0`, and
  `c(x)⁻¹ f_x` is a test function with vanishing constant terms, trace `1` on `π` and trace `0`
  on every irreducible admissible `ρ ≇ π` with central character `χ`.
-/

noncomputable section

namespace Langlands.BaseChange.SupercuspidalCutoff

open MeasureTheory HarmonicAnalysis PeriodicWindow
open scoped ComplexConjugate

universe u uV uW

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

/-- The scalar uniformizer as an element of the centre. -/
def centralUniformizerCenter : Subgroup.center (GeneralLinear n F) :=
  ⟨centralUniformizer, centralUniformizer_mem_center⟩

section Central

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear n F) V) (ℓ : Module.Dual ℂ V)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem coeff_central_mul {χ : Subgroup.center (GeneralLinear n F) →* ℂˣ}
    (hπχ : HasCentralCharacterRep π χ) (zc : Subgroup.center (GeneralLinear n F)) (x : V)
    (g : GeneralLinear n F) :
    coeff π ℓ x ((zc : GeneralLinear n F) * g) = (χ zc⁻¹ : ℂ) * coeff π ℓ x g := by
  simp only [coeff, mul_inv_rev, map_mul, Module.End.mul_apply]
  rw [show ((zc : GeneralLinear n F))⁻¹ = ((zc⁻¹ : Subgroup.center _) : GeneralLinear n F)
    from rfl, hπχ, map_smul, map_smul, smul_eq_mul]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem character_inv_mul_character (χ : Subgroup.center (GeneralLinear n F) →* ℂˣ)
    (zc : Subgroup.center (GeneralLinear n F)) :
    (χ zc⁻¹ : ℂ) * (χ zc : ℂ) = 1 := by
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mul_central_comm (zc : Subgroup.center (GeneralLinear n F)) (h g : GeneralLinear n F) :
    h * ((zc : GeneralLinear n F) * g) = (zc : GeneralLinear n F) * (h * g) := by
  rw [← mul_assoc, ← mul_assoc, (Subgroup.mem_center_iff.mp zc.property h)]

end Central

variable [T2Space (GeneralLinear n F)] [MeasurableSpace (GeneralLinear n F)]
  [BorelSpace (GeneralLinear n F)] (μ : Measure (GeneralLinear n F)) [μ.IsHaarMeasure]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear n F) V) (ℓ : Module.Dual ℂ V)

section Integrability

omit [T2Space (GeneralLinear n F)] [MeasurableSpace (GeneralLinear n F)]
  [BorelSpace (GeneralLinear n F)] in
theorem continuous_matrixCoefficient {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GeneralLinear n F) W) (hρ : IsSmooth ρ) (L : Module.Dual ℂ W)
    (w : W) : Continuous fun g => L (ρ g w) :=
  ((Hecke.orbitMap_locallyConstant ρ (hρ w)).comp fun v => L v).continuous

omit [T2Space (GeneralLinear n F)] [MeasurableSpace (GeneralLinear n F)]
  [BorelSpace (GeneralLinear n F)] in
theorem continuous_coeff (hπ : IsSmooth π) (x : V) : Continuous (coeff π ℓ x) :=
  (isLocallyConstant_coeff π ℓ hπ x).continuous

theorem integrable_levelSet_coeff_mul (hn : 0 < n) (hπ : GeneralLinear.IsSupercuspidal π)
    (hℓ : IsSmoothVector π.dual ℓ) (x : V) (j : ℤ) {b : GeneralLinear n F → ℂ}
    (hb : Continuous b) :
    Integrable ((levelSet detOrd j).indicator (fun g => coeff π ℓ x g * b g)) μ := by
  have heq : (levelSet detOrd j).indicator (fun g => coeff π ℓ x g * b g) =
      fun g => (levelSet detOrd j).indicator (coeff π ℓ x) g * b g :=
    funext fun g => Set.indicator_mul_left _ _ _
  rw [heq]
  have hc : Continuous ((levelSet detOrd j).indicator (coeff π ℓ x)) :=
    (isLocallyConstant_indicator_detOrd (fun d => d = j)
      (isLocallyConstant_coeff π ℓ hπ.1.1 x)).continuous
  exact (hc.mul hb).integrable_of_hasCompactSupport
    (hasCompactSupport_levelSet_coeff π ℓ hn hπ hℓ x j).mul_right

theorem integrable_cutoffFun_mul (hn : 0 < n) (hπ : GeneralLinear.IsSupercuspidal π)
    (hℓ : IsSmoothVector π.dual ℓ) (x : V) {b : GeneralLinear n F → ℂ} (hb : Continuous b) :
    Integrable (fun g => cutoffFun π ℓ x g * b g) μ :=
  (((cutoff π ℓ hn hπ hℓ x).2.1.continuous).mul hb).integrable_of_hasCompactSupport
    (cutoff π ℓ hn hπ hℓ x).2.2.mul_right

end Integrability

section Intertwining

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- **Intertwining.** For a smooth `ρ` with the central character of `π`,
`ρ(f_{π(h) x}) = ρ(h) ∘ ρ(f_x)`. Both sides are tested against an arbitrary linear form `L`
on `W`; the two scalar integrals differ by a left translation of a `z`-periodic integrand, which
does not change the window integral. -/
theorem integratedAction_cutoff_rho (hn : 0 < n) (hπ : GeneralLinear.IsSupercuspidal π)
    (hℓ : IsSmoothVector π.dual ℓ) {χ : Subgroup.center (GeneralLinear n F) →* ℂˣ}
    (hπχ : HasCentralCharacterRep π χ) (ρ : Representation ℂ (GeneralLinear n F) W)
    (hρ : IsSmooth ρ) (hρχ : HasCentralCharacterRep ρ χ) (h : GeneralLinear n F) (x : V)
    (w : W) :
    Hecke.integratedAction μ ρ hρ (cutoff π ℓ hn hπ hℓ (π h x)) w =
      ρ h (Hecke.integratedAction μ ρ hρ (cutoff π ℓ hn hπ hℓ x) w) := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro L
  rw [map_sub, sub_eq_zero, Hecke.integratedAction_dual,
    show L (ρ h (Hecke.integratedAction μ ρ hρ (cutoff π ℓ hn hπ hℓ x) w)) =
      (L ∘ₗ ρ h) (Hecke.integratedAction μ ρ hρ (cutoff π ℓ hn hπ hℓ x) w) from rfl,
    Hecke.integratedAction_dual]
  let zc : Subgroup.center (GeneralLinear n F) := centralUniformizerCenter
  let Φ : GeneralLinear n F → ℂ := fun g => coeff π ℓ x (h⁻¹ * g) * L (ρ g w)
  have hΦ : ∀ g, Φ ((zc : GeneralLinear n F) * g) = Φ g := by
    intro g
    simp only [Φ]
    rw [mul_central_comm zc h⁻¹ g, coeff_central_mul π ℓ hπχ, map_mul, Module.End.mul_apply,
      hρχ, map_smul, smul_eq_mul]
    calc (χ zc⁻¹ : ℂ) * coeff π ℓ x (h⁻¹ * g) * ((χ zc : ℂ) * L (ρ g w))
        = ((χ zc⁻¹ : ℂ) * (χ zc : ℂ)) * (coeff π ℓ x (h⁻¹ * g) * L (ρ g w)) := by ring
      _ = _ := by rw [character_inv_mul_character, one_mul]
  have hint : ∀ j, Integrable ((levelSet detOrd j).indicator Φ) μ := by
    intro j
    have heq : Φ = fun g => coeff π ℓ (π h x) g * L (ρ g w) := by
      funext g
      simp only [Φ, coeff_rho]
    rw [heq]
    exact integrable_levelSet_coeff_mul μ π ℓ hn hπ hℓ (π h x) j
      (continuous_matrixCoefficient ρ hρ L w)
  have key := integral_window_comp_mul_left μ detOrd_mul
    (detOrd_centralUniformizer (F := F) (n := n)) hΦ hint h
  have hlhs : ∀ g, cutoff π ℓ hn hπ hℓ (π h x) g * L (ρ g w) =
      (window detOrd n 0).indicator Φ g := by
    intro g
    rw [cutoff_apply, cutoffFun, Set.indicator_mul_left]
    congr 1
    congr 1
    funext g
    exact coeff_rho π ℓ h x g
  have hrhs : ∀ g, cutoff π ℓ hn hπ hℓ x g * (L ∘ₗ ρ h) (ρ g w) =
      (window detOrd n 0).indicator (fun g => Φ (h * g)) g := by
    intro g
    simp only [Φ, inv_mul_cancel_left]
    rw [cutoff_apply, cutoffFun, Set.indicator_mul_left (window detOrd n 0) (coeff π ℓ x)]
    simp only [LinearMap.coe_comp, Function.comp_apply, map_mul, Module.End.mul_apply]
  simp_rw [hlhs, hrhs]
  exact key.symm

/-- The linear map `x ↦ ρ(f_x) w`. -/
def cutoffActionMap (hn : 0 < n) (hπ : GeneralLinear.IsSupercuspidal π)
    (hℓ : IsSmoothVector π.dual ℓ) (ρ : Representation ℂ (GeneralLinear n F) W)
    (hρ : IsSmooth ρ) (w : W) : V →ₗ[ℂ] W where
  toFun x := Hecke.integratedAction μ ρ hρ (cutoff π ℓ hn hπ hℓ x) w
  map_add' x y := by simp only [map_add, LinearMap.add_apply]
  map_smul' c x := by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply]

/-- The intertwiner `x ↦ ρ(f_x) w` from `π` to `ρ`. -/
def cutoffIntertwiner (hn : 0 < n) (hπ : GeneralLinear.IsSupercuspidal π)
    (hℓ : IsSmoothVector π.dual ℓ) {χ : Subgroup.center (GeneralLinear n F) →* ℂˣ}
    (hπχ : HasCentralCharacterRep π χ) (ρ : Representation ℂ (GeneralLinear n F) W)
    (hρ : IsSmooth ρ) (hρχ : HasCentralCharacterRep ρ χ) (w : W) :
    π.IntertwiningMap ρ :=
  (cutoffActionMap μ π ℓ hn hπ hℓ ρ hρ w).intertwiningMap_of_isIntertwiningMap π ρ
    fun h x => integratedAction_cutoff_rho μ π ℓ hn hπ hℓ hπχ ρ hρ hρχ h x w

/-- **Other representations.** For an irreducible admissible `ρ ≇ π` with the central
character of `π`, `ρ(f_x) = 0`: the intertwiner `x ↦ ρ(f_x) w` vanishes by Schur's lemma. -/
theorem integratedAction_cutoff_eq_zero (hn : 0 < n) (hπ : GeneralLinear.IsSupercuspidal π)
    (hirr : π.IsIrreducible) (hℓ : IsSmoothVector π.dual ℓ)
    {χ : Subgroup.center (GeneralLinear n F) →* ℂˣ} (hπχ : HasCentralCharacterRep π χ)
    (ρ : Representation ℂ (GeneralLinear n F) W) (hρ : IsAdmissible ρ)
    (hρirr : ρ.IsIrreducible) (hρχ : HasCentralCharacterRep ρ χ) (hne : IsEmpty (ρ.Equiv π))
    (x : V) :
    Hecke.integratedAction μ ρ hρ.1 (cutoff π ℓ hn hπ hℓ x) = 0 := by
  let := hirr
  let := hρirr
  let : IsEmpty (π.Equiv ρ) := ⟨fun e => hne.false e.symm⟩
  ext w
  have h0 : cutoffIntertwiner μ π ℓ hn hπ hℓ hπχ ρ hρ.1 hρχ w = 0 := Subsingleton.elim _ _
  have := congrArg (fun S : π.IntertwiningMap ρ => S.toLinearMap x) h0
  simpa [cutoffIntertwiner, cutoffActionMap] using this

/-- The distribution character of `ρ ≇ π` vanishes on every `f_x`. -/
theorem distribution_cutoff_eq_zero [LocallyCompactSpace (GeneralLinear n F)]
    [TotallyDisconnectedSpace (GeneralLinear n F)] (hn : 0 < n)
    (hπ : GeneralLinear.IsSupercuspidal π) (hirr : π.IsIrreducible)
    (hℓ : IsSmoothVector π.dual ℓ) {χ : Subgroup.center (GeneralLinear n F) →* ℂˣ}
    (hπχ : HasCentralCharacterRep π χ) (ρ : Representation ℂ (GeneralLinear n F) W)
    (hρ : IsAdmissible ρ) (hρirr : ρ.IsIrreducible) (hρχ : HasCentralCharacterRep ρ χ)
    (hne : IsEmpty (ρ.Equiv π)) (x : V) :
    Character.distribution μ ρ hρ (cutoff π ℓ hn hπ hℓ x) = 0 := by
  have h : Character.finiteRankIntegratedAction μ ρ hρ (cutoff π ℓ hn hπ hℓ x) = 0 :=
    Subtype.ext (integratedAction_cutoff_eq_zero μ π ℓ hn hπ hirr hℓ hπχ ρ hρ hρirr hρχ hne x)
  rw [Character.distribution_apply, h, map_zero]

end Intertwining

section Self

/-- **Schur.** `π(f_x) w = c(w) x` for a function `c` independent of `x`. -/
theorem exists_integratedAction_cutoff_self (hn : 0 < n) (hπ : GeneralLinear.IsSupercuspidal π)
    (hirr : π.IsIrreducible) (hℓ : IsSmoothVector π.dual ℓ)
    {χ : Subgroup.center (GeneralLinear n F) →* ℂˣ} (hπχ : HasCentralCharacterRep π χ) :
    ∃ c : V → ℂ, ∀ x w,
      Hecke.integratedAction μ π hπ.1.1 (cutoff π ℓ hn hπ hℓ x) w = c w • x := by
  have h : ∀ w : V, ∃ c : ℂ, ∀ x,
      Hecke.integratedAction μ π hπ.1.1 (cutoff π ℓ hn hπ hℓ x) w = c • x := by
    intro w
    obtain ⟨c, hc, -⟩ := admissibleSchur_scalarEndomorphism π hπ.1 hirr
      (cutoffIntertwiner μ π ℓ hn hπ hℓ hπχ π hπ.1.1 hπχ w)
    refine ⟨c, fun x => ?_⟩
    have := congrArg (fun S : π.IntertwiningMap π => S.toLinearMap x) hc
    simpa [cutoffIntertwiner, cutoffActionMap] using this
  choose c hc using h
  exact ⟨c, fun x w => hc w x⟩

/-- **The trace on `π`.** If `π(f_x) w = c(w) x` for all `w` and `x ≠ 0`, the operator
`π(f_x)` has range in `ℂ x`, acts there by `c(x)`, and `tr π(f_x) = c(x)`. -/
theorem distribution_cutoff_self [LocallyCompactSpace (GeneralLinear n F)]
    [TotallyDisconnectedSpace (GeneralLinear n F)] (hn : 0 < n)
    (hπ : GeneralLinear.IsSupercuspidal π) (hℓ : IsSmoothVector π.dual ℓ) {c : V → ℂ}
    (hc : ∀ x w, Hecke.integratedAction μ π hπ.1.1 (cutoff π ℓ hn hπ hℓ x) w = c w • x)
    {x : V} (hx : x ≠ 0) :
    Character.distribution μ π hπ.1 (cutoff π ℓ hn hπ hℓ x) = c x := by
  have hS : (Hecke.integratedAction μ π hπ.1.1 (cutoff π ℓ hn hπ hℓ x)).range ≤ ℂ ∙ x := by
    rintro _ ⟨w, rfl⟩
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  rw [Character.distribution_eq_subspace μ π hπ.1 _ (ℂ ∙ x) hS]
  have hop : FiniteRankEnd.onSubspace (Hecke.integratedAction μ π hπ.1.1
      (cutoff π ℓ hn hπ hℓ x)) (ℂ ∙ x) hS = c x • LinearMap.id := by
    ext ⟨v, hv⟩
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
    change Hecke.integratedAction μ π hπ.1.1 (cutoff π ℓ hn hπ hℓ x) (t • x) = c x • (t • x)
    rw [map_smul, hc, smul_comm]
  rw [hop, map_smul, LinearMap.trace_id, finrank_span_singleton hx]
  simp

end Self

end Langlands.BaseChange.SupercuspidalCutoff

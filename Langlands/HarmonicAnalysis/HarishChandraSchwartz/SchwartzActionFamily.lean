import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzActionConvolution
import Langlands.Representation.Hecke.ActionProjection
import Langlands.Representation.Smooth.FixedVectors.Definitions
import Langlands.Representation.Smooth.FixedVectors.OrderProof

/-! # The operators `π[φ]` in the proof of Proposition III.7.1

For a compact open subgroup `H`, the normalized indicator `ε_H = (mes H)⁻¹ 1_H` lies in `C(G)`
and `π(ε_H)` fixes every `H`-fixed vector. The operators `π(f)`, `f ∈ C(G)`, commute with
intertwiners, and `π(ρ(g) λ(g) f) = ρ(g) π(f) ρ(g)⁻¹` when the measure is also right
invariant.

A family `H ↦ φ_H ∈ C(G)` with `φ_H * ε_{H'} = φ_{H'}` for `H ⊆ H'` and
`ρ(g) λ(g) φ_H = φ_{g H g⁻¹}` defines, on every admissible representation with tempered
coefficients, an intertwining operator `π[φ]` by `π[φ] v = π(φ_H) v` for any compact open
subgroup `H` fixing `v`, and these operators commute with intertwiners.
-/

noncomputable section

universe u v w

open MeasureTheory Filter
open Langlands.HarmonicAnalysis

namespace Langlands.HarishChandraSchwartz

section FixedVectors

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Nonempty (CompactOpenSubgroup G)]
  {V : Type v} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

/-- Every vector of a smooth representation is fixed by a compact open subgroup. -/
theorem exists_compactOpenSubgroup_fixed (hρ : IsSmooth ρ) (v : V) :
    ∃ H : CompactOpenSubgroup G, v ∈ fixedVectors ρ H.toSubgroup := by
  obtain ⟨K, hK⟩ := hρ v
  obtain ⟨L, hLc, hLK⟩ := CompactOpenSubgroup.cofinal K
  exact ⟨⟨L, hLc⟩, fixedVectors_antitone ρ (OpenSubgroup.toSubgroup_le.mpr hLK) hK⟩

omit [Nonempty (CompactOpenSubgroup G)] in
/-- If `H` fixes `v`, then `g H g⁻¹` fixes `ρ(g) v`. -/
theorem rho_mem_fixedVectors_conj {H : CompactOpenSubgroup G} {v : V}
    (hv : v ∈ fixedVectors ρ H.toSubgroup) (g : G) :
    ρ g v ∈ fixedVectors ρ (H.conj g).toSubgroup := by
  change ∀ x : (H.conj g).toSubgroup, ρ (x : G) (ρ g v) = ρ g v
  intro x
  have hx : g⁻¹ * (x : G) * g ∈ H.toSubgroup := mem_conjSubgroup.mp x.2
  have h₁ : ρ (g⁻¹ * (x : G) * g) v = v := hv ⟨_, hx⟩
  have h₂ : (x : G) * g = g * (g⁻¹ * (x : G) * g) := by group
  rw [← Module.End.mul_apply, ← map_mul, h₂, map_mul, Module.End.mul_apply, h₁]

end FixedVectors

section NormalizedIndicator

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {Ξ σ : G → ℝ}

omit [BorelSpace G] in
/-- The normalized indicator `ε_H` is bi-invariant under `H`. -/
theorem isBiInvariant_normalizedIndicator (μ : Measure G) (H : CompactOpenSubgroup G) :
    IsBiInvariant H.toSubgroup
      (Hecke.HeckeAlgebra.normalizedIndicator μ H.1 H.2 : SchwartzBruhat G) := by
  have hf := Hecke.HeckeAlgebra.normalizedIndicator_mem_biInvariant μ H.1 H.2
  intro h₁ h₁m h₂ h₂m g
  rw [hf.2 ⟨h₂, h₂m⟩ (h₁ * g), hf.1 ⟨h₁, h₁m⟩ g]

omit [BorelSpace G] in
/-- The function `ε_H = (mes H)⁻¹ 1_H` of Waldspurger's proof of Proposition III.7.1, the
normalized indicator of the Hecke algebra, as an element of `C(G)` (for continuous positive
`Ξ` and continuous nonnegative `σ`). -/
def Space.normalizedIndicator (μ : Measure G) (hΞc : Continuous Ξ) (hΞ : ∀ g, 0 < Ξ g)
    (hσc : Continuous σ) (hσ : ∀ g, 0 ≤ σ g) (H : CompactOpenSubgroup G) : Space Ξ σ :=
  (⟨(Hecke.HeckeAlgebra.normalizedIndicator μ H.1 H.2 : SchwartzBruhat G),
    levelSubmodule_le_schwartzSubmodule Ξ σ H
      (schwartzBruhat_mem_levelSubmodule hΞc hΞ hσc hσ _
        (isBiInvariant_normalizedIndicator μ H))⟩ : schwartzSubmodule Ξ σ)

omit [BorelSpace G] in
theorem Space.normalizedIndicator_apply (μ : Measure G) (hΞc : Continuous Ξ)
    (hΞ : ∀ g, 0 < Ξ g) (hσc : Continuous σ) (hσ : ∀ g, 0 ≤ σ g) (H : CompactOpenSubgroup G)
    (x : G) :
    Space.normalizedIndicator μ hΞc hΞ hσc hσ H x =
      (μ.real (H.1 : Set G) : ℂ)⁻¹ * (H.1 : Set G).indicator (fun _ => (1 : ℂ)) x :=
  rfl

variable [MeasurableMul G] [Nonempty (CompactOpenSubgroup G)] {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type v} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

/-- `π(ε_H)` is the action of the normalized indicator of the Hecke algebra. -/
theorem schwartzAction_normalizedIndicator (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) (hΞc : Continuous Ξ) (hΞ : ∀ g, 0 < Ξ g)
    (hσc : Continuous σ) (hσ : ∀ g, 0 ≤ σ g) (H : CompactOpenSubgroup G) :
    schwartzAction hw hρ hT (Space.normalizedIndicator μ hΞc hΞ hσc hσ H) =
      Hecke.heckeAction μ ρ hρ.1 (Hecke.HeckeAlgebra.normalizedIndicator μ H.1 H.2) := by
  refine LinearMap.ext fun v => ext_smoothDual hρ.1 fun ℓ => ?_
  rw [schwartzAction_eval]
  change _ = ℓ.val (Hecke.integratedAction μ ρ hρ.1 _ v)
  rw [Hecke.integratedAction_dual]
  rfl

/-- `π(ε_H) v = v` for every `H`-fixed vector `v`. -/
theorem schwartzAction_normalizedIndicator_of_mem (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) (hΞc : Continuous Ξ) (hΞ : ∀ g, 0 < Ξ g)
    (hσc : Continuous σ) (hσ : ∀ g, 0 ≤ σ g) {H : CompactOpenSubgroup G} {v : V}
    (hv : v ∈ fixedVectors ρ H.toSubgroup) :
    schwartzAction hw hρ hT (Space.normalizedIndicator μ hΞc hΞ hσc hσ H) v = v := by
  rw [schwartzAction_normalizedIndicator]
  exact Hecke.heckeAction_normalizedIndicator_of_fixed μ ρ hρ.1 H.1 H.2 hv

/-- `π(ε_H)` takes values in the `H`-fixed vectors. -/
theorem schwartzAction_normalizedIndicator_mem (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) (hΞc : Continuous Ξ) (hΞ : ∀ g, 0 < Ξ g)
    (hσc : Continuous σ) (hσ : ∀ g, 0 ≤ σ g) (H : CompactOpenSubgroup G) (v : V) :
    schwartzAction hw hρ hT (Space.normalizedIndicator μ hΞc hΞ hσc hσ H) v ∈
      fixedVectors ρ H.toSubgroup := by
  rw [schwartzAction_normalizedIndicator]
  exact Hecke.heckeAction_normalizedIndicator_mem μ ρ hρ.1 H.1 H.2 v

end NormalizedIndicator

section Naturality

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
  [Nonempty (CompactOpenSubgroup G)]
  {μ : Measure G} [μ.IsMulLeftInvariant] {Ξ σ : G → ℝ}
  {V : Type v} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {W : Type w} [AddCommGroup W] [Module ℂ W] {τ : Representation ℂ G W}

/-- The operators `π(f)` commute with intertwiners: `T π₁(f) = π₂(f) T`. -/
theorem schwartzAction_intertwining (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hτ : IsAdmissible τ) (hTρ : HasTemperedCoefficients Ξ σ ρ)
    (hTτ : HasTemperedCoefficients Ξ σ τ) (T : ρ.IntertwiningMap τ) (f : Space Ξ σ) (v : V) :
    T (schwartzAction hw hρ hTρ f v) = schwartzAction hw hτ hTτ f (T v) := by
  refine ext_smoothDual hτ.1 fun ℓ => ?_
  have h₁ : ∀ x : V, ℓ.val (T x) = (contragredientMap T ℓ).val x := fun x => rfl
  rw [h₁, schwartzAction_eval, schwartzAction_eval]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  change f g * ℓ.val (T (ρ g v)) = f g * ℓ.val (τ g (T v))
  rw [T.isIntertwining]

/-- For a right invariant measure, `π(ρ(g) λ(g) f) = ρ(g) π(f) ρ(g)⁻¹`. -/
theorem schwartzAction_translate_conj [μ.IsMulRightInvariant] (hw : L2Weights μ Ξ σ)
    (ht : TranslationWeights Ξ σ) (hρ : IsAdmissible ρ) (hT : HasTemperedCoefficients Ξ σ ρ)
    (g : G) (f : Space Ξ σ) :
    schwartzAction hw hρ hT (Space.translate ht g g f) =
      ρ g * schwartzAction hw hρ hT f * ρ g⁻¹ := by
  have h : Space.translate ht g g f = Space.translate ht g 1 (Space.translate ht 1 g f) := by
    rw [Space.translate_translate, mul_one, one_mul]
  rw [h, schwartzAction_translate_right, schwartzAction_translate_left]

end Naturality

section Family

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [Nonempty (CompactOpenSubgroup G)]
  {μ : Measure G} [μ.IsHaarMeasure] [SFinite μ]
  {K : Subgroup G} [CompactSpace K]
  {Ξ σ : G → ℝ}

/-- A family `H ↦ φ_H ∈ C(G)` indexed by the compact open subgroups, with the two properties
of Waldspurger's proof of Proposition III.7.1: `φ_H * ε_{H'} = φ_{H'}` for `H ⊆ H'`, and
`ρ(g) λ(g) φ_H = φ_{g H g⁻¹}`. -/
structure IdempotentFamily (hc : ConvolutionWeights μ K Ξ σ) (ht : TranslationWeights Ξ σ) where
  /-- The function `φ_H`. -/
  toFun : CompactOpenSubgroup G → Space Ξ σ
  /-- `φ_H * ε_{H'} = φ_{H'}` for `H ⊆ H'`. -/
  convolution_normalizedIndicator : ∀ H H' : CompactOpenSubgroup G,
    H.toSubgroup ≤ H'.toSubgroup →
      Space.convolution hc (toFun H)
        (Space.normalizedIndicator μ hc.continuous_xi hc.pos hc.continuous_sigma hc.nonneg H') =
        toFun H'
  /-- `ρ(g) λ(g) φ_H = φ_{g H g⁻¹}`. -/
  translate_conj : ∀ (g : G) (H : CompactOpenSubgroup G),
    Space.translate ht g g (toFun H) = toFun (H.conj g)

namespace IdempotentFamily

variable {hc : ConvolutionWeights μ K Ξ σ} {ht : TranslationWeights Ξ σ}
  (Φ : IdempotentFamily hc ht)
  {V : Type v} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

/-- For `H ⊆ H'` and `v` fixed by `H'`, `π(φ_{H'}) v = π(φ_H) v`. -/
theorem schwartzAction_eq_of_le (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) {H H' : CompactOpenSubgroup G}
    (hHH' : H.toSubgroup ≤ H'.toSubgroup) {v : V} (hv : v ∈ fixedVectors ρ H'.toSubgroup) :
    schwartzAction hw hρ hT (Φ.toFun H') v = schwartzAction hw hρ hT (Φ.toFun H) v := by
  rw [← Φ.convolution_normalizedIndicator H H' hHH', schwartzAction_convolution hw hc hρ hT,
    Module.End.mul_apply, schwartzAction_normalizedIndicator_of_mem hw hρ hT _ _ _ _ hv]

/-- `π(φ_H) v` does not depend on the compact open subgroup `H` fixing `v`. -/
theorem schwartzAction_eq (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) {H₁ H₂ : CompactOpenSubgroup G} {v : V}
    (h₁ : v ∈ fixedVectors ρ H₁.toSubgroup) (h₂ : v ∈ fixedVectors ρ H₂.toSubgroup) :
    schwartzAction hw hρ hT (Φ.toFun H₁) v = schwartzAction hw hρ hT (Φ.toFun H₂) v := by
  rw [Φ.schwartzAction_eq_of_le hw hρ hT (H₁.inf_le_left H₂) h₁,
    Φ.schwartzAction_eq_of_le hw hρ hT (H₁.inf_le_right H₂) h₂]

/-- The vector `π[φ] v = π(φ_H) v`, for a chosen compact open subgroup `H` fixing `v`. -/
def operatorFun (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) (v : V) : V :=
  schwartzAction hw hρ hT (Φ.toFun (exists_compactOpenSubgroup_fixed hρ.1 v).choose) v

theorem operatorFun_eq (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) {H : CompactOpenSubgroup G} {v : V}
    (hv : v ∈ fixedVectors ρ H.toSubgroup) :
    Φ.operatorFun hw hρ hT v = schwartzAction hw hρ hT (Φ.toFun H) v :=
  Φ.schwartzAction_eq hw hρ hT (exists_compactOpenSubgroup_fixed hρ.1 v).choose_spec hv

variable [μ.IsMulRightInvariant]

/-- Waldspurger, proof of Proposition III.7.1: the operator `π[φ] ∈ End_G V`,
`π[φ] v = π(φ_H) v` for any compact open subgroup `H` fixing `v`. -/
def operator (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) : ρ.IntertwiningMap ρ where
  toFun := Φ.operatorFun hw hρ hT
  map_add' v₁ v₂ := by
    obtain ⟨H₁, h₁⟩ := exists_compactOpenSubgroup_fixed hρ.1 v₁
    obtain ⟨H₂, h₂⟩ := exists_compactOpenSubgroup_fixed hρ.1 v₂
    have h₁' := fixedVectors_antitone ρ (H₁.inf_le_left H₂) h₁
    have h₂' := fixedVectors_antitone ρ (H₁.inf_le_right H₂) h₂
    rw [Φ.operatorFun_eq hw hρ hT h₁', Φ.operatorFun_eq hw hρ hT h₂',
      Φ.operatorFun_eq hw hρ hT (add_mem h₁' h₂'), map_add]
  map_smul' c v := by
    obtain ⟨H, h⟩ := exists_compactOpenSubgroup_fixed hρ.1 v
    rw [Φ.operatorFun_eq hw hρ hT h, Φ.operatorFun_eq hw hρ hT (Submodule.smul_mem _ c h),
      map_smul, RingHom.id_apply]
  isIntertwining' g := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨H, h⟩ := exists_compactOpenSubgroup_fixed hρ.1 v
    change Φ.operatorFun hw hρ hT (ρ g v) = ρ g (Φ.operatorFun hw hρ hT v)
    have hinv : ρ g⁻¹ (ρ g v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [Φ.operatorFun_eq hw hρ hT (rho_mem_fixedVectors_conj h g), Φ.operatorFun_eq hw hρ hT h,
      ← Φ.translate_conj g H, schwartzAction_translate_conj hw ht hρ hT, Module.End.mul_apply,
      Module.End.mul_apply, hinv]

/-- `π[φ] v = π(φ_H) v` for every compact open subgroup `H` fixing `v`. -/
theorem operator_apply_of_mem (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) {H : CompactOpenSubgroup G} {v : V}
    (hv : v ∈ fixedVectors ρ H.toSubgroup) :
    Φ.operator hw hρ hT v = schwartzAction hw hρ hT (Φ.toFun H) v := by
  change Φ.operatorFun hw hρ hT v = _
  exact Φ.operatorFun_eq hw hρ hT hv

variable {W : Type w} [AddCommGroup W] [Module ℂ W] {τ : Representation ℂ G W}

/-- Proposition III.7.1 (i) for `π[φ]`: for an intertwiner `T`, `π₂[φ] ∘ T = T ∘ π₁[φ]`. -/
theorem operator_intertwining (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hτ : IsAdmissible τ) (hTρ : HasTemperedCoefficients Ξ σ ρ)
    (hTτ : HasTemperedCoefficients Ξ σ τ) (T : ρ.IntertwiningMap τ) (v : V) :
    T (Φ.operator hw hρ hTρ v) = Φ.operator hw hτ hTτ (T v) := by
  obtain ⟨H, h⟩ := exists_compactOpenSubgroup_fixed hρ.1 v
  have hTv : T v ∈ fixedVectors τ H.toSubgroup := (fixedVectorsMap T H.toSubgroup ⟨v, h⟩).2
  rw [Φ.operator_apply_of_mem hw hρ hTρ h, Φ.operator_apply_of_mem hw hτ hTτ hTv,
    schwartzAction_intertwining hw hρ hτ hTρ hTτ]

/-- `π[φ]` composed with an intertwiner, as an identity of intertwiners. -/
theorem comp_operator (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ)
    (hτ : IsAdmissible τ) (hTρ : HasTemperedCoefficients Ξ σ ρ)
    (hTτ : HasTemperedCoefficients Ξ σ τ) (T : ρ.IntertwiningMap τ) :
    T.comp (Φ.operator hw hρ hTρ) = (Φ.operator hw hτ hTτ).comp T :=
  Representation.IntertwiningMap.ext (LinearMap.ext fun v =>
    Φ.operator_intertwining hw hρ hτ hTρ hTτ T v)

end IdempotentFamily

end Family

end Langlands.HarishChandraSchwartz

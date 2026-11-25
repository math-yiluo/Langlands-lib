import Langlands.Theta.Heisenberg.SchrodingerFourier

/-!
# The partial Fourier transform between two Schrödinger models

GKT §1.2.5 (**Theorem 1.27** and **Remark 1.28**, p. 35). Let `W = W₁ ⊕ W₂` be the orthogonal sum of
two polarized spaces `W₁ = X₁ × Y₁`, `W₂ = X₂ × Y₂` (`sumPairing β₁ β₂`). Besides the polarization
`(X₁ × X₂) × (Y₁ × Y₂)`, whose Schrödinger model lives on `S(X₁ × X₂)`, there is the polarization
with the roles of `X₁` and `Y₁` exchanged, `(Y₁ × X₂) × (X₁ × Y₂)` with the pairing
`sumPairing (-β₁.flip) β₂` (`partialSwapHeisenbergEquiv`), whose Schrödinger model lives on
`S(Y₁ × X₂)` (`schrodingerSBPartial`). In the book's notation (with its `X = X₁ ⊕ Z`,
`Y = Y₁ ⊕ Z`, `X ∩ Y = Z`) these are its two polarizations `(X₁ ⊕ Z) ⊕ (Y₁ ⊕ Z*)` and
`(Y₁ ⊕ Z) ⊕ (X₁ ⊕ Z*)`.

* `partialPairingFourier μ α φ (y₁, x₂) = ∫ α(x₁, y₁) φ(x₁, x₂) dμ(x₁)` for a perfect bicharacter
  `α`; it preserves Schwartz–Bruhat functions (`partialPairingFourier_mem`), is an isometry from
  `μ × ν` to `μ' × ν` for the dual measure `μ'` (`lintegral_enorm_partialPairingFourier_sq`), and
  is `ℱ ⊗ 1` on tensors (`partialPairingFourier_tensor`, Remark 1.28).
* `schrodingerPartialFourier β₁ hψ hψ1 μ`: the partial Fourier transform `F_{Y₁, X₁}` for
  `α = ψ ∘ β₁`; **Theorem 1.27**: it intertwines the two Schrödinger models
  (`schrodingerPartialFourier_schrodinger`) and is unitary
  (`lintegral_enorm_schrodingerPartialFourier_sq`).

The module also holds the orthogonal sum `sumPairing` of two pairings and the tensor
`schwartzBruhatTensor φ₁ φ₂` of two Schwartz–Bruhat functions, used for the blocks of
`Langlands.Theta.Metaplectic.Block`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace Langlands.HeisenbergGroup

open Langlands.HarmonicAnalysis
open Langlands.Theta (schwartzBruhatInner)

universe u v₁ w₁ v₂ w₂

section Tensor

variable {X₁ : Type v₁} {X₂ : Type v₂} [TopologicalSpace X₁] [TopologicalSpace X₂]

/-- **The tensor `φ₁ ⊗ φ₂`** of two Schwartz–Bruhat functions, `(x₁, x₂) ↦ φ₁(x₁) φ₂(x₂)` (GKT
Remark 1.28 and p. 64: `C_c^∞(Y) = C_c^∞(Y_S) ⊗ C_c^∞(Y_{S^c})`). -/
def schwartzBruhatTensor (φ₁ : SchwartzBruhat X₁) (φ₂ : SchwartzBruhat X₂) :
    SchwartzBruhat (X₁ × X₂) :=
  ⟨fun x => (φ₁ : X₁ → ℂ) x.1 * (φ₂ : X₂ → ℂ) x.2,
    IsLocallyConstant.comp₂ (φ₁.2.1.comp_continuous continuous_fst)
      (φ₂.2.1.comp_continuous continuous_snd) (· * ·),
    HasCompactSupport.intro' (φ₁.2.2.prod φ₂.2.2) ((isClosed_tsupport _).prod (isClosed_tsupport _))
      fun x hx => by
        rcases not_and_or.1 (Set.mem_prod.not.1 hx) with h | h
        · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
        · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]⟩

@[simp] theorem schwartzBruhatTensor_apply (φ₁ : SchwartzBruhat X₁) (φ₂ : SchwartzBruhat X₂)
    (x : X₁ × X₂) :
    (schwartzBruhatTensor φ₁ φ₂ : X₁ × X₂ → ℂ) x = (φ₁ : X₁ → ℂ) x.1 * (φ₂ : X₂ → ℂ) x.2 := rfl

theorem schwartzBruhatTensor_smul (a b : ℂ) (φ₁ : SchwartzBruhat X₁) (φ₂ : SchwartzBruhat X₂) :
    schwartzBruhatTensor (a • φ₁) (b • φ₂) = (a * b) • schwartzBruhatTensor φ₁ φ₂ :=
  Subtype.ext <| funext fun x => by
    change a * (φ₁ : X₁ → ℂ) x.1 * (b * (φ₂ : X₂ → ℂ) x.2) =
      a * b * ((φ₁ : X₁ → ℂ) x.1 * (φ₂ : X₂ → ℂ) x.2)
    ring

variable [MeasurableSpace X₁] [BorelSpace X₁] [MeasurableSpace X₂] [BorelSpace X₂]
  [SecondCountableTopology X₁]

/-- `⟨φ₁ ⊗ φ₂, φ₁' ⊗ φ₂'⟩ = ⟨φ₁, φ₁'⟩ ⟨φ₂, φ₂'⟩` for the product measure (Fubini). -/
theorem schwartzBruhatInner_tensor (ν₁ : Measure X₁) (ν₂ : Measure X₂)
    [IsFiniteMeasureOnCompacts (ν₁.prod ν₂)] [SFinite ν₁] [SFinite ν₂]
    [IsFiniteMeasureOnCompacts ν₁] [IsFiniteMeasureOnCompacts ν₂]
    (φ₁ φ₁' : SchwartzBruhat X₁) (φ₂ φ₂' : SchwartzBruhat X₂) :
    schwartzBruhatInner (ν₁.prod ν₂) (schwartzBruhatTensor φ₁ φ₂) (schwartzBruhatTensor φ₁' φ₂') =
      schwartzBruhatInner ν₁ φ₁ φ₁' * schwartzBruhatInner ν₂ φ₂ φ₂' := by
  change ∫ x, (starRingEnd ℂ) ((φ₁ : X₁ → ℂ) x.1 * (φ₂ : X₂ → ℂ) x.2) *
      ((φ₁' : X₁ → ℂ) x.1 * (φ₂' : X₂ → ℂ) x.2) ∂(ν₁.prod ν₂) =
    (∫ x, (starRingEnd ℂ) ((φ₁ : X₁ → ℂ) x) * (φ₁' : X₁ → ℂ) x ∂ν₁) *
      ∫ x, (starRingEnd ℂ) ((φ₂ : X₂ → ℂ) x) * (φ₂' : X₂ → ℂ) x ∂ν₂
  rw [← integral_prod_mul]
  congr 1
  funext x
  rw [map_mul]
  ring

end Tensor

section Sum

variable {R : Type u} [CommRing R]
  {X₁ : Type v₁} {Y₁ : Type w₁} {X₂ : Type v₂} {Y₂ : Type w₂}
  [AddCommGroup X₁] [Module R X₁] [AddCommGroup Y₁] [Module R Y₁]
  [AddCommGroup X₂] [Module R X₂] [AddCommGroup Y₂] [Module R Y₂]
  (β₁ : X₁ →ₗ[R] Y₁ →ₗ[R] R) (β₂ : X₂ →ₗ[R] Y₂ →ₗ[R] R)

/-- **The orthogonal sum of two pairings**: `((x₁, x₂), (y₁, y₂)) ↦ β₁(x₁, y₁) + β₂(x₂, y₂)`; its
polarized space is `W₁ ⊕ W₂` (GKT §1.2.5, p. 34, and §2.3.4, p. 67). -/
def sumPairing : (X₁ × X₂) →ₗ[R] (Y₁ × Y₂) →ₗ[R] R :=
  β₁.compl₁₂ (LinearMap.fst R X₁ X₂) (LinearMap.fst R Y₁ Y₂) +
    β₂.compl₁₂ (LinearMap.snd R X₁ X₂) (LinearMap.snd R Y₁ Y₂)

@[simp] theorem sumPairing_apply (x : X₁ × X₂) (y : Y₁ × Y₂) :
    sumPairing β₁ β₂ x y = β₁ x.1 y.1 + β₂ x.2 y.2 := rfl

/-- The form of `W₁ ⊕ W₂` is the sum of the forms of `W₁` and `W₂`. -/
theorem polarizedForm_sumPairing (w w' : (X₁ × X₂) × (Y₁ × Y₂)) :
    polarizedForm (sumPairing β₁ β₂) w w' =
      polarizedForm β₁ (w.1.1, w.2.1) (w'.1.1, w'.2.1) +
        polarizedForm β₂ (w.1.2, w.2.2) (w'.1.2, w'.2.2) := by
  simp only [polarizedForm_apply, sumPairing_apply]
  ring

/-- **The partial swap** `((x₁, x₂), (y₁, y₂)) ↦ ((y₁, x₂), (x₁, y₂))` carries the form of
`sumPairing β₁ β₂` to that of `sumPairing (-β₁.flip) β₂`. -/
theorem polarizedForm_partialSwap (w w' : (X₁ × X₂) × (Y₁ × Y₂)) :
    polarizedForm (sumPairing (-β₁.flip) β₂) ((w.2.1, w.1.2), (w.1.1, w.2.2))
        ((w'.2.1, w'.1.2), (w'.1.1, w'.2.2)) =
      polarizedForm (sumPairing β₁ β₂) w w' := by
  simp only [polarizedForm_apply, sumPairing_apply, LinearMap.neg_apply, LinearMap.flip_apply]
  ring

variable [Invertible (2 : R)]

/-- **The partial swap of the polarization** as an isomorphism of Heisenberg groups
`H(W, sumPairing β₁ β₂) ≃ H(W, sumPairing (-β₁.flip) β₂)`. -/
def partialSwapHeisenbergEquiv :
    HeisenbergGroup (polarizedForm (sumPairing β₁ β₂)) ≃*
      HeisenbergGroup (polarizedForm (sumPairing (-β₁.flip) β₂)) where
  toFun g := ⟨((g.vec.2.1, g.vec.1.2), (g.vec.1.1, g.vec.2.2)), g.cen⟩
  invFun g := ⟨((g.vec.2.1, g.vec.1.2), (g.vec.1.1, g.vec.2.2)), g.cen⟩
  left_inv g := rfl
  right_inv g := rfl
  map_mul' g h := by
    refine HeisenbergGroup.ext ?_ ?_
    · rfl
    · change g.cen + h.cen + ⅟2 * polarizedForm (sumPairing β₁ β₂) g.vec h.vec =
        g.cen + h.cen + ⅟2 * polarizedForm (sumPairing (-β₁.flip) β₂)
          ((g.vec.2.1, g.vec.1.2), (g.vec.1.1, g.vec.2.2))
          ((h.vec.2.1, h.vec.1.2), (h.vec.1.1, h.vec.2.2))
      rw [polarizedForm_partialSwap]

@[simp] theorem partialSwapHeisenbergEquiv_apply
    (g : HeisenbergGroup (polarizedForm (sumPairing β₁ β₂))) :
    partialSwapHeisenbergEquiv β₁ β₂ g =
      ⟨((g.vec.2.1, g.vec.1.2), (g.vec.1.1, g.vec.2.2)), g.cen⟩ := rfl

end Sum

section PerfPair

variable {K : Type u} [Field K]
  {X₁ : Type v₁} {Y₁ : Type w₁} {X₂ : Type v₂} {Y₂ : Type w₂}
  [AddCommGroup X₁] [Module K X₁] [AddCommGroup Y₁] [Module K Y₁]
  [AddCommGroup X₂] [Module K X₂] [AddCommGroup Y₂] [Module K Y₂]
  [FiniteDimensional K X₁] [FiniteDimensional K X₂]
  (β₁ : X₁ →ₗ[K] Y₁ →ₗ[K] K) (β₂ : X₂ →ₗ[K] Y₂ →ₗ[K] K)

/-- The orthogonal sum of two perfect pairings is perfect. -/
instance isPerfPair_sumPairing [β₁.IsPerfPair] [β₂.IsPerfPair] : (sumPairing β₁ β₂).IsPerfPair := by
  refine .of_injective ((injective_iff_map_eq_zero _).2 fun x hx => ?_)
    ((injective_iff_map_eq_zero _).2 fun y hy => ?_)
  · have h1 : β₁ x.1 = 0 := LinearMap.ext fun y => by
      simpa using LinearMap.congr_fun hx (y, 0)
    have h2 : β₂ x.2 = 0 := LinearMap.ext fun y => by
      simpa using LinearMap.congr_fun hx (0, y)
    exact Prod.ext ((injective_iff_map_eq_zero _).1 (LinearMap.IsPerfPair.bijective_left β₁).1 _ h1)
      ((injective_iff_map_eq_zero _).1 (LinearMap.IsPerfPair.bijective_left β₂).1 _ h2)
  · have h1 : β₁.flip y.1 = 0 := LinearMap.ext fun x => by
      simpa using LinearMap.congr_fun hy (x, 0)
    have h2 : β₂.flip y.2 = 0 := LinearMap.ext fun x => by
      simpa using LinearMap.congr_fun hy (0, x)
    exact Prod.ext
      ((injective_iff_map_eq_zero _).1 (LinearMap.IsPerfPair.bijective_right β₁).1 _ h1)
      ((injective_iff_map_eq_zero _).1 (LinearMap.IsPerfPair.bijective_right β₂).1 _ h2)

end PerfPair

section PartialPairingFourier

variable {X₁ : Type v₁} {Y₁ : Type w₁} {X₂ : Type v₂}
  [AddCommGroup X₁] [TopologicalSpace X₁] [IsTopologicalAddGroup X₁]
  [AddCommGroup Y₁] [TopologicalSpace Y₁] [IsTopologicalAddGroup Y₁]
  [AddCommGroup X₂] [TopologicalSpace X₂] [IsTopologicalAddGroup X₂]
  [MeasurableSpace X₁] {α : X₁ → Y₁ → ℂ}

/-- **The partial Fourier transform** `φ ↦ ((y₁, x₂) ↦ ∫ α(x₁, y₁) φ(x₁, x₂) dμ(x₁))` (GKT
Theorem 1.27): the Fourier transform in the first variable. -/
def partialPairingFourier (μ : Measure X₁) (α : X₁ → Y₁ → ℂ) (φ : X₁ × X₂ → ℂ) : Y₁ × X₂ → ℂ :=
  fun p => ∫ x, α x p.1 * φ (x, p.2) ∂μ

omit [AddCommGroup X₁] [TopologicalSpace X₁] [IsTopologicalAddGroup X₁] [AddCommGroup Y₁]
  [TopologicalSpace Y₁] [IsTopologicalAddGroup Y₁] [AddCommGroup X₂] [TopologicalSpace X₂]
  [IsTopologicalAddGroup X₂] in
theorem partialPairingFourier_apply (μ : Measure X₁) (φ : X₁ × X₂ → ℂ) (p : Y₁ × X₂) :
    partialPairingFourier μ α φ p = pairingFourier μ α (fun x => φ (x, p.2)) p.1 := rfl

omit [AddCommGroup X₁] [TopologicalSpace X₁] [IsTopologicalAddGroup X₁] [AddCommGroup Y₁]
  [TopologicalSpace Y₁] [IsTopologicalAddGroup Y₁] [AddCommGroup X₂] [TopologicalSpace X₂]
  [IsTopologicalAddGroup X₂] in
/-- **Remark 1.28**: on a tensor, the partial Fourier transform is `ℱ ⊗ 1`. -/
theorem partialPairingFourier_tensor (μ : Measure X₁) (φ₁ : X₁ → ℂ) (φ₂ : X₂ → ℂ) :
    partialPairingFourier μ α (fun x => φ₁ x.1 * φ₂ x.2) =
      fun p => pairingFourier μ α φ₁ p.1 * φ₂ p.2 := by
  funext p
  change ∫ x, α x p.1 * (φ₁ x * φ₂ p.2) ∂μ = (∫ x, α x p.1 * φ₁ x ∂μ) * φ₂ p.2
  rw [← integral_mul_const]
  simp_rw [mul_assoc]

variable [T2Space Y₁]

omit [IsTopologicalAddGroup Y₁] in
/-- **The partial Fourier transform preserves Schwartz–Bruhat functions** (the first step of
Theorem 1.27): locally constant in `y₁` uniformly on the compact projection of the support, and in
`x₂` by the invariance of `φ` under small translations; supported in `K × pr₂(supp φ)`, where `K`
is the compact set of the `y₁` on which `α(·, y₁)` is trivial on a neighbourhood of `0` fixing
`φ` by translation. -/
theorem partialPairingFourier_mem [BorelSpace X₁] (μ : Measure X₁) [μ.IsAddHaarMeasure]
    (h : IsPerfectBicharacter α) {φ : X₁ × X₂ → ℂ}
    (hφ : φ ∈ schwartzBruhatSubmodule (X₁ × X₂)) :
    partialPairingFourier μ α φ ∈ schwartzBruhatSubmodule (Y₁ × X₂) := by
  have hinv := HarmonicAnalysis.eventually_add_eq_of_mem_schwartzBruhatSubmodule hφ
  have hinv₁ : ∀ᶠ t in 𝓝 (0 : X₁), ∀ x, φ (x + (t, 0)) = φ x := by
    have ht : Tendsto (fun t : X₁ => ((t, 0) : X₁ × X₂)) (𝓝 0) (𝓝 0) :=
      (continuous_id.prodMk continuous_const).tendsto' 0 0 rfl
    exact ht.eventually hinv
  have hinv₂ : ∀ᶠ t in 𝓝 (0 : X₂), ∀ x, φ (x + (0, t)) = φ x := by
    have ht : Tendsto (fun t : X₂ => ((0, t) : X₁ × X₂)) (𝓝 0) (𝓝 0) :=
      (continuous_const.prodMk continuous_id).tendsto' 0 0 rfl
    exact ht.eventually hinv
  have hK₁ : IsCompact (Prod.fst '' tsupport φ) := hφ.2.image continuous_fst
  have hK₂ : IsCompact (Prod.snd '' tsupport φ) := hφ.2.image continuous_snd
  have hzero₁ : ∀ x₁ x₂, x₁ ∉ Prod.fst '' tsupport φ → φ (x₁, x₂) = 0 := fun x₁ x₂ hx =>
    image_eq_zero_of_notMem_tsupport fun hm => hx ⟨_, hm, rfl⟩
  have hzero₂ : ∀ x₁ x₂, x₂ ∉ Prod.snd '' tsupport φ → φ (x₁, x₂) = 0 := fun x₁ x₂ hx =>
    image_eq_zero_of_notMem_tsupport fun hm => hx ⟨_, hm, rfl⟩
  obtain ⟨K, hK, hKm⟩ := h.big_left _ hinv₁
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun p => ?_,
    HasCompactSupport.intro (hK.prod hK₂) fun p hp => ?_⟩
  · obtain ⟨y, x₂⟩ := p
    have h1 : ∀ᶠ z in 𝓝 y, ∀ x ∈ Prod.fst '' tsupport φ, α x z = α x y := by
      refine IsCompact.eventually_forall_of_forall_eventually hK₁ fun x _ => ?_
      have h2 : IsLocallyConstant fun q : Y₁ × X₁ => (α q.2 q.1, α q.2 y) :=
        (h.isLocallyConstant.comp_continuous continuous_swap).prodMk
          (h.isLocallyConstant.comp_continuous (continuous_snd.prodMk continuous_const))
      filter_upwards [h2.eventually_eq (y, x)] with q hq
      simp only [Prod.mk.injEq] at hq
      rw [hq.1, hq.2]
    have h2 : ∀ᶠ z in 𝓝 x₂, ∀ x, φ (x, z) = φ (x, x₂) := by
      have ht : Tendsto (fun z => z - x₂) (𝓝 x₂) (𝓝 0) :=
        (continuous_id.sub continuous_const).tendsto' x₂ 0 (sub_self x₂)
      filter_upwards [ht.eventually hinv₂] with z hz x
      have := hz (x, x₂)
      simpa using this
    filter_upwards [h1.prod_nhds h2] with q hq
    change ∫ x, α x q.1 * φ (x, q.2) ∂μ = ∫ x, α x y * φ (x, x₂) ∂μ
    congr 1
    funext x
    rw [hq.2 x]
    by_cases hx : x ∈ Prod.fst '' tsupport φ
    · rw [hq.1 x hx]
    · rw [hzero₁ x x₂ hx, mul_zero, mul_zero]
  · obtain ⟨y, x₂⟩ := p
    rcases not_and_or.1 (Set.mem_prod.not.1 hp) with hy | hx₂
    · obtain ⟨t, ht, hne⟩ : ∃ t, (∀ x, φ (x + (t, 0)) = φ x) ∧ α t y ≠ 1 := by
        by_contra hne
        exact hy (hKm y fun t ht => by
          by_contra h4
          exact hne ⟨t, ht, h4⟩)
      have h1 := integral_add_right_eq_self (μ := μ) (fun x => α x y * φ (x, x₂)) t
      have h2 : ∀ x, α (x + t) y * φ (x + t, x₂) = α t y * (α x y * φ (x, x₂)) := by
        intro x
        have := ht (x, x₂)
        simp only [Prod.mk_add_mk, add_zero] at this
        rw [this, h.map_add_left]
        ring
      simp only [h2, integral_const_mul] at h1
      refine (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hne)
      change (α t y - 1) * ∫ x, α x y * φ (x, x₂) ∂μ = 0
      rw [sub_mul, h1, one_mul, sub_self]
    · change ∫ x, α x y * φ (x, x₂) ∂μ = 0
      simp [hzero₂ _ x₂ hx₂]

variable [LocallyCompactSpace X₁] [SecondCountableTopology X₁] [BorelSpace X₁]
  [CompactOpenExhaustion X₁] [LocallyCompactSpace Y₁] [SecondCountableTopology Y₁]
  [MeasurableSpace Y₁] [BorelSpace Y₁] [CompactOpenExhaustion Y₁]
  [MeasurableSpace X₂] [BorelSpace X₂] [SecondCountableTopology X₂]

/-- **The partial Fourier transform is an isometry** from `μ × ν` to `μ' × ν`, `μ'` the dual
measure of `μ` (the unitarity of Theorem 1.27): Plancherel in the first variable and Tonelli. -/
theorem lintegral_enorm_partialPairingFourier_sq (μ : Measure X₁) [μ.IsAddHaarMeasure]
    (h : IsPerfectBicharacter α) (ν : Measure X₂) [SFinite ν] {φ : X₁ × X₂ → ℂ}
    (hφ : φ ∈ schwartzBruhatSubmodule (X₁ × X₂)) :
    ∫⁻ p, ‖partialPairingFourier μ α φ p‖ₑ ^ 2 ∂((pairingDualMeasure μ α).prod ν) =
      ∫⁻ p, ‖φ p‖ₑ ^ 2 ∂(μ.prod ν) := by
  have := isAddHaarMeasure_pairingDualMeasure h μ
  have hF := partialPairingFourier_mem μ h hφ
  have hmF : AEMeasurable (fun p => ‖partialPairingFourier μ α φ p‖ₑ ^ 2)
      ((pairingDualMeasure μ α).prod ν) :=
    ((ENNReal.continuous_pow 2).comp hF.1.continuous.enorm).measurable.aemeasurable
  have hmφ : AEMeasurable (fun p => ‖φ p‖ₑ ^ 2) (μ.prod ν) :=
    ((ENNReal.continuous_pow 2).comp hφ.1.continuous.enorm).measurable.aemeasurable
  rw [lintegral_prod_symm _ hmF, lintegral_prod_symm _ hmφ]
  congr 1
  funext x₂
  have hs : (fun x => φ (x, x₂)) ∈ schwartzBruhatSubmodule X₁ :=
    ⟨hφ.1.comp_continuous (continuous_id.prodMk continuous_const),
      HasCompactSupport.intro (hφ.2.image continuous_fst) fun x hx =>
        image_eq_zero_of_notMem_tsupport fun hm => hx ⟨_, hm, rfl⟩⟩
  exact lintegral_enorm_pairingFourier_sq_pairingDualMeasure h μ hs

end PartialPairingFourier

section Local

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Invertible (2 : F)]
  {X₁ : Type v₁} [AddCommGroup X₁] [Module F X₁] [FiniteDimensional F X₁] [TopologicalSpace X₁]
  [IsModuleTopology F X₁] [IsTopologicalAddGroup X₁]
  {Y₁ : Type w₁} [AddCommGroup Y₁] [Module F Y₁] [FiniteDimensional F Y₁] [TopologicalSpace Y₁]
  [IsModuleTopology F Y₁] [IsTopologicalAddGroup Y₁]
  {X₂ : Type v₂} [AddCommGroup X₂] [Module F X₂] [FiniteDimensional F X₂] [TopologicalSpace X₂]
  [IsModuleTopology F X₂] [IsTopologicalAddGroup X₂]
  {Y₂ : Type w₂} [AddCommGroup Y₂] [Module F Y₂] [FiniteDimensional F Y₂] [TopologicalSpace Y₂]
  [IsModuleTopology F Y₂]
  {β₁ : X₁ →ₗ[F] Y₁ →ₗ[F] F} {β₂ : X₂ →ₗ[F] Y₂ →ₗ[F] F} {ψ : AddChar F ℂ}

variable (β₁ β₂) in
omit [Invertible (2 : F)] [IsTopologicalAddGroup X₁] [FiniteDimensional F Y₁]
  [IsTopologicalAddGroup Y₁] [IsTopologicalAddGroup X₂] [FiniteDimensional F Y₂] in
/-- `x ↦ β₁(x₁, y₁) + β₂(x₂, y₂)` is continuous. -/
theorem continuous_sumPairing_left (y : Y₁ × Y₂) :
    Continuous fun x : X₁ × X₂ => sumPairing β₁ β₂ x y :=
  (((continuous_pairing β₁).comp (continuous_fst.prodMk continuous_const)).add
    ((continuous_pairing β₂).comp (continuous_snd.prodMk continuous_const)))

variable (β₁ β₂) in
omit [Invertible (2 : F)] [IsTopologicalAddGroup X₁] [FiniteDimensional F Y₁]
  [IsTopologicalAddGroup Y₁] [IsTopologicalAddGroup X₂] [FiniteDimensional F Y₂] in
/-- `(y₁, x₂) ↦ -β₁(x₁, y₁) + β₂(x₂, y₂)` is continuous. -/
theorem continuous_sumPairing_neg_flip_left (x : X₁ × Y₂) :
    Continuous fun v : Y₁ × X₂ => sumPairing (-β₁.flip) β₂ v x := by
  simp only [sumPairing_apply, LinearMap.neg_apply, LinearMap.flip_apply]
  exact ((continuous_pairing β₁).comp (continuous_const.prodMk continuous_fst)).neg.add
    ((continuous_pairing β₂).comp (continuous_snd.prodMk continuous_const))

variable (hψ : Continuous ψ)

/-- **The Schrödinger model on `S(Y₁ × X₂)`** of the polarization `(Y₁ × X₂) × (X₁ × Y₂)` (the
book's `C_c^∞(X₁ ⊕ Z*)`): the Schrödinger model of `sumPairing (-β₁.flip) β₂` read through the
partial swap. -/
def schrodingerSBPartial :
    Representation ℂ (HeisenbergGroup (polarizedForm (sumPairing β₁ β₂)))
      (SchwartzBruhat (Y₁ × X₂)) :=
  (schrodingerSB hψ (continuous_sumPairing_neg_flip_left β₁ β₂)).comp
    (partialSwapHeisenbergEquiv β₁ β₂).toMonoidHom

omit [IsTopologicalAddGroup X₁] [FiniteDimensional F Y₁] [FiniteDimensional F Y₂] in
theorem schrodingerSBPartial_apply (g : HeisenbergGroup (polarizedForm (sumPairing β₁ β₂)))
    (f : SchwartzBruhat (Y₁ × X₂)) (p : Y₁ × X₂) :
    (schrodingerSBPartial hψ g f : Y₁ × X₂ → ℂ) p =
      ψ g.cen * (ψ (-β₁ g.vec.1.1 p.1 + β₂ p.2 g.vec.2.2 +
        ⅟2 * (-β₁ g.vec.1.1 g.vec.2.1 + β₂ g.vec.1.2 g.vec.2.2)) *
          (f : Y₁ × X₂ → ℂ) (p.1 + g.vec.2.1, p.2 + g.vec.1.2)) := by
  change ψ g.cen • schrodingerFun ψ (sumPairing (-β₁.flip) β₂)
    ((g.vec.2.1, g.vec.1.2), (g.vec.1.1, g.vec.2.2)) f p = _
  simp only [schrodingerFun_apply, sumPairing_apply, LinearMap.neg_apply, LinearMap.flip_apply,
    smul_eq_mul]
  rfl

section Fourier

variable [MeasurableSpace X₁] [BorelSpace X₁] [MeasurableSpace Y₁] [BorelSpace Y₁]
  [MeasurableSpace X₂] [BorelSpace X₂] [β₁.IsPerfPair] (hψ1 : ψ ≠ 1)
  (μ : Measure X₁) [μ.IsAddHaarMeasure]

variable (β₁) in
/-- **The partial Fourier transform `F_{Y₁, X₁}`** (GKT Theorem 1.27):
`φ ↦ ((y₁, x₂) ↦ ∫ ψ(β₁(x₁, y₁)) φ(x₁, x₂) dμ(x₁))`, from the Schrödinger model on `S(X₁ × X₂)`
to the one on `S(Y₁ × X₂)`. -/
def schrodingerPartialFourier : SchwartzBruhat (X₁ × X₂) →ₗ[ℂ] SchwartzBruhat (Y₁ × X₂) where
  toFun φ := ⟨partialPairingFourier μ (fun x y => ψ (β₁ x y)) φ, by
    have := t2Space_of_finiteDimensional F Y₁
    exact partialPairingFourier_mem μ (isPerfectBicharacter_psi_pairing (β := β₁) hψ hψ1) φ.2⟩
  map_add' φ φ' := Subtype.ext <| funext fun p => by
    have hc := (isPerfectBicharacter_psi_pairing (β := β₁) hψ hψ1).continuous
    have hi : ∀ f : SchwartzBruhat (X₁ × X₂),
        Integrable (fun x => ψ (β₁ x p.1) * (f : X₁ × X₂ → ℂ) (x, p.2)) μ := fun f => by
      have hs : HasCompactSupport fun x => (f : X₁ × X₂ → ℂ) (x, p.2) := by
        have := t2Space_of_finiteDimensional F X₁
        exact HasCompactSupport.intro (f.2.2.image continuous_fst) fun x hx =>
          image_eq_zero_of_notMem_tsupport fun hm => hx ⟨_, hm, rfl⟩
      exact ((hc.comp (continuous_id.prodMk continuous_const)).mul
        (f.continuous.comp (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
          hs.mul_left
    change ∫ x, ψ (β₁ x p.1) * ((φ : X₁ × X₂ → ℂ) (x, p.2) + φ' (x, p.2)) ∂μ =
      (∫ x, ψ (β₁ x p.1) * (φ : X₁ × X₂ → ℂ) (x, p.2) ∂μ) +
        ∫ x, ψ (β₁ x p.1) * (φ' : X₁ × X₂ → ℂ) (x, p.2) ∂μ
    simp_rw [mul_add]
    exact integral_add (hi φ) (hi φ')
  map_smul' a φ := Subtype.ext <| funext fun p => by
    change ∫ x, ψ (β₁ x p.1) * (a * (φ : X₁ × X₂ → ℂ) (x, p.2)) ∂μ =
      a * ∫ x, ψ (β₁ x p.1) * (φ : X₁ × X₂ → ℂ) (x, p.2) ∂μ
    simp_rw [mul_left_comm _ a]
    exact integral_const_mul a _

omit [Invertible (2 : F)] [IsTopologicalAddGroup Y₁] [MeasurableSpace Y₁] [BorelSpace Y₁]
  [MeasurableSpace X₂] [BorelSpace X₂] [Module F X₂] [FiniteDimensional F X₂]
  [IsModuleTopology F X₂] in
theorem schrodingerPartialFourier_apply (φ : SchwartzBruhat (X₁ × X₂)) (p : Y₁ × X₂) :
    (schrodingerPartialFourier β₁ hψ hψ1 μ φ : Y₁ × X₂ → ℂ) p =
      ∫ x, ψ (β₁ x p.1) * (φ : X₁ × X₂ → ℂ) (x, p.2) ∂μ := rfl

omit [MeasurableSpace Y₁] [BorelSpace Y₁] [MeasurableSpace X₂] [BorelSpace X₂]
  [FiniteDimensional F Y₂] in
/-- **GKT Theorem 1.27, intertwining**: `F_{Y₁, X₁} ∘ σ(h) = σ'(h) ∘ F_{Y₁, X₁}` for the
Schrödinger models `σ` on `S(X₁ × X₂)` and `σ'` on `S(Y₁ × X₂)`. -/
theorem schrodingerPartialFourier_schrodinger
    (g : HeisenbergGroup (polarizedForm (sumPairing β₁ β₂))) (φ : SchwartzBruhat (X₁ × X₂)) :
    schrodingerPartialFourier β₁ hψ hψ1 μ
        (schrodingerSB hψ (continuous_sumPairing_left β₁ β₂) g φ) =
      schrodingerSBPartial hψ g (schrodingerPartialFourier β₁ hψ hψ1 μ φ) := by
  obtain ⟨⟨⟨x₀₁, x₀₂⟩, ⟨y₀₁, y₀₂⟩⟩, t⟩ := g
  refine Subtype.ext (funext fun p => ?_)
  obtain ⟨y, x₂⟩ := p
  rw [schrodingerSBPartial_apply, schrodingerPartialFourier_apply,
    schrodingerPartialFourier_apply]
  have h := integral_add_right_eq_self (μ := μ) (fun x => ψ (β₁ x y) *
    (schrodingerSB hψ (continuous_sumPairing_left β₁ β₂) ⟨((x₀₁, x₀₂), (y₀₁, y₀₂)), t⟩ φ :
      X₁ × X₂ → ℂ) (x, x₂)) (-x₀₁)
  rw [← h]
  have h2 : (⅟2 : F) + ⅟2 = 1 := by rw [← two_mul, mul_invOf_self]
  have e : ∀ x, ψ (β₁ (x + -x₀₁) y) * (schrodingerSB hψ (continuous_sumPairing_left β₁ β₂)
      ⟨((x₀₁, x₀₂), (y₀₁, y₀₂)), t⟩ φ : X₁ × X₂ → ℂ) (x + -x₀₁, x₂) =
      ψ t * (ψ (-β₁ x₀₁ y + β₂ x₂ y₀₂ + ⅟2 * (-β₁ x₀₁ y₀₁ + β₂ x₀₂ y₀₂)) *
        (ψ (β₁ x (y + y₀₁)) * (φ : X₁ × X₂ → ℂ) (x, x₂ + x₀₂))) := fun x => by
    rw [schrodingerSB_apply, schrodinger_apply, Pi.smul_apply, schrodingerFun_apply, smul_eq_mul]
    simp only [sumPairing_apply, Prod.mk_add_mk, neg_add_cancel_right]
    have hph : β₁ (x + -x₀₁) y + (β₁ (x + -x₀₁) y₀₁ + β₂ x₂ y₀₂ +
        ⅟2 * (β₁ x₀₁ y₀₁ + β₂ x₀₂ y₀₂)) =
        (-β₁ x₀₁ y + β₂ x₂ y₀₂ + ⅟2 * (-β₁ x₀₁ y₀₁ + β₂ x₀₂ y₀₂)) + β₁ x (y + y₀₁) := by
      simp only [map_add, map_neg, LinearMap.add_apply, LinearMap.neg_apply]
      linear_combination (β₁ x₀₁ y₀₁) * h2
    calc ψ (β₁ (x + -x₀₁) y) * (ψ t * (ψ (β₁ (x + -x₀₁) y₀₁ + β₂ x₂ y₀₂ +
          ⅟2 * (β₁ x₀₁ y₀₁ + β₂ x₀₂ y₀₂)) * (φ : X₁ × X₂ → ℂ) (x, x₂ + x₀₂)))
        = ψ t * (ψ (β₁ (x + -x₀₁) y + (β₁ (x + -x₀₁) y₀₁ + β₂ x₂ y₀₂ +
          ⅟2 * (β₁ x₀₁ y₀₁ + β₂ x₀₂ y₀₂))) * (φ : X₁ × X₂ → ℂ) (x, x₂ + x₀₂)) := by
          simp only [AddChar.map_add_eq_mul]; ring
      _ = ψ t * (ψ ((-β₁ x₀₁ y + β₂ x₂ y₀₂ + ⅟2 * (-β₁ x₀₁ y₀₁ + β₂ x₀₂ y₀₂)) +
          β₁ x (y + y₀₁)) * (φ : X₁ × X₂ → ℂ) (x, x₂ + x₀₂)) := by rw [hph]
      _ = _ := by rw [AddChar.map_add_eq_mul]; ring
  simp only [e, integral_const_mul]

omit [Invertible (2 : F)] in
/-- **GKT Theorem 1.27, unitarity**: for the dual measure `μ'` of `μ` and every measure `ν` on `X₂`,
`∫ |F φ|² d(μ' × ν) = ∫ |φ|² d(μ × ν)`. -/
theorem lintegral_enorm_schrodingerPartialFourier_sq (ν : Measure X₂) [SFinite ν]
    (φ : SchwartzBruhat (X₁ × X₂)) :
    ∫⁻ p, ‖(schrodingerPartialFourier β₁ hψ hψ1 μ φ : Y₁ × X₂ → ℂ) p‖ₑ ^ 2
        ∂((pairingDualMeasure μ fun x y => ψ (β₁ x y)).prod ν) =
      ∫⁻ p, ‖(φ : X₁ × X₂ → ℂ) p‖ₑ ^ 2 ∂(μ.prod ν) := by
  have := t2Space_of_finiteDimensional F Y₁
  have := locallyCompactSpace_of_finiteDimensional F X₁
  have := locallyCompactSpace_of_finiteDimensional F Y₁
  have := secondCountableTopology_of_finiteDimensional F X₁
  have := secondCountableTopology_of_finiteDimensional F Y₁
  have := secondCountableTopology_of_finiteDimensional F X₂
  have := compactOpenExhaustion_of_finiteDimensional F X₁
  have := compactOpenExhaustion_of_finiteDimensional F Y₁
  exact lintegral_enorm_partialPairingFourier_sq μ
    (isPerfectBicharacter_psi_pairing (β := β₁) hψ hψ1) ν φ.2

omit [Invertible (2 : F)] [Module F X₂] [FiniteDimensional F X₂] [IsModuleTopology F X₂]
  [MeasurableSpace Y₁] [BorelSpace Y₁] [MeasurableSpace X₂] [BorelSpace X₂] in
/-- **GKT Remark 1.28**: on a tensor `φ₁ ⊗ φ₂`, `F_{Y₁, X₁}` is the Fourier transform of
Theorem 1.25 on the first factor and the identity on the second. -/
theorem schrodingerPartialFourier_tensor (φ₁ : SchwartzBruhat X₁) (φ₂ : SchwartzBruhat X₂) :
    schrodingerPartialFourier β₁ hψ hψ1 μ (schwartzBruhatTensor φ₁ φ₂) =
      schwartzBruhatTensor (schrodingerFourier β₁ hψ hψ1 μ φ₁) φ₂ :=
  Subtype.ext (partialPairingFourier_tensor (α := fun x y => ψ (β₁ x y)) μ (φ₁ : X₁ → ℂ)
    (φ₂ : X₂ → ℂ))

end Fourier

end Local

end Langlands.HeisenbergGroup

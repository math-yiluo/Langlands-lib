import Langlands.Representation.Whittaker.CompletenessPairing
import Langlands.Representation.RankinSelberg.SupercuspidalCompleteness.CompactGrading
import Langlands.Representation.Twist.Definitions

/-!
# Delta functions in compact induction from a character

Let `N` be a subgroup of a topological group `G` and `θ : N →* ℂˣ` a character. For an open
subgroup `K` and `g ∈ G` such that `θ` is trivial on `N ∩ g K g⁻¹`, the function supported on
`N g K` with value `θ(n)` at `n g k` lies in `c-Ind_N^G θ` when `K` is compact. Its integral
against a right `K`-invariant `θ⁻¹`-equivariant function `f` over `N \ G` is `f(g)` times the
measure of the image of `g K`.
-/

noncomputable section

namespace Langlands.RankinSelberg.SupercuspidalCompleteness

open MeasureTheory QuotientIntegration Induction Whittaker.CompletenessPairing

universe uG

section Delta

variable {G : Type uG} [Group G] (N : Subgroup G) (θ : N →* ℂˣ)

/-- The character is trivial on `N ∩ g K g⁻¹`. -/
def IsGood (K : Subgroup G) (g : G) : Prop :=
  ∀ n : N, g⁻¹ * (n : G) * g ∈ K → θ n = 1

open Classical in
/-- The function on `N g K` with value `θ(n)` at `n g k`, and zero elsewhere. -/
def deltaFun (K : Subgroup G) (g : G) (x : G) : ℂ :=
  if h : ∃ n : N, ∃ k ∈ K, x = (n : G) * (g * k) then (θ h.choose : ℂ) else 0

variable {N θ}

theorem deltaFun_apply {K : Subgroup G} {g : G} (hg : IsGood N θ K g) (n : N) {k : G}
    (hk : k ∈ K) : deltaFun N θ K g ((n : G) * (g * k)) = θ n := by
  have h : ∃ n' : N, ∃ k' ∈ K, (n : G) * (g * k) = (n' : G) * (g * k') := ⟨n, k, hk, rfl⟩
  rw [deltaFun, dif_pos h]
  obtain ⟨k', hk', he⟩ := h.choose_spec
  set n' := h.choose
  -- `n'⁻¹ n = g k' k⁻¹ g⁻¹`
  have hmem : g⁻¹ * ((n'⁻¹ * n : N) : G) * g ∈ K := by
    have : g⁻¹ * ((n'⁻¹ * n : N) : G) * g = k' * k⁻¹ := by
      have he' : (n'⁻¹ : G) * n = g * k' * k⁻¹ * g⁻¹ := by
        calc (n'⁻¹ : G) * n = (n'⁻¹ : G) * ((n : G) * (g * k)) * k⁻¹ * g⁻¹ := by group
          _ = (n'⁻¹ : G) * ((n' : G) * (g * k')) * k⁻¹ * g⁻¹ := by rw [he]
          _ = g * k' * k⁻¹ * g⁻¹ := by group
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, he']
      group
    rw [this]
    exact K.mul_mem hk' (K.inv_mem hk)
  have h1 := hg _ hmem
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  rw [h1]

theorem deltaFun_eq_zero {K : Subgroup G} {g x : G}
    (hx : ¬ ∃ n : N, ∃ k ∈ K, x = (n : G) * (g * k)) : deltaFun N θ K g x = 0 := by
  rw [deltaFun, dif_neg hx]

theorem deltaFun_left {K : Subgroup G} {g : G} (hg : IsGood N θ K g) (m : N) (x : G) :
    deltaFun N θ K g ((m : G) * x) = (θ m : ℂ) * deltaFun N θ K g x := by
  by_cases hx : ∃ n : N, ∃ k ∈ K, x = (n : G) * (g * k)
  · obtain ⟨n, k, hk, rfl⟩ := hx
    rw [← mul_assoc, ← Subgroup.coe_mul, deltaFun_apply hg _ hk, deltaFun_apply hg _ hk,
      map_mul, Units.val_mul]
  · have hmx : ¬ ∃ n : N, ∃ k ∈ K, (m : G) * x = (n : G) * (g * k) := by
      rintro ⟨n, k, hk, he⟩
      refine hx ⟨m⁻¹ * n, k, hk, ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, ← he]
      group
    rw [deltaFun_eq_zero hmx, deltaFun_eq_zero hx, mul_zero]

theorem deltaFun_right {K : Subgroup G} {g : G} (hg : IsGood N θ K g) (x : G) {k : G}
    (hk : k ∈ K) : deltaFun N θ K g (x * k) = deltaFun N θ K g x := by
  by_cases hx : ∃ n : N, ∃ k' ∈ K, x = (n : G) * (g * k')
  · obtain ⟨n, k', hk', rfl⟩ := hx
    have he : (n : G) * (g * k') * k = (n : G) * (g * (k' * k)) := by group
    rw [he, deltaFun_apply hg _ (K.mul_mem hk' hk), deltaFun_apply hg _ hk']
  · have hxk : ¬ ∃ n : N, ∃ k' ∈ K, x * k = (n : G) * (g * k') := by
      rintro ⟨n, k', hk', he⟩
      refine hx ⟨n, k' * k⁻¹, K.mul_mem hk' (K.inv_mem hk), ?_⟩
      calc x = x * k * k⁻¹ := by group
        _ = (n : G) * (g * k') * k⁻¹ := by rw [he]
        _ = (n : G) * (g * (k' * k⁻¹)) := by group
    rw [deltaFun_eq_zero hxk, deltaFun_eq_zero hx]

theorem isGood_mul_left {K : Subgroup G} {g : G} (m : N) :
    IsGood N θ K ((m : G) * g) ↔ IsGood N θ K g := by
  constructor
  · intro h n hn
    have hmem : ((m : G) * g)⁻¹ * ((m * n * m⁻¹ : N) : G) * ((m : G) * g) ∈ K := by
      have : ((m : G) * g)⁻¹ * ((m * n * m⁻¹ : N) : G) * ((m : G) * g) =
          g⁻¹ * (n : G) * g := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [this]
      exact hn
    have := h _ hmem
    rwa [map_mul, map_mul, map_inv, mul_inv_cancel_comm] at this
  · intro h n hn
    have hmem : g⁻¹ * ((m⁻¹ * n * m : N) : G) * g ∈ K := by
      have : g⁻¹ * ((m⁻¹ * n * m : N) : G) * g = ((m : G) * g)⁻¹ * (n : G) * ((m : G) * g) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [this]
      exact hn
    have := h _ hmem
    rwa [map_mul, map_mul, map_inv, inv_mul_cancel_comm] at this

theorem isGood_mul_right {K : Subgroup G} {g k : G} (hk : k ∈ K) :
    IsGood N θ K (g * k) ↔ IsGood N θ K g := by
  constructor
  · intro h n hn
    apply h n
    have : (g * k)⁻¹ * (n : G) * (g * k) = k⁻¹ * (g⁻¹ * (n : G) * g) * k := by group
    rw [this]
    exact K.mul_mem (K.mul_mem (K.inv_mem hk) hn) hk
  · intro h n hn
    apply h n
    have : g⁻¹ * (n : G) * g = k * ((g * k)⁻¹ * (n : G) * (g * k)) * k⁻¹ := by group
    rw [this]
    exact K.mul_mem (K.mul_mem hk hn) (K.inv_mem hk)

theorem IsGood.mono {K K' : Subgroup G} {g : G} (h : IsGood N θ K g) (hK : K' ≤ K) :
    IsGood N θ K' g := fun n hn => h n (hK hn)

theorem deltaFun_mul_left {K : Subgroup G} {g : G} (hg : IsGood N θ K g) (m : N) (x : G) :
    deltaFun N θ K ((m : G) * g) x = ((θ m)⁻¹ : ℂˣ) * deltaFun N θ K g x := by
  have hmg : IsGood N θ K ((m : G) * g) := (isGood_mul_left m).mpr hg
  by_cases hx : ∃ n : N, ∃ k ∈ K, x = (n : G) * (g * k)
  · obtain ⟨n, k, hk, rfl⟩ := hx
    have he : (n : G) * (g * k) = ((n * m⁻¹ : N) : G) * (((m : G) * g) * k) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [deltaFun_apply hg _ hk, he, deltaFun_apply hmg _ hk, map_mul, map_inv]
    simp only [Units.val_mul]
    ring
  · have hx' : ¬ ∃ n : N, ∃ k ∈ K, x = (n : G) * (((m : G) * g) * k) := by
      rintro ⟨n, k, hk, rfl⟩
      exact hx ⟨n * m, k, hk, by simp only [Subgroup.coe_mul]; group⟩
    rw [deltaFun_eq_zero hx, deltaFun_eq_zero hx', mul_zero]

theorem deltaFun_mul_right {K : Subgroup G} {g : G} (hg : IsGood N θ K g) {k : G} (hk : k ∈ K)
    (x : G) : deltaFun N θ K (g * k) x = deltaFun N θ K g x := by
  have hgk : IsGood N θ K (g * k) := (isGood_mul_right hk).mpr hg
  by_cases hx : ∃ n : N, ∃ k' ∈ K, x = (n : G) * (g * k')
  · obtain ⟨n, k', hk', rfl⟩ := hx
    have he : (n : G) * (g * k') = (n : G) * ((g * k) * (k⁻¹ * k')) := by group
    rw [deltaFun_apply hg _ hk', he, deltaFun_apply hgk _ (K.mul_mem (K.inv_mem hk) hk')]
  · have hx' : ¬ ∃ n : N, ∃ k' ∈ K, x = (n : G) * ((g * k) * k') := by
      rintro ⟨n, k', hk', rfl⟩
      exact hx ⟨n, k * k', K.mul_mem hk hk', by group⟩
    rw [deltaFun_eq_zero hx, deltaFun_eq_zero hx']

end Delta

section DeltaVector

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {N : Subgroup G} {θ : N →* ℂˣ}

/-- The delta function as a vector of the compact induction `c-Ind_N^G θ`. -/
def deltaVector (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (hg : IsGood N θ K g) : CompactFunctions N (characterRepresentation θ) :=
  let s : SmoothFunctions N (characterRepresentation θ) :=
    smoothFunctionOf N (characterRepresentation θ) (deltaFun N θ K g)
      (fun m x => by
        rw [deltaFun_left hg m x]
        rfl)
      K (fun k x => deltaFun_right hg x k.property)
  ⟨s, by
    apply (hK.image (f := fun k : G => (Quotient.mk _ (g * k) : Induction.LeftQuotient N))
      ((continuous_quot_mk).comp (continuous_const.mul continuous_id))).of_isClosed_subset
      (isClosed_quotientSupport s)
    rintro _ ⟨x, hx, rfl⟩
    by_cases h : ∃ n : N, ∃ k ∈ (K : Subgroup G), x = (n : G) * (g * k)
    · obtain ⟨n, k, hk, rfl⟩ := h
      refine ⟨k, hk, ?_⟩
      apply Quotient.sound
      change QuotientGroup.rightRel _ (g * k) ((n : G) * (g * k))
      rw [QuotientGroup.rightRel_apply]
      simpa [mul_assoc] using n.property
    · exact absurd (deltaFun_eq_zero h) hx⟩

theorem eval_deltaVector (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (hg : IsGood N θ K g) (x : G) :
    eval _ _ (deltaVector K hK g hg).1 x = deltaFun N θ K g x := rfl

end DeltaVector

section Integral

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {N : Subgroup G} {θ : N →* ℂˣ}

/-- A `θ⁻¹`-equivariant function. -/
def IsInverseEquivariant (θ : N →* ℂˣ) (f : G → ℂ) : Prop :=
  ∀ n : N, ∀ x, f ((n : G) * x) = (((θ n)⁻¹ : ℂˣ) : ℂ) * f x

theorem deltaFun_mul_invariant {K : Subgroup G} {g : G} (hg : IsGood N θ K g) {f : G → ℂ}
    (hf : IsInverseEquivariant θ f) (n : N) (x : G) :
    deltaFun N θ K g ((n : G) * x) * f ((n : G) * x) = deltaFun N θ K g x * f x := by
  rw [deltaFun_left hg, hf]
  have : ((θ n : ℂˣ) : ℂ) * (((θ n)⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc (θ n : ℂ) * deltaFun N θ K g x * ((((θ n)⁻¹ : ℂˣ) : ℂ) * f x)
      = ((θ n : ℂ) * (((θ n)⁻¹ : ℂˣ) : ℂ)) * (deltaFun N θ K g x * f x) := by ring
    _ = deltaFun N θ K g x * f x := by rw [this, one_mul]

theorem descend_deltaFun_mul_eq_indicator {K : Subgroup G} {g : G} (hg : IsGood N θ K g)
    {f : G → ℂ} (hf : IsInverseEquivariant θ f) (hfK : ∀ x, ∀ k ∈ K, f (x * k) = f x) :
    descend N (fun x => deltaFun N θ K g x * f x) (deltaFun_mul_invariant hg hf) =
      (orbit N K g).indicator (fun _ => f g) := by
  funext q
  induction q using Quotient.inductionOn with
  | h x =>
    by_cases hx : ∃ n : N, ∃ k ∈ K, x = (n : G) * (g * k)
    · obtain ⟨n, k, hk, rfl⟩ := hx
      have hmem : (Quotient.mk _ ((n : G) * (g * k)) : QuotientIntegration.LeftQuotient N) ∈
          orbit N K g := by
        refine ⟨⟨k, hk⟩, ?_⟩
        apply Quotient.sound
        change QuotientGroup.rightRel _ (g * k) ((n : G) * (g * k))
        rw [QuotientGroup.rightRel_apply]
        simpa [mul_assoc] using n.property
      rw [Set.indicator_of_mem hmem, descend_mk, deltaFun_apply hg _ hk, hf, hfK g k hk]
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    · have hnot : (Quotient.mk _ x : QuotientIntegration.LeftQuotient N) ∉ orbit N K g := by
        rintro ⟨k, hk⟩
        have hn : x * (g * k.val)⁻¹ ∈ N :=
          QuotientGroup.rightRel_apply.mp (Quotient.exact hk)
        exact hx ⟨⟨x * (g * k.val)⁻¹, hn⟩, k.val, k.property, by simp only []; group⟩
      rw [Set.indicator_of_notMem hnot, descend_mk, deltaFun_eq_zero hx, zero_mul]

/-- The integral of a delta function against a right `K`-invariant `θ⁻¹`-equivariant
function. -/
theorem integral_deltaFun_mul [MeasurableSpace (QuotientIntegration.LeftQuotient N)]
    [OpensMeasurableSpace (QuotientIntegration.LeftQuotient N)]
    (ν : Measure (QuotientIntegration.LeftQuotient N)) {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) {g : G} (hg : IsGood N θ K g) {f : G → ℂ}
    (hf : IsInverseEquivariant θ f) (hfK : ∀ x, ∀ k ∈ K, f (x * k) = f x) :
    ∫ q, descend N (fun x => deltaFun N θ K g x * f x) (deltaFun_mul_invariant hg hf) q ∂ν =
      ν.real (orbit N K g) • f g := by
  rw [descend_deltaFun_mul_eq_indicator hg hf hfK]
  exact integral_indicator_const _ (isOpen_orbit N hKo g).measurableSet

end Integral

end Langlands.RankinSelberg.SupercuspidalCompleteness

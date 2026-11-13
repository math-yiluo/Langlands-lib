import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility
import Langlands.Representation.Jacquet.CompressionStabilizationStatement

/-! # Compression by an element dominating a power of an Iwahori contraction

Renard 2026, VI.9.1, Remark 3 (printed p.198 / PDF p.204), abstract part. Let `t₀` be an
`M`-central Iwahori contraction of `K` relative to `(N, M, N̄)` and `b ≥ 1`. An `M`-central
element `g ∈ M` *dominates* `t₀ ^ b` when conjugation by `g` carries
`t₀^{-b} (K ∩ N) t₀^b` into `K` and conjugation by `g⁻¹` carries `t₀^b (K ∩ N̄) t₀^{-b}`
into `K`. Then `g` is itself an Iwahori contraction, and, writing `A_x` for the compressed
action `v ↦ e_K(π(x) v)` on `V^K`,

  `A_g = A_Y ∘ A_{t₀}^b = A_{t₀}^b ∘ A_Y`, with `Y = t₀^{-b} g`.

Hence `ker A_{t₀}^b ⊆ ker A_g` and `Im A_g ⊆ Im A_{t₀}^b`. When the kernel and range of
`A_{t₀}^b` are the kernel supremum `V^K_0` and the stable image `V^K_*` of `t₀`, and the
compressions of `t₀` and `g` both split, this gives `ker A_g = V^K_0` and `Im A_g = V^K_*`.
-/

noncomputable section

namespace Langlands.Jacquet

universe uG uV

section Group

variable {G : Type uG} [Group G]

/-- If conjugation by `y` maps a subgroup `H` into itself, so does conjugation by every
power of `y`. -/
theorem conj_pow_mem_of_conj_mem {H : Subgroup G} {y : G}
    (hy : ∀ u ∈ H, y * u * y⁻¹ ∈ H) (r : ℕ) : ∀ u ∈ H, y ^ r * u * (y ^ r)⁻¹ ∈ H := by
  induction r with
  | zero => intro u hu; simpa using hu
  | succ r ih =>
    intro u hu
    have e : y ^ (r + 1) * u * (y ^ (r + 1))⁻¹ = y * (y ^ r * u * (y ^ r)⁻¹) * y⁻¹ := by
      group
    rw [e]
    exact hy _ (ih u hu)

/-- If conjugation by `y⁻¹` maps a subgroup `H` into itself, so does conjugation by the
inverse of every power of `y`. -/
theorem inv_conj_pow_mem_of_inv_conj_mem {H : Subgroup G} {y : G}
    (hy : ∀ l ∈ H, y⁻¹ * l * y ∈ H) (r : ℕ) : ∀ l ∈ H, (y ^ r)⁻¹ * l * y ^ r ∈ H := by
  induction r with
  | zero => intro l hl; simpa using hl
  | succ r ih =>
    intro l hl
    have e : (y ^ (r + 1))⁻¹ * l * y ^ (r + 1) = y⁻¹ * ((y ^ r)⁻¹ * l * y ^ r) * y := by
      group
    rw [e]
    exact hy _ (ih l hl)

end Group

variable {G : Type uG} [Group G] [TopologicalSpace G]

namespace IsIwahoriContraction

variable {K : OpenSubgroup G} {N M Nbar : Subgroup G} {t₀ g : G}

/-- Renard VI.9.1, Remark 3, abstract part: an `M`-central element of `M` dominating a
power `t₀ ^ b` (`b ≥ 1`) of an Iwahori contraction `t₀` is an Iwahori contraction. -/
theorem of_dominates (h : IsIwahoriContraction K N M Nbar t₀)
    (hMN : M ≤ Subgroup.normalizer N) (hMNbar : M ≤ Subgroup.normalizer Nbar)
    {b : ℕ} (hb : 1 ≤ b) (hg : g ∈ M) (hcent : ∀ m ∈ M, m * g = g * m)
    (hup : ∀ u ∈ K.toSubgroup ⊓ N, g * ((t₀ ^ b)⁻¹ * u * t₀ ^ b) * g⁻¹ ∈ K)
    (hlow : ∀ l ∈ K.toSubgroup ⊓ Nbar, g⁻¹ * (t₀ ^ b * l * (t₀ ^ b)⁻¹) * g ∈ K) :
    IsIwahoriContraction K N M Nbar g := by
  have hcomm : Commute (t₀ ^ b) g := Commute.pow_left (hcent t₀ h.mem_levi : Commute t₀ g) b
  -- `Y = t₀^{-b} g = g t₀^{-b}` lies in `M`.
  set Y : G := (t₀ ^ b)⁻¹ * g with hYdef
  have hY' : Y = g * (t₀ ^ b)⁻¹ := hcomm.inv_left.eq
  have hYM : Y ∈ M := M.mul_mem (M.inv_mem (M.pow_mem h.mem_levi b)) hg
  have hgY : g = Y * t₀ ^ b := by rw [hY']; group
  have hgY' : g = t₀ ^ b * Y := by rw [hYdef]; group
  have hYc : Commute Y (t₀ ^ b) := by
    show Y * t₀ ^ b = t₀ ^ b * Y
    rw [← hgY, ← hgY']
  -- Conjugation by `Y` preserves `K ∩ N`, conjugation by `Y⁻¹` preserves `K ∩ N̄`.
  have hYup : ∀ u ∈ K.toSubgroup ⊓ N, Y * u * Y⁻¹ ∈ K.toSubgroup ⊓ N := by
    intro u hu
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hMN hYM) u).mp hu.2⟩
    have e : Y * u * Y⁻¹ = g * ((t₀ ^ b)⁻¹ * u * t₀ ^ b) * g⁻¹ := by rw [hY']; group
    rw [e]
    exact hup u hu
  have hYlow : ∀ l ∈ K.toSubgroup ⊓ Nbar, Y⁻¹ * l * Y ∈ K.toSubgroup ⊓ Nbar := by
    intro l hl
    refine ⟨?_, ?_⟩
    · have e : Y⁻¹ * l * Y = g⁻¹ * (t₀ ^ b * l * (t₀ ^ b)⁻¹) * g := by rw [hYdef]; group
      rw [e]
      exact hlow l hl
    · have := (Subgroup.mem_normalizer_iff.mp (hMNbar (M.inv_mem hYM)) l).mp hl.2
      simpa using this
  refine
    { mem_levi := hg
      factor := h.factor
      upper := ?_
      levi := ?_
      lower := ?_
      exhaust := ?_
      contract := ?_ }
  · intro u hu
    have hu' := h.upper_pow b u hu
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hMN hg) u).mp hu.2⟩
    have e : g * u * g⁻¹ =
        g * ((t₀ ^ b)⁻¹ * (t₀ ^ b * u * (t₀ ^ b)⁻¹) * t₀ ^ b) * g⁻¹ := by group
    rw [e]
    exact hup _ hu'
  · intro m hm
    have e : g⁻¹ * m * g = m := by
      rw [mul_assoc, hcent m hm.2, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e]
    exact hm
  · intro l hl
    have hl' := inv_conj_pow_mem_of_inv_conj_mem h.lower b l hl
    refine ⟨?_, ?_⟩
    · have e : g⁻¹ * l * g =
          g⁻¹ * (t₀ ^ b * ((t₀ ^ b)⁻¹ * l * t₀ ^ b) * (t₀ ^ b)⁻¹) * g := by group
      rw [e]
      exact hlow _ hl'
    · have := (Subgroup.mem_normalizer_iff.mp (hMNbar (M.inv_mem hg)) l).mp hl.2
      simpa using this
  · intro x hx
    obtain ⟨r, hr⟩ := h.eventually_mem hMN ⟨x, hx⟩
    refine ⟨r, ?_⟩
    have hrb : r ≤ b * r := Nat.le_mul_of_pos_left r hb
    have hx' : t₀ ^ (b * r) * x * (t₀ ^ (b * r))⁻¹ ∈ K.toSubgroup ⊓ N :=
      ⟨hr (b * r) hrb,
        (Subgroup.mem_normalizer_iff.mp (hMN (M.pow_mem h.mem_levi (b * r))) x).mp hx⟩
    have e : g ^ r * x * (g ^ r)⁻¹ =
        Y ^ r * (t₀ ^ (b * r) * x * (t₀ ^ (b * r))⁻¹) * (Y ^ r)⁻¹ := by
      rw [hgY, hYc.mul_pow, ← pow_mul]
      group
    rw [e]
    exact (conj_pow_mem_of_conj_mem hYup r _ hx').1
  · intro L
    obtain ⟨s, hs⟩ := h.contract L
    refine ⟨s, fun l hl => ?_⟩
    have hl' := inv_conj_pow_mem_of_inv_conj_mem hYlow s l hl
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (Nat.le_mul_of_pos_left s hb)
    have hl'' := inv_conj_pow_mem_of_inv_conj_mem h.lower c _ hl'
    have e : (g ^ s)⁻¹ * l * g ^ s =
        (t₀ ^ s)⁻¹ * ((t₀ ^ c)⁻¹ * ((Y ^ s)⁻¹ * l * Y ^ s) * t₀ ^ c) * t₀ ^ s := by
      rw [hgY, hYc.mul_pow, ← pow_mul, hc]
      group
    rw [e]
    exact hs _ hl''

end IsIwahoriContraction

section Compression

variable [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable {K : OpenSubgroup G} (hK : IsCompact (K : Set G)) {N M Nbar : Subgroup G} {t₀ g : G}

/-- Renard VI.9.1, Remark 3, abstract part: for an `M`-central element `g ∈ M` dominating
`t₀ ^ b` (`b ≥ 1`), the compression of `g` factors through the `b`-th power of the
compression of `t₀` on both sides. -/
theorem compressedAction_eq_of_dominates (h : IsIwahoriContraction K N M Nbar t₀)
    (hcent₀ : ∀ m ∈ M, m * t₀ = t₀ * m) (hcent : ∀ m ∈ M, m * g = g * m)
    {b : ℕ} (hup : ∀ u ∈ K.toSubgroup ⊓ N, g * ((t₀ ^ b)⁻¹ * u * t₀ ^ b) * g⁻¹ ∈ K)
    (hlow : ∀ l ∈ K.toSubgroup ⊓ Nbar, g⁻¹ * (t₀ ^ b * l * (t₀ ^ b)⁻¹) * g ∈ K) :
    compressedAction ρ hρ K hK g =
        compressedAction ρ hρ K hK ((t₀ ^ b)⁻¹ * g) * compressedAction ρ hρ K hK t₀ ^ b ∧
      compressedAction ρ hρ K hK g =
        compressedAction ρ hρ K hK t₀ ^ b * compressedAction ρ hρ K hK ((t₀ ^ b)⁻¹ * g) := by
  have hcomm : Commute (t₀ ^ b) g := Commute.pow_left (hcent t₀ h.mem_levi : Commute t₀ g) b
  set Y : G := (t₀ ^ b)⁻¹ * g with hYdef
  have hY' : Y = g * (t₀ ^ b)⁻¹ := hcomm.inv_left.eq
  have hgY : g = Y * t₀ ^ b := by rw [hY']; group
  have hgY' : g = t₀ ^ b * Y := by rw [hYdef]; group
  constructor
  · conv_lhs => rw [hgY]
    rw [compressedAction_mul_of_factor ρ hρ K hK N M Nbar h.factor Y (t₀ ^ b)
      (fun u hu => by
        have e : Y * u * Y⁻¹ = g * ((t₀ ^ b)⁻¹ * u * t₀ ^ b) * g⁻¹ := by rw [hY']; group
        rw [e]
        exact hup u hu)
      (fun l hl => (inv_conj_pow_mem_of_inv_conj_mem h.lower b l hl).1)
      (fun m hm => (h.levi_pow b m hm).1), h.compressedAction_pow ρ hρ hK b]
  · conv_lhs => rw [hgY']
    rw [compressedAction_mul_of_factor ρ hρ K hK N M Nbar h.factor (t₀ ^ b) Y
      (fun u hu => (h.upper_pow b u hu).1)
      (fun l hl => by
        have e : Y⁻¹ * l * Y = g⁻¹ * (t₀ ^ b * l * (t₀ ^ b)⁻¹) * g := by rw [hYdef]; group
        rw [e]
        exact hlow l hl)
      (fun m hm => by
        have hmY : Commute m Y :=
          ((Commute.pow_right (hcent₀ m hm.2 : Commute m t₀) b).inv_right).mul_right
            (hcent m hm.2 : Commute m g)
        have e : Y⁻¹ * m * Y = m := by
          rw [mul_assoc, hmY.eq, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [e]
        exact hm.1), h.compressedAction_pow ρ hρ hK b]

/-- Renard VI.9.1, Remark 3, abstract part. Let `t₀` be an `M`-central Iwahori contraction
and `g ∈ M` an `M`-central element dominating `t₀ ^ b` with `b ≥ 1`. If the kernel and the
range of the `b`-th power of the compression of `t₀` are its kernel supremum and its
stable image, and the compressions of `t₀` and `g` split, then the kernel and the range
of the compression of `g` itself are the kernel supremum and the stable image of `t₀`. -/
theorem ker_range_compressedAction_of_dominates (h : IsIwahoriContraction K N M Nbar t₀)
    (hcent₀ : ∀ m ∈ M, m * t₀ = t₀ * m)
    (hMN : M ≤ Subgroup.normalizer N) (hMNbar : M ≤ Subgroup.normalizer Nbar)
    {b : ℕ} (hb : 1 ≤ b) (hg : g ∈ M) (hcent : ∀ m ∈ M, m * g = g * m)
    (hup : ∀ u ∈ K.toSubgroup ⊓ N, g * ((t₀ ^ b)⁻¹ * u * t₀ ^ b) * g⁻¹ ∈ K)
    (hlow : ∀ l ∈ K.toSubgroup ⊓ Nbar, g⁻¹ * (t₀ ^ b * l * (t₀ ^ b)⁻¹) * g ∈ K)
    (hker : powerKernelSup ρ hρ K hK t₀ =
      LinearMap.ker (compressedAction ρ hρ K hK t₀ ^ b))
    (hrange : stableImage ρ hρ K hK t₀ =
      LinearMap.range (compressedAction ρ hρ K hK t₀ ^ b))
    (hsplit₀ : CompactCompressionSplits ρ hρ K hK t₀)
    (hsplit : CompactCompressionSplits ρ hρ K hK g) :
    powerKernelSup ρ hρ K hK t₀ = LinearMap.ker (compressedAction ρ hρ K hK g) ∧
      stableImage ρ hρ K hK t₀ = LinearMap.range (compressedAction ρ hρ K hK g) := by
  have hgc := h.of_dominates hMN hMNbar hb hg hcent hup hlow
  obtain ⟨e1, e2⟩ := compressedAction_eq_of_dominates ρ hρ hK h hcent₀ hcent hup hlow
  -- Remark 1 for the kernel: both kernel suprema are the kernel of the Jacquet map.
  have hpk : powerKernelSup ρ hρ K hK g = powerKernelSup ρ hρ K hK t₀ := by
    rw [powerKernelSup_eq_ker_of_iwahoriContraction ρ hρ hK hgc hMN,
      powerKernelSup_eq_ker_of_iwahoriContraction ρ hρ hK h hMN]
  have hker_le : LinearMap.ker (compressedAction ρ hρ K hK g) ≤ powerKernelSup ρ hρ K hK g := by
    have := le_iSup (fun r : ℕ => LinearMap.ker (compressedAction ρ hρ K hK g ^ r)) 1
    simpa [powerKernelSup] using this
  have hrange_le : stableImage ρ hρ K hK g ≤ LinearMap.range (compressedAction ρ hρ K hK g) := by
    have := iInf_le (fun r : ℕ => LinearMap.range (compressedAction ρ hρ K hK g ^ r)) 1
    simpa [stableImage] using this
  have hrange_le' : LinearMap.range (compressedAction ρ hρ K hK g) ≤ stableImage ρ hρ K hK t₀ := by
    rw [hrange, e2]
    exact LinearMap.range_comp_le_range _ _
  refine ⟨le_antisymm ?_ (hpk ▸ hker_le), ?_⟩
  · rw [hker, e1]
    exact LinearMap.ker_le_ker_comp _ _
  · -- `V^K_*(g) ⊆ V^K_*(t₀)` are complements of the same `V^K_0`, hence equal.
    have hsplit' : IsCompl (powerKernelSup ρ hρ K hK t₀) (stableImage ρ hρ K hK g) :=
      hpk ▸ hsplit
    have hle : stableImage ρ hρ K hK g ≤ stableImage ρ hρ K hK t₀ := hrange_le.trans hrange_le'
    have heq : stableImage ρ hρ K hK g = stableImage ρ hρ K hK t₀ :=
      eq_of_le_of_inf_le_of_sup_le hle
        (by rw [inf_comm, hsplit₀.inf_eq_bot]; exact bot_le)
        (by rw [sup_comm (stableImage ρ hρ K hK g), hsplit'.sup_eq_top]; exact le_top)
    exact le_antisymm (heq ▸ hrange_le) hrange_le'

end Compression

end Langlands.Jacquet

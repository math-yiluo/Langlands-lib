import Langlands.BushnellKutzko.TypeJacquetCompression
import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility
import Langlands.Representation.Jacquet.StablePairingProof

/-! # Nonvanishing Jacquet modules from injective compression -/

noncomputable section

namespace Langlands.Jacquet

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- An Iwahori factorization `K = (K ∩ Nbar)(K ∩ M)(K ∩ N)` of an open subgroup `K` together with
an element `g ∈ M` such that conjugation by `g` maps `K ∩ N` into itself, conjugation by `g⁻¹`
maps `K ∩ M` and `K ∩ Nbar` into themselves, and every element of `N` is carried into `K` by
conjugation with some power of `g`. These are the conditions of `IsIwahoriContraction` without
its uniform contraction of `K ∩ Nbar`. -/
structure IsCompressionContraction (K : OpenSubgroup G) (N M Nbar : Subgroup G) (g : G) :
    Prop where
  mem_levi : g ∈ M
  factor : ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar, ∃ m ∈ K.toSubgroup ⊓ M,
    ∃ u ∈ K.toSubgroup ⊓ N, k = l * m * u
  upper : ∀ u ∈ K.toSubgroup ⊓ N, g * u * g⁻¹ ∈ K.toSubgroup ⊓ N
  levi : ∀ m ∈ K.toSubgroup ⊓ M, g⁻¹ * m * g ∈ K.toSubgroup ⊓ M
  lower : ∀ l ∈ K.toSubgroup ⊓ Nbar, g⁻¹ * l * g ∈ K.toSubgroup ⊓ Nbar
  exhaust : ∀ x ∈ N, ∃ r : ℕ, g ^ r * x * (g ^ r)⁻¹ ∈ K

namespace IsCompressionContraction

variable {K : OpenSubgroup G} {N M Nbar : Subgroup G} {g : G}

theorem upper_pow (h : IsCompressionContraction K N M Nbar g) (s : ℕ) :
    ∀ u ∈ K.toSubgroup ⊓ N, g ^ s * u * (g ^ s)⁻¹ ∈ K.toSubgroup ⊓ N := by
  induction s with
  | zero => intro u hu; simpa using hu
  | succ s ih =>
    intro u hu
    have e : g ^ (s + 1) * u * (g ^ (s + 1))⁻¹ = g * (g ^ s * u * (g ^ s)⁻¹) * g⁻¹ := by
      group
    rw [e]
    exact h.upper _ (ih u hu)

theorem eventually_mem (h : IsCompressionContraction K N M Nbar g)
    (hMN : M ≤ Subgroup.normalizer N) (x : N) :
    ∃ r : ℕ, ∀ s : ℕ, r ≤ s → g ^ s * x.val * (g ^ s)⁻¹ ∈ K := by
  obtain ⟨r, hr⟩ := h.exhaust x.val x.property
  refine ⟨r, fun s hs => ?_⟩
  have hgN : g ^ r ∈ Subgroup.normalizer N := pow_mem (hMN h.mem_levi) r
  have hN : g ^ r * x.val * (g ^ r)⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp hgN x.val).mp x.property
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
  have e : g ^ (r + t) * x.val * (g ^ (r + t))⁻¹ =
      g ^ t * (g ^ r * x.val * (g ^ r)⁻¹) * (g ^ t)⁻¹ := by
    group
  rw [e]
  exact (h.upper_pow t _ ⟨hr, hN⟩).1

theorem ofIwahoriContraction (h : IsIwahoriContraction K N M Nbar g) :
    IsCompressionContraction K N M Nbar g :=
  ⟨h.mem_levi, h.factor, h.upper, h.levi, h.lower, h.exhaust⟩

end IsCompressionContraction

variable [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- On `K`-fixed vectors, the `r`-th power of compression by a compression contraction `g`
agrees with compression by `g ^ r`. -/
theorem IsCompressionContraction.compressionMap_pow (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    {K : OpenSubgroup G} (hK : IsCompact (K : Set G)) {N M Nbar : Subgroup G} {g : G}
    (h : IsCompressionContraction K N M Nbar g) (r : ℕ) (v : V)
    (hv : v ∈ fixedVectors ρ K.toSubgroup) :
    (compressionMap ρ hρ K hK g ^ r) v = compressionMap ρ hρ K hK (g ^ r) v := by
  induction r generalizing v with
  | zero =>
    simp only [pow_zero, Module.End.one_apply, compressionMap_apply, map_one]
    exact (Compact.averageMap_id ρ hρ K hK v hv).symm
  | succ r ih =>
    rw [pow_succ, Module.End.mul_apply,
      ih (compressionMap ρ hρ K hK g v) (Compact.averageMap_mem_fixedVectors ρ hρ K hK _),
      compressionMap_mul_of_factor ρ hρ K hK (g ^ r) g ?_ v hv, ← pow_succ]
    intro k hk
    obtain ⟨l, hl, m, hm, u, hu, hkinv⟩ := h.factor k⁻¹ (K.inv_mem hk)
    refine ⟨u⁻¹, m⁻¹ * l⁻¹, ?_, ?_, ?_⟩
    · rw [← inv_inv k, hkinv]; group
    · exact (h.upper_pow r _ ((K.toSubgroup ⊓ N).inv_mem hu)).1
    · have e : g⁻¹ * (m⁻¹ * l⁻¹) * g = (g⁻¹ * m⁻¹ * g) * (g⁻¹ * l⁻¹ * g) := by group
      rw [e]
      exact K.mul_mem (h.levi _ ((K.toSubgroup ⊓ M).inv_mem hm)).1
        (h.lower _ ((K.toSubgroup ⊓ Nbar).inv_mem hl)).1

/-- Let `g` satisfy `IsCompressionContraction K N M Nbar g` and let `M` normalize `N`. If the
Jacquet module along `N` vanishes, every `K`-fixed vector is killed by a power of the
compression by `g`. -/
theorem exists_pow_compressionMap_eq_zero_of_compressionContraction (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    {K : OpenSubgroup G} (hK : IsCompact (K : Set G)) {N M Nbar : Subgroup G} {g : G}
    (h : IsCompressionContraction K N M Nbar g) (hMN : M ≤ Subgroup.normalizer N)
    (hN : Subsingleton (Coinvariants ρ N)) (v : V)
    (hv : v ∈ fixedVectors ρ K.toSubgroup) :
    ∃ r : ℕ, (compressionMap ρ hρ K hK g ^ r) v = 0 := by
  have hrel : v ∈ relations ρ N := (mk_eq_zero ρ N v).mp (Subsingleton.elim _ _)
  have hev : ∀ x ∈ relations ρ N, ∃ r : ℕ, ∀ s : ℕ, r ≤ s →
      Compact.averageMap ρ hρ K hK (ρ (g ^ s) x) = 0 := by
    intro x hx
    rw [relations_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨⟨n, w⟩, rfl⟩ := hw
      obtain ⟨r, hr⟩ := h.eventually_mem hMN n
      refine ⟨r, fun s hs => ?_⟩
      rw [map_sub, map_sub, sub_eq_zero]
      calc
        _ = Compact.averageMap ρ hρ K hK
            (ρ (g ^ s * n.val * (g ^ s)⁻¹) (ρ (g ^ s) w)) := by
          congr 1
          simp only [← Module.End.mul_apply, ← map_mul ρ]
          congr 1
          group
        _ = _ := averageMap_apply_of_mem ρ hρ K hK (hr s hs) _
    | zero => exact ⟨0, fun s _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨rx, hx⟩ := hx
      obtain ⟨ry, hy⟩ := hy
      refine ⟨max rx ry, fun s hs => ?_⟩
      rw [map_add, map_add, hx s (le_trans (le_max_left _ _) hs),
        hy s (le_trans (le_max_right _ _) hs), add_zero]
    | smul c x _ hx =>
      obtain ⟨r, hr⟩ := hx
      refine ⟨r, fun s hs => ?_⟩
      rw [map_smul, map_smul, hr s hs, smul_zero]
  obtain ⟨r, hr⟩ := hev v hrel
  refine ⟨r, ?_⟩
  rw [h.compressionMap_pow ρ hρ hK r v hv, compressionMap_apply]
  exact hr r le_rfl

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- **Jacquet nonvanishing from injective compression.** Let `K` be a compact open subgroup,
let `g` satisfy `IsCompressionContraction K N M Nbar g`, and let `M` normalize `N`. Let `P` be a
property of linear maps from a finite-dimensional space `W` with values in the
`K`-fixed vectors, stable under composition with the compression by `g`, and such
that this composition is zero only for the zero map. If some nonzero map has `P`, then
the Jacquet module along `N` is nonzero. -/
theorem not_subsingleton_coinvariants_of_compressionContraction (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) {K : OpenSubgroup G} (hK : IsCompact (K : Set G))
    {N M Nbar : Subgroup G} {g : G} (h : IsCompressionContraction K N M Nbar g)
    (hMN : M ≤ Subgroup.normalizer N) [FiniteDimensional ℂ W]
    (P : (W →ₗ[ℂ] V) → Prop)
    (hrange : ∀ f, P f → ∀ w, f w ∈ fixedVectors ρ K.toSubgroup)
    (hstep : ∀ f, P f → P ((compressionMap ρ hρ K hK g).comp f))
    (hinj : ∀ f, P f → (compressionMap ρ hρ K hK g).comp f = 0 → f = 0)
    (f : W →ₗ[ℂ] V) (hf : P f) (hf0 : f ≠ 0) :
    ¬ Subsingleton (Coinvariants ρ N) := by
  intro hN
  classical
  let A := compressionMap ρ hρ K hK g
  let b := Module.finBasis ℂ W
  have hzero : ∀ i, ∃ r : ℕ, (A ^ r) (f (b i)) = 0 := fun i =>
    exists_pow_compressionMap_eq_zero_of_compressionContraction ρ hρ hK h hMN hN _ (hrange f hf (b i))
  choose r hr using hzero
  let R := Finset.univ.sup r
  have hP : ∀ t : ℕ, P ((A ^ t).comp f) := by
    intro t
    induction t with
    | zero =>
      rw [pow_zero, Module.End.one_eq_id, LinearMap.id_comp]
      exact hf
    | succ t ih =>
      have := hstep _ ih
      rwa [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_assoc]
  have hR : (A ^ R).comp f = 0 := by
    apply b.ext
    intro i
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := r) (Finset.mem_univ i))
    change (A ^ R) (f (b i)) = 0
    rw [show R = c + r i by omega, pow_add, Module.End.mul_apply, hr i, map_zero]
  have hdown : ∀ t : ℕ, (A ^ t).comp f = 0 → f = 0 := by
    intro t
    induction t with
    | zero =>
      rw [pow_zero, Module.End.one_eq_id, LinearMap.id_comp]
      exact id
    | succ t ih =>
      intro ht
      apply ih
      apply hinj _ (hP t)
      rwa [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_assoc] at ht
  exact hf0 (hdown R hR)

end Langlands.Jacquet

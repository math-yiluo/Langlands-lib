import Langlands.Representation.Jacquet.CompactCompressionStableDualityProof
import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility

/-!
# Stable-image duality and Jacquet's lemma from the Fitting splitting

The published finite-dimensional arguments for the stable-image evaluation duality
and for Jacquet's lemma use finite dimensionality only through the splitting of
the `K`-fixed vectors into the kernel supremum and the stable image of the
compressed action. This file proves both conclusions from that splitting alone,
for arbitrary smooth complex representations, and derives the splitting from
eventual stability of the power ranges and kernels.
-/

noncomputable section

namespace Langlands.Jacquet

universe uR uM uA uB uG uV

section Fitting

variable {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module R M]

/-- Power ranges and kernels that are constant from `r` on split the module into
the kernel supremum and the stable image. -/
theorem isCompl_iSup_ker_pow_iInf_range_pow_of_eventually (f : Module.End R M) (r : ℕ)
    (hr : ∀ s : ℕ, r ≤ s →
      (⨅ n : ℕ, LinearMap.range (f ^ n)) = LinearMap.range (f ^ s) ∧
        (⨆ n : ℕ, LinearMap.ker (f ^ n)) = LinearMap.ker (f ^ s)) :
    IsCompl (⨆ n : ℕ, LinearMap.ker (f ^ n)) (⨅ n : ℕ, LinearMap.range (f ^ n)) := by
  obtain ⟨hR1, hK1⟩ := hr r le_rfl
  obtain ⟨hR2, hK2⟩ := hr (r + r) (Nat.le_add_right r r)
  rw [hR1, hK1]
  constructor
  · rw [Submodule.disjoint_def]
    rintro x hx ⟨y, rfl⟩
    have hy : y ∈ LinearMap.ker (f ^ (r + r)) := by
      rw [LinearMap.mem_ker, pow_add, Module.End.mul_apply]
      exact hx
    rw [← hK2, hK1] at hy
    exact hy
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : (f ^ r) x ∈ LinearMap.range (f ^ (r + r)) := by
      rw [← hR2, hR1]
      exact LinearMap.mem_range_self _ x
    obtain ⟨y, hy⟩ := hx
    rw [Submodule.mem_sup]
    refine ⟨x - (f ^ r) y, ?_, (f ^ r) y, LinearMap.mem_range_self _ y, sub_add_cancel _ _⟩
    rw [LinearMap.mem_ker, map_sub, ← hy, pow_add, Module.End.mul_apply, sub_self]

end Fitting

section Splitting

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Eventual stability of the compressed action gives the Fitting splitting of
the `K`-fixed vectors. -/
theorem compactCompressionSplits_of_eventuallyStable (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (h : CompactCompressionEventuallyStable ρ hρ K hK g) :
    CompactCompressionSplits ρ hρ K hK g := by
  obtain ⟨r, hr⟩ := h
  exact isCompl_iSup_ker_pow_iInf_range_pow_of_eventually _ r hr

/-- The kernel supremum is carried into itself by the compressed action. -/
theorem powerKernelSup_le_comap_compressedAction (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) :
    powerKernelSup ρ hρ K hK g ≤
      (powerKernelSup ρ hρ K hK g).comap (compressedAction ρ hρ K hK g) := by
  refine iSup_le fun n x hx => ?_
  rw [Submodule.mem_comap]
  refine Submodule.mem_iSup_of_mem n ?_
  rw [LinearMap.mem_ker] at hx ⊢
  rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply, hx, map_zero]

/-- With the Fitting splitting, the restriction of the compressed action to its
stable image is bijective. -/
theorem stableImageAction_bijective_of_splits (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (hsplit : CompactCompressionSplits ρ hρ K hK g) :
    CompactCompressionStableActionBijective ρ hρ K hK g := by
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have hv0 : compressedAction ρ hρ K hK g (v : fixedVectors ρ K.toSubgroup) = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.mp hv)
    have hker : (v : fixedVectors ρ K.toSubgroup) ∈ powerKernelSup ρ hρ K hK g := by
      refine Submodule.mem_iSup_of_mem 1 ?_
      rw [LinearMap.mem_ker, pow_one]
      exact hv0
    have h0 := hsplit.disjoint.le_bot ⟨hker, v.property⟩
    exact Subtype.ext (by simpa using h0)
  · intro s
    have hs1 : (s : fixedVectors ρ K.toSubgroup) ∈
        LinearMap.range (compressedAction ρ hρ K hK g ^ 1) :=
      (iInf_le (fun r : ℕ => LinearMap.range (compressedAction ρ hρ K hK g ^ r)) 1) s.property
    obtain ⟨x, hx⟩ := hs1
    have hx' : x ∈ powerKernelSup ρ hρ K hK g ⊔ stableImage ρ hρ K hK g := by
      rw [hsplit.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨t, ht, u, hu, rfl⟩ := Submodule.mem_sup.mp hx'
    rw [pow_one, map_add] at hx
    have hCtT : compressedAction ρ hρ K hK g t ∈ powerKernelSup ρ hρ K hK g :=
      powerKernelSup_le_comap_compressedAction ρ hρ K hK g ht
    have hCtS : compressedAction ρ hρ K hK g t ∈ stableImage ρ hρ K hK g := by
      have heq : compressedAction ρ hρ K hK g t =
          (s : fixedVectors ρ K.toSubgroup) - compressedAction ρ hρ K hK g u := by
        rw [← hx, add_sub_cancel_right]
      rw [heq]
      exact Submodule.sub_mem _ s.property (compressedAction_mem_stableImage ρ hρ K hK g u hu)
    have hCt : compressedAction ρ hρ K hK g t = 0 := by
      simpa using hsplit.disjoint.le_bot ⟨hCtT, hCtS⟩
    refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
    change compressedAction ρ hρ K hK g u = (s : fixedVectors ρ K.toSubgroup)
    rw [← hx, hCt, zero_add]

end Splitting

section DualityAlgebra

variable {A : Type uA} {B : Type uB}
variable [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

private theorem adjoint_pow_of_adjoint (p : A →ₗ[ℂ] Module.Dual ℂ B)
    (C : Module.End ℂ A) (D : Module.End ℂ B)
    (h : ∀ a b, p (C a) b = p a (D b)) (n : ℕ) (a : A) (b : B) :
    p ((C ^ n) a) b = p a ((D ^ n) b) := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, h, ih, ← Module.End.mul_apply, ← pow_succ]

/-- For a perfect pairing `p` with `C` adjoint to `D`, a vector lies in the stable
image of `C` exactly when it annihilates the kernel supremum of `D`. -/
private theorem mem_iInf_range_pow_iff_of_adjoint (p : A →ₗ[ℂ] Module.Dual ℂ B)
    (hp : Function.Bijective p) (C : Module.End ℂ A) (D : Module.End ℂ B)
    (h : ∀ a b, p (C a) b = p a (D b)) (a : A) :
    a ∈ (⨅ n : ℕ, LinearMap.range (C ^ n)) ↔
      ∀ b ∈ (⨆ n : ℕ, LinearMap.ker (D ^ n)), p a b = 0 := by
  constructor
  · intro ha b hb
    have hle : (⨆ n : ℕ, LinearMap.ker (D ^ n)) ≤ LinearMap.ker (p a) := by
      refine iSup_le fun n x hx => ?_
      obtain ⟨a', ha'⟩ := (Submodule.mem_iInf _).mp ha n
      rw [LinearMap.mem_ker, ← ha', adjoint_pow_of_adjoint p C D h, LinearMap.mem_ker.mp hx,
        map_zero]
    exact hle hb
  · intro ha
    rw [Submodule.mem_iInf]
    intro n
    have hann : p a ∈ (LinearMap.ker (D ^ n)).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro x hx
      exact ha x (Submodule.mem_iSup_of_mem n hx)
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hann
    obtain ⟨ψ, hψ⟩ := hann
    obtain ⟨a', ha'⟩ := hp.2 ψ
    refine ⟨a', hp.1 ?_⟩
    ext b
    rw [adjoint_pow_of_adjoint p C D h, ha', ← hψ, LinearMap.dualMap_apply]

/-- A perfect pairing with adjoint operators restricts to a perfect pairing of
stable images, provided the second operator has the Fitting splitting. -/
private theorem stable_pairing_bijective_of_isCompl (p : A →ₗ[ℂ] Module.Dual ℂ B)
    (hp : Function.Bijective p) (C : Module.End ℂ A) (D : Module.End ℂ B)
    (h : ∀ a b, p (C a) b = p a (D b))
    (hD : IsCompl (⨆ n : ℕ, LinearMap.ker (D ^ n)) (⨅ n : ℕ, LinearMap.range (D ^ n))) :
    Function.Bijective
      (p.compl₁₂ (⨅ n : ℕ, LinearMap.range (C ^ n)).subtype
        (⨅ n : ℕ, LinearMap.range (D ^ n)).subtype) := by
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro a ha
    have hT := (mem_iInf_range_pow_iff_of_adjoint p hp C D h a.val).mp a.property
    have hzero : p a.val = 0 := by
      ext b
      have hb : b ∈ (⨆ n : ℕ, LinearMap.ker (D ^ n)) ⊔ (⨅ n : ℕ, LinearMap.range (D ^ n)) := by
        rw [hD.sup_eq_top]
        exact Submodule.mem_top
      obtain ⟨t, ht, s, hs, rfl⟩ := Submodule.mem_sup.mp hb
      rw [map_add, hT t ht, zero_add, LinearMap.zero_apply]
      exact LinearMap.congr_fun (LinearMap.mem_ker.mp ha) ⟨s, hs⟩
    exact Subtype.ext (hp.1 (hzero.trans (map_zero p).symm))
  · intro φ
    obtain ⟨a, ha⟩ := hp.2 (φ.comp (Submodule.projectionOnto _ _ hD.symm))
    have hmem : a ∈ ⨅ n : ℕ, LinearMap.range (C ^ n) := by
      rw [mem_iInf_range_pow_iff_of_adjoint p hp C D h]
      intro b hb
      rw [ha, LinearMap.comp_apply, Submodule.projectionOnto_apply_of_mem_right hD.symm hb,
        map_zero]
    refine ⟨⟨a, hmem⟩, ?_⟩
    ext s
    change p a s.val = φ s
    rw [ha, LinearMap.comp_apply, Submodule.projectionOnto_apply_left]

end DualityAlgebra

section Duality

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The stable-image evaluation duality for `g` holds whenever compression by `g`
on the `K`-fixed vectors of `ρ` has the Fitting splitting; no finite
dimensionality is assumed. -/
theorem compactCompression_stableEvaluationDuality_of_splits
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (hsplit : CompactCompressionSplits ρ hρ K hK g) :
    CompactCompressionStableEvaluationDuality ρ hρ K hK g := by
  let p := smoothDualFixedRestriction ρ K.toSubgroup
  let q := p.compl₁₂
    (stableImage (smoothContragredient ρ) (isSmooth_smoothContragredient ρ) K hK g⁻¹).subtype
    (stableImage ρ hρ K hK g).subtype
  have hp : Function.Bijective p := smoothDualFixedRestriction_bijective ρ hρ K hK
  have hq0 := stable_pairing_bijective_of_isCompl
      (A := fixedVectors (smoothContragredient ρ) K.toSubgroup)
      (B := fixedVectors ρ K.toSubgroup) p hp
      (compressedAction (smoothContragredient ρ) (isSmooth_smoothContragredient ρ) K hK g⁻¹)
      (compressedAction ρ hρ K hK g) (compressedAction_adjoint ρ hρ K hK g) hsplit
  have hq : Function.Bijective q := hq0
  exact ⟨LinearEquiv.ofBijective q hq, fun _ _ => rfl⟩

end Duality

section Jacquet

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable {K : OpenSubgroup G} (hK : IsCompact (K : Set G)) {N M Nbar : Subgroup G} {g : G}

/-- Jacquet's lemma from the Fitting splitting: the actual quotient map restricted
to the stable image of compression by `g` is bijective onto the `K ∩ M`-fixed
coinvariants. -/
theorem stableImageJacquetMap_bijective_of_splits
    (h : IsIwahoriContraction K N M Nbar g) (hMN : M ≤ Subgroup.normalizer N)
    (hcompl : CompactCompressionSplits ρ hρ K hK g) :
    Function.Bijective (stableImageJacquetMap ρ hρ K hK g N M hMN) := by
  have hker := powerKernelSup_eq_ker_of_iwahoriContraction ρ hρ hK h hMN
  let gM : M := ⟨g, h.mem_levi⟩
  -- Every fixed vector has the quotient of a stable-image vector.
  have hsplit : ∀ x : fixedVectors ρ K.toSubgroup,
      ∃ t : stableImage ρ hρ K hK g,
        mk ρ N ((t : fixedVectors ρ K.toSubgroup) : V) = mk ρ N (x : V) := by
    intro x
    have hx : x ∈ powerKernelSup ρ hρ K hK g ⊔ stableImage ρ hρ K hK g := by
      rw [hcompl.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨k, hk, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
    refine ⟨⟨t, ht⟩, ?_⟩
    rw [hker, LinearMap.mem_ker] at hk
    have hk0 : mk ρ N (k : V) = 0 := congrArg Subtype.val hk
    rw [Submodule.coe_add, map_add, hk0, zero_add]
  -- The action of `g` can be cancelled on the image of the stable image.
  have hstep : ∀ z : Coinvariants ρ N,
      (∃ t : stableImage ρ hρ K hK g,
        mk ρ N ((t : fixedVectors ρ K.toSubgroup) : V) = action ρ N M hMN gM z) →
      ∃ t : stableImage ρ hρ K hK g, mk ρ N ((t : fixedVectors ρ K.toSubgroup) : V) = z := by
    rintro z ⟨t, htz⟩
    obtain ⟨t', rfl⟩ := (stableImageAction_bijective_of_splits ρ hρ K hK g hcompl).2 t
    refine ⟨t', ?_⟩
    apply (Representation.apply_bijective (action ρ N M hMN) gM).injective
    rw [← htz]
    exact (mk_compressedAction_of_iwahoriContraction ρ hρ hK h hMN
      (t' : fixedVectors ρ K.toSubgroup)).symm
  have hpow : ∀ (s : ℕ) (z : Coinvariants ρ N),
      (∃ t : stableImage ρ hρ K hK g,
        mk ρ N ((t : fixedVectors ρ K.toSubgroup) : V) = action ρ N M hMN (gM ^ s) z) →
      ∃ t : stableImage ρ hρ K hK g, mk ρ N ((t : fixedVectors ρ K.toSubgroup) : V) = z := by
    intro s
    induction s with
    | zero =>
      intro z hz
      simpa using hz
    | succ s ih =>
      intro z hz
      apply ih
      apply hstep
      simpa only [pow_succ', map_mul, Module.End.mul_apply] using hz
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro t ht
    have h1 : (t : fixedVectors ρ K.toSubgroup) ∈
        LinearMap.ker (fixedJacquetMap ρ N M hMN K.toSubgroup) := ht
    rw [← hker] at h1
    have h0 := hcompl.disjoint.le_bot ⟨h1, t.property⟩
    exact Subtype.ext (by simpa using h0)
  · intro y
    suffices hy : ∃ t : stableImage ρ hρ K hK g,
        mk ρ N ((t : fixedVectors ρ K.toSubgroup) : V) = (y : Coinvariants ρ N) by
      obtain ⟨t, ht⟩ := hy
      exact ⟨t, Subtype.ext ht⟩
    obtain ⟨v, hv⟩ := mk_surjective ρ N (y : Coinvariants ρ N)
    obtain ⟨s, hs⟩ := h.exists_pow_lower_fixed ρ hρ v
    have hgs : ((gM ^ s : M) : G) = g ^ s := by simp [gM]
    -- The Levi factor of `K` acts through the fixed vector `y`.
    have hlevi : ∀ m ∈ K.toSubgroup ⊓ M,
        mk ρ N (ρ m (ρ (g ^ s) v)) = action ρ N M hMN (gM ^ s) (y : Coinvariants ρ N) := by
      intro m hm
      have hm' := h.levi_pow s m hm
      have hyfix := y.property ⟨⟨_, hm'.2⟩, hm'.1⟩
      calc
        mk ρ N (ρ m (ρ (g ^ s) v)) =
            mk ρ N (ρ (gM ^ s : M) (ρ ((g ^ s)⁻¹ * m * g ^ s) v)) := by
          rw [hgs]
          simp only [← Module.End.mul_apply, ← map_mul ρ]
          congr 2
          group
        _ = action ρ N M hMN (gM ^ s)
              (action ρ N M hMN ⟨_, hm'.2⟩ (mk ρ N v)) := by
          rw [action_mk, action_mk]
        _ = _ := by
          rw [hv]
          exact congrArg _ hyfix
    -- Every `K`-translate of `ρ(g^s) v` has quotient `g^s y`.
    have hconst : ∀ k : K,
        mk ρ N (ρ k.val (ρ (g ^ s) v)) = action ρ N M hMN (gM ^ s) (y : Coinvariants ρ N) := by
      intro k
      obtain ⟨l, hl, m, hm, u, hu, hprod⟩ := h.factor k.val⁻¹ (K.inv_mem k.property)
      have heq : k.val = u⁻¹ * (m⁻¹ * l⁻¹) := by
        rw [← inv_inv k.val, hprod]
        group
      rw [heq, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        hs _ ((K.toSubgroup ⊓ Nbar).inv_mem hl)]
      rw [mk_apply_subgroup ρ N ⟨u⁻¹, N.inv_mem hu.2⟩]
      exact hlevi _ ((K.toSubgroup ⊓ M).inv_mem hm)
    apply hpow s
    obtain ⟨t, ht⟩ := hsplit ⟨Compact.averageMap ρ hρ K hK (ρ (g ^ s) v),
      Compact.averageMap_mem_fixedVectors ρ hρ K hK _⟩
    exact ⟨t, ht.trans (map_averageMap_of_forall_eq ρ hρ K hK (mk ρ N) _ _ hconst)⟩

include hρ hK in
/-- Jacquet's lemma from the Fitting splitting: the actual quotient map sends
`K`-fixed vectors onto the `K ∩ M`-fixed coinvariants. -/
theorem fixedJacquetMap_surjective_of_splits
    (h : IsIwahoriContraction K N M Nbar g) (hMN : M ≤ Subgroup.normalizer N)
    (hcompl : CompactCompressionSplits ρ hρ K hK g) :
    Function.Surjective (fixedJacquetMap ρ N M hMN K.toSubgroup) := by
  intro y
  obtain ⟨t, ht⟩ := (stableImageJacquetMap_bijective_of_splits ρ hρ hK h hMN hcompl).2 y
  exact ⟨t, ht⟩

end Jacquet

end Langlands.Jacquet

import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility

/-!
# Jacquet lifts from stationary compression ranges

For an arbitrary smooth complex representation, eventual stationarity of the
actual compact-compression ranges implies surjectivity of the fixed-vector
Jacquet quotient. No finite-dimensionality assumption is used.
-/

noncomputable section

namespace Langlands.Jacquet

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable {K : OpenSubgroup G} (hK : IsCompact (K : Set G))
variable {N M Nbar : Subgroup G} {g : G}

/-- The compression-power identity on the actual coinvariant quotient. -/
theorem mk_compressedAction_pow_of_iwahoriContraction
    (h : IsIwahoriContraction K N M Nbar g)
    (hMN : M ≤ Subgroup.normalizer N) (r : ℕ)
    (v : fixedVectors ρ K.toSubgroup) :
    mk ρ N ((compressedAction ρ hρ K hK g ^ r) v : V) =
      action ρ N M hMN (⟨g, h.mem_levi⟩ ^ r) (mk ρ N (v : V)) := by
  induction r generalizing v with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply,
      mk_compressedAction_of_iwahoriContraction ρ hρ hK h hMN, ih,
      pow_succ', map_mul, Module.End.mul_apply]

include hρ hK in
/-- Each Levi-fixed Jacquet vector has a nonnegative-power translate in the image of
the actual quotient on `K`-fixed vectors. The exponent may be zero. -/
theorem exists_pow_fixedJacquetMap_preimage_of_iwahoriContraction
    (h : IsIwahoriContraction K N M Nbar g)
    (hMN : M ≤ Subgroup.normalizer N)
    (y : fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype)) :
    ∃ (s : ℕ) (x : fixedVectors ρ K.toSubgroup),
      mk ρ N (x : V) =
        action ρ N M hMN (⟨g, h.mem_levi⟩ ^ s) (y : Coinvariants ρ N) := by
  let gM : M := ⟨g, h.mem_levi⟩
  obtain ⟨v, hv⟩ := mk_surjective ρ N (y : Coinvariants ρ N)
  obtain ⟨s, hs⟩ := h.exists_pow_lower_fixed ρ hρ v
  have hgs : ((gM ^ s : M) : G) = g ^ s := by simp [gM]
  have hlevi : ∀ m ∈ K.toSubgroup ⊓ M,
      mk ρ N (ρ m (ρ (g ^ s) v)) =
        action ρ N M hMN (gM ^ s) (y : Coinvariants ρ N) := by
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
  have hconst : ∀ k : K,
      mk ρ N (ρ k.val (ρ (g ^ s) v)) =
        action ρ N M hMN (gM ^ s) (y : Coinvariants ρ N) := by
    intro k
    obtain ⟨l, hl, m, hm, u, hu, hprod⟩ := h.factor k.val⁻¹ (K.inv_mem k.property)
    have heq : k.val = u⁻¹ * (m⁻¹ * l⁻¹) := by
      rw [← inv_inv k.val, hprod]
      group
    rw [heq, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      hs _ ((K.toSubgroup ⊓ Nbar).inv_mem hl)]
    rw [mk_apply_subgroup ρ N ⟨u⁻¹, N.inv_mem hu.2⟩]
    exact hlevi _ ((K.toSubgroup ⊓ M).inv_mem hm)
  refine ⟨s, ⟨Compact.averageMap ρ hρ K hK (ρ (g ^ s) v),
    Compact.averageMap_mem_fixedVectors ρ hρ K hK _⟩, ?_⟩
  exact map_averageMap_of_forall_eq ρ hρ K hK (mk ρ N) _ _ hconst

/-- Stationarity of the compression ranges suffices for the generalized
Jacquet lemma. No kernel stationarity or finite dimensionality is required. -/
theorem fixedJacquetMap_surjective_of_stationaryRanges
    (h : IsIwahoriContraction K N M Nbar g)
    (hMN : M ≤ Subgroup.normalizer N)
    (hstationary : ∃ b : ℕ, ∀ s : ℕ, b ≤ s →
      LinearMap.range (compressedAction ρ hρ K hK g ^ s) =
        LinearMap.range (compressedAction ρ hρ K hK g ^ b)) :
    Function.Surjective (fixedJacquetMap ρ N M hMN K.toSubgroup) := by
  obtain ⟨b, hb⟩ := hstationary
  let C := compressedAction ρ hρ K hK g
  let gM : M := ⟨g, h.mem_levi⟩
  intro y
  obtain ⟨s, x, hx⟩ :=
    exists_pow_fixedJacquetMap_preimage_of_iwahoriContraction ρ hρ hK h hMN y
  have hrange : (C ^ b) x ∈ LinearMap.range (C ^ (b + s)) := by
    rw [hb (b + s) (Nat.le_add_right b s)]
    exact LinearMap.mem_range_self _ x
  obtain ⟨w, hw⟩ := hrange
  refine ⟨w, Subtype.ext ?_⟩
  apply (Representation.apply_bijective (action ρ N M hMN) (gM ^ (b + s))).injective
  calc
    action ρ N M hMN (gM ^ (b + s)) (mk ρ N (w : V)) =
        mk ρ N ((C ^ (b + s)) w : V) :=
      (mk_compressedAction_pow_of_iwahoriContraction ρ hρ hK h hMN (b + s) w).symm
    _ = mk ρ N ((C ^ b) x : V) :=
      congrArg (fun z : fixedVectors ρ K.toSubgroup => mk ρ N (z : V)) hw
    _ = action ρ N M hMN (gM ^ b) (mk ρ N (x : V)) :=
      mk_compressedAction_pow_of_iwahoriContraction ρ hρ hK h hMN b x
    _ = action ρ N M hMN (gM ^ (b + s)) (y : Coinvariants ρ N) := by
      rw [hx, pow_add, map_mul, Module.End.mul_apply]

/-- With the published kernel/stable-image splitting, the quotient on the
stable image is bijective as soon as the compression ranges are stationary. -/
theorem stableImageJacquetMap_bijective_of_stationaryRanges
    (h : IsIwahoriContraction K N M Nbar g)
    (hMN : M ≤ Subgroup.normalizer N)
    (hstationary : ∃ b : ℕ, ∀ s : ℕ, b ≤ s →
      LinearMap.range (compressedAction ρ hρ K hK g ^ s) =
        LinearMap.range (compressedAction ρ hρ K hK g ^ b))
    (hsplit : CompactCompressionSplits ρ hρ K hK g) :
    Function.Bijective (stableImageJacquetMap ρ hρ K hK g N M hMN) := by
  have hker := powerKernelSup_eq_ker_of_iwahoriContraction ρ hρ hK h hMN
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro t ht
    have h1 : (t : fixedVectors ρ K.toSubgroup) ∈
        LinearMap.ker (fixedJacquetMap ρ N M hMN K.toSubgroup) := ht
    rw [← hker] at h1
    have h0 := hsplit.disjoint.le_bot ⟨h1, t.property⟩
    exact Subtype.ext (by simpa using h0)
  · intro y
    obtain ⟨x, hx⟩ :=
      fixedJacquetMap_surjective_of_stationaryRanges ρ hρ hK h hMN hstationary y
    have hxmem : x ∈ powerKernelSup ρ hρ K hK g ⊔ stableImage ρ hρ K hK g := by
      rw [hsplit.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨k, hk, t, ht, hkt⟩ := Submodule.mem_sup.mp hxmem
    have hk0 : fixedJacquetMap ρ N M hMN K.toSubgroup k = 0 := by
      rwa [hker, LinearMap.mem_ker] at hk
    refine ⟨⟨t, ht⟩, ?_⟩
    change fixedJacquetMap ρ N M hMN K.toSubgroup t = y
    calc
      _ = fixedJacquetMap ρ N M hMN K.toSubgroup (k + t) := by
        rw [map_add, hk0, zero_add]
      _ = fixedJacquetMap ρ N M hMN K.toSubgroup x := congrArg _ hkt
      _ = y := hx

/-- The actual stable-image Jacquet isomorphism from stationary compression
ranges and the kernel/stable-image splitting. -/
def stationaryRangeJacquetEquiv
    (h : IsIwahoriContraction K N M Nbar g)
    (hMN : M ≤ Subgroup.normalizer N)
    (hstationary : ∃ b : ℕ, ∀ s : ℕ, b ≤ s →
      LinearMap.range (compressedAction ρ hρ K hK g ^ s) =
        LinearMap.range (compressedAction ρ hρ K hK g ^ b))
    (hsplit : CompactCompressionSplits ρ hρ K hK g) :
    stableImage ρ hρ K hK g ≃ₗ[ℂ]
      fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype) :=
  LinearEquiv.ofBijective (stableImageJacquetMap ρ hρ K hK g N M hMN)
    (stableImageJacquetMap_bijective_of_stationaryRanges ρ hρ hK h hMN
      hstationary hsplit)

@[simp]
theorem stationaryRangeJacquetEquiv_apply
    (h : IsIwahoriContraction K N M Nbar g)
    (hMN : M ≤ Subgroup.normalizer N)
    (hstationary : ∃ b : ℕ, ∀ s : ℕ, b ≤ s →
      LinearMap.range (compressedAction ρ hρ K hK g ^ s) =
        LinearMap.range (compressedAction ρ hρ K hK g ^ b))
    (hsplit : CompactCompressionSplits ρ hρ K hK g)
    (v : stableImage ρ hρ K hK g) :
    stationaryRangeJacquetEquiv ρ hρ hK h hMN hstationary hsplit v =
      stableImageJacquetMap ρ hρ K hK g N M hMN v := rfl

end Langlands.Jacquet

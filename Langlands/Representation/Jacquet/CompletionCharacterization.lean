import Langlands.Representation.Jacquet.CompletionComparison

/-!
# Completion comparison at arbitrary Iwahori factorizations

Compact exhaustion of the lower group makes the comparison independent of
which contracting element certifies the target compact index.
-/

noncomputable section

namespace Langlands.Jacquet

open Langlands.HarishChandraSchwartz Langlands.CompactCompletion

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {N M Nbar : Subgroup G} {g : G} {K L : OpenSubgroup G}
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable (hK : IsCompact (K : Set G)) (hL : IsCompact (L : Set G))

/-- A stable source with an opposite contraction compares to any target
Iwahori factorization, even when the target has another contracting element. -/
theorem map_mk_averageMap_of_opposite_stableImage
    (hfactor : ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar,
      ∃ m ∈ K.toSubgroup ⊓ M, ∃ u ∈ K.toSubgroup ⊓ N, k = l * m * u)
    (h' : IsIwahoriContraction L N M Nbar g) (hLK : L ≤ K)
    (hopp : IsIwahoriContraction L Nbar M N g⁻¹)
    (hNbar : IsClosed (Nbar : Set G))
    (hMNbar : M ≤ Subgroup.normalizer Nbar)
    (hMN : M ≤ Subgroup.normalizer N)
    (hcentral : ∀ m ∈ M, m * g = g * m)
    (v : stableImage ρ hρ L hL g)
    (f : Coinvariants ρ N →ₗ[ℂ] W)
    (hf : ∀ m : M, (m : G) ∈ K →
      f (action ρ N M hMN m (mk ρ N (v : fixedVectors ρ L.toSubgroup))) =
        f (mk ρ N (v : fixedVectors ρ L.toSubgroup))) :
    f (mk ρ N (Compact.averageMap ρ hρ K hK
        (v : fixedVectors ρ L.toSubgroup))) =
      f (mk ρ N (v : fixedVectors ρ L.toSubgroup)) := by
  obtain ⟨s, hs'⟩ := hopp.exists_uniform_exhaust hMNbar
    ((K : Set G) ∩ (Nbar : Set G)) (hK.inter_right hNbar) Set.inter_subset_right
  have hs : ∀ x ∈ K.toSubgroup ⊓ Nbar, (g ^ s)⁻¹ * x * g ^ s ∈ L := by
    intro x hx
    simpa only [inv_pow, inv_inv] using hs' x hx
  obtain ⟨w, hw⟩ := (mem_stableImage ρ hρ L hL g v.val).mp v.property s
  let u : V := ρ (g ^ s) (w : V)
  have hveu : ((v : fixedVectors ρ L.toSubgroup) : V) =
      Compact.averageMap ρ hρ L hL u := by
    rw [← hw, ← h'.compressedAction_pow ρ hρ hL s]
    rfl
  have hfixLower : ∀ x ∈ K.toSubgroup ⊓ Nbar, ρ x u = u := by
    intro x hx
    have heq : x * g ^ s = g ^ s * ((g ^ s)⁻¹ * x * g ^ s) := by group
    change ρ x (ρ (g ^ s) (w : V)) = _
    rw [← Module.End.mul_apply, ← map_mul, heq, map_mul, Module.End.mul_apply,
      apply_eq_of_mem_fixedVectors ρ w.property (hs x hx)]
  have hfixLevi : ∀ m ∈ L.toSubgroup ⊓ M, ρ m u = u := by
    intro m hm
    change ρ m (ρ (g ^ s) (w : V)) = _
    rw [← Module.End.mul_apply, ← map_mul,
      (Commute.pow_right (hcentral m hm.2) s).eq, map_mul, Module.End.mul_apply,
      apply_eq_of_mem_fixedVectors ρ w.property hm.1]
  have hclass : mk ρ N (v : fixedVectors ρ L.toSubgroup) = mk ρ N u := by
    rw [hveu]
    apply map_averageMap_of_forall_eq ρ hρ L hL (mk ρ N) u
    intro k
    obtain ⟨l, hl, m, hm, a, ha, hk⟩ := h'.factor k.val⁻¹ (L.inv_mem k.property)
    have heq : k.val = a⁻¹ * (m⁻¹ * l⁻¹) := by
      rw [← inv_inv k.val, hk]
      group
    rw [heq, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      hfixLower l⁻¹ ⟨hLK (L.inv_mem hl.1), Nbar.inv_mem hl.2⟩,
      hfixLevi m⁻¹ ((L.toSubgroup ⊓ M).inv_mem hm),
      mk_apply_subgroup ρ N ⟨a⁻¹, N.inv_mem ha.2⟩]
  have hclass' : mk ρ N (Compact.averageMap ρ hρ L hL u) = mk ρ N u := by
    rw [← hveu]
    exact hclass
  rw [hveu, averageMap_averageMap_of_le ρ hρ K L hK hL hLK, hclass']
  apply map_averageMap_of_forall_eq ρ hρ K hK (f.comp (mk ρ N)) u
  intro k
  obtain ⟨l, hl, m, hm, a, ha, hk⟩ := hfactor k.val⁻¹ (K.inv_mem k.property)
  have heq : k.val = a⁻¹ * (m⁻¹ * l⁻¹) := by
    rw [← inv_inv k.val, hk]
    group
  change f (mk ρ N (ρ k.val u)) = _
  rw [heq, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    hfixLower l⁻¹ ((K.toSubgroup ⊓ Nbar).inv_mem hl),
    mk_apply_subgroup ρ N ⟨a⁻¹, N.inv_mem ha.2⟩]
  have hfm := hf ⟨m⁻¹, M.inv_mem hm.2⟩ (K.inv_mem hm.1)
  rw [hclass, action_mk] at hfm
  exact hfm

/-- Actual Jacquet and Levi averaging compatibility at an arbitrary target
Iwahori factorization. Only the source needs the fixed opposite contractions. -/
theorem mk_averageMap_eq_leviAverage_of_opposite_stableImage
    (hfactor : ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar,
      ∃ m ∈ K.toSubgroup ⊓ M, ∃ u ∈ K.toSubgroup ⊓ N, k = l * m * u)
    (h' : IsIwahoriContraction L N M Nbar g) (hLK : L ≤ K)
    (hopp : IsIwahoriContraction L Nbar M N g⁻¹)
    (hNbar : IsClosed (Nbar : Set G))
    (hMNbar : M ≤ Subgroup.normalizer Nbar)
    (hMN : M ≤ Subgroup.normalizer N)
    (hcentral : ∀ m ∈ M, m * g = g * m)
    (hM : IsClosed (M : Set G))
    (v : stableImage ρ hρ L hL g) :
    mk ρ N (Compact.averageMap ρ hρ K hK (v : fixedVectors ρ L.toSubgroup)) =
      Compact.averageMap (action ρ N M hMN) (isSmooth_action ρ N M hMN hρ)
        (leviCompactIndex M hM ⟨K, hK⟩).1 (leviCompactIndex M hM ⟨K, hK⟩).2
          (mk ρ N (v : fixedVectors ρ L.toSubgroup)) := by
  let τ := action ρ N M hMN
  let hτ := isSmooth_action ρ N M hMN hρ
  let KM := leviCompactIndex M hM ⟨K, hK⟩
  have hfix : mk ρ N (Compact.averageMap ρ hρ K hK
      (v : fixedVectors ρ L.toSubgroup)) ∈ fixedVectors τ KM.1.toSubgroup := by
    intro m
    change action ρ N M hMN m.val
      (mk ρ N (Compact.averageMap ρ hρ K hK (v : fixedVectors ρ L.toSubgroup))) = _
    rw [action_mk]
    exact congrArg (mk ρ N) (apply_eq_of_mem_fixedVectors ρ
      (Compact.averageMap_mem_fixedVectors ρ hρ K hK _) m.property)
  have hid : Compact.averageMap τ hτ KM.1 KM.2
      (mk ρ N (Compact.averageMap ρ hρ K hK (v : fixedVectors ρ L.toSubgroup))) =
      mk ρ N (Compact.averageMap ρ hρ K hK (v : fixedVectors ρ L.toSubgroup)) :=
    Compact.averageMap_id τ hτ KM.1 KM.2 _ hfix
  rw [← hid]
  apply map_mk_averageMap_of_opposite_stableImage ρ hρ hK hL hfactor h' hLK
    hopp hNbar hMNbar hMN hcentral v
  intro m hm
  exact averageMap_apply_of_mem τ hτ KM.1 KM.2 hm _


variable (N M Nbar : Subgroup G) (g : G)

/-- Take the genuine Jacquet quotient of an ambient stable-family component. -/
def stableCompletionJacquetComponentMap (K : CompactOpenSubgroup G) :
    stableImageCompletion ρ hρ N M Nbar g →ₗ[ℂ] Coinvariants ρ N where
  toFun v := mk ρ N (v.val.val K)
  map_add' _ _ := (mk ρ N).map_add _ _
  map_smul' _ _ := (mk ρ N).map_smul _ _

/-- The completion comparison has its quotient-component formula at every
Iwahori factorization, independently of its chosen contracting element. -/
theorem stableCompletionJacquetMap_apply_of_factor
    (hMN : M ≤ Subgroup.normalizer N)
    (hMNbar : M ≤ Subgroup.normalizer Nbar)
    (hcentral : ∀ m ∈ M, m * g = g * m)
    (hM : IsClosed (M : Set G)) (hNbar : IsClosed (Nbar : Set G))
    (hS : CompactCompletion.IsCofinal (oppositeCompressionIndices N M Nbar g))
    (hSM : CompactCompletion.IsCofinal
      (leviCompactIndex M hM '' oppositeCompressionIndices N M Nbar g))
    (v : stableImageCompletion ρ hρ N M Nbar g) (K : CompactOpenSubgroup G)
    (hfactor : ∀ k ∈ K.1, ∃ l ∈ K.1.toSubgroup ⊓ Nbar,
      ∃ m ∈ K.1.toSubgroup ⊓ M, ∃ u ∈ K.1.toSubgroup ⊓ N, k = l * m * u) :
    (stableCompletionJacquetMap ρ hρ N M Nbar g hMN hcentral hM hS hSM v).val
      (leviCompactIndex M hM K) =
        stableCompletionJacquetComponentMap ρ hρ N M Nbar g K v := by
  obtain ⟨L, hLS, hLK⟩ := hS K
  let L' : oppositeCompressionIndices N M Nbar g := ⟨L, hLS⟩
  rw [stableCompletionJacquetMap_apply ρ hρ N M Nbar g hMN hcentral hM hS hSM v
    (leviCompactIndex M hM K) L' (leviCompactIndex_mono M hM hLK)]
  have hcompat := mk_averageMap_eq_leviAverage_of_opposite_stableImage ρ hρ K.2 L.2
    hfactor hLS.1 hLK hLS.2 hNbar hMNbar hMN hcentral hM
      (stableCompletionComponent ρ hρ N M Nbar g v L')
  change mk ρ N (Compact.averageMap ρ hρ K.1 K.2 (v.val.val L)) =
    Compact.averageMap (action ρ N M hMN) (isSmooth_action ρ N M hMN hρ)
      (leviCompactIndex M hM K).1 (leviCompactIndex M hM K).2
        (mk ρ N (v.val.val L)) at hcompat
  rw [← hcompat]
  change mk ρ N (Compact.averageMap ρ hρ K.1 K.2 (v.val.val L)) =
    mk ρ N (v.val.val K)
  exact congrArg (mk ρ N) (v.val.property K L hLK)

end Langlands.Jacquet

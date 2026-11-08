import Langlands.Representation.Jacquet.StableImageAveraging
import Langlands.Representation.Jacquet.StablePairingProof
import Langlands.Representation.Smooth.CompactCompletionCofinal

/-!
# Averaging transitions for stable Jacquet lifts

Nested compact averages preserve stable images and commute, on those images,
with the actual Jacquet map and averaging over the Levi intersection.
-/

noncomputable section

namespace Langlands.Jacquet

open Langlands.HarishChandraSchwartz

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The compact open Levi intersection, with the induced subgroup topology. -/
def leviCompactIndex (M : Subgroup G) (hM : IsClosed (M : Set G))
    (K : CompactOpenSubgroup G) : CompactOpenSubgroup M :=
  ⟨K.1.comap M.subtype continuous_subtype_val,
    hM.isClosedEmbedding_subtypeVal.isCompact_preimage K.2⟩

omit [IsTopologicalGroup G] in
@[simp]
theorem mem_leviCompactIndex (M : Subgroup G) (hM : IsClosed (M : Set G))
    (K : CompactOpenSubgroup G) (m : M) :
    m ∈ (leviCompactIndex M hM K).1 ↔ (m : G) ∈ K.1 :=
  Iff.rfl

omit [IsTopologicalGroup G] in
theorem leviCompactIndex_mono (M : Subgroup G) (hM : IsClosed (M : Set G))
    {K L : CompactOpenSubgroup G} (hLK : L.1 ≤ K.1) :
    (leviCompactIndex M hM L).1 ≤ (leviCompactIndex M hM K).1 :=
  fun _ hm => hLK hm

omit [IsTopologicalGroup G] in
/-- A neighborhood-cofinal family in the ambient group has cofinal Levi
intersections. The ambient family is supplied at every open neighborhood. -/
theorem leviCompactIndex_cofinal (M : Subgroup G) (hM : IsClosed (M : Set G))
    (S : Set (CompactOpenSubgroup G))
    (hS : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K ∈ S, (K.1 : Set G) ⊆ O) :
    CompactCompletion.IsCofinal (leviCompactIndex M hM '' S) := by
  intro J
  obtain ⟨O, hO, heq⟩ :=
    Topology.IsInducing.subtypeVal.isOpen_iff.mp J.1.isOpen
  have heq' : (Subtype.val : M → G) ⁻¹' O = (J.1 : Set M) := heq
  have h1O : (1 : G) ∈ O := by
    have h1 : (1 : M) ∈ (Subtype.val : M → G) ⁻¹' O := by
      rw [heq']
      exact J.1.one_mem
    exact h1
  obtain ⟨K, hKS, hKO⟩ := hS O hO h1O
  refine ⟨leviCompactIndex M hM K, ⟨K, hKS, rfl⟩, ?_⟩
  intro m hm
  have hmO : m ∈ (Subtype.val : M → G) ⁻¹' O := hKO hm
  rw [heq'] at hmO
  exact hmO

variable {N M Nbar : Subgroup G} {g : G}
variable {K L : OpenSubgroup G}

omit [IsTopologicalGroup G] in
/-- A single shift compares every expanded lower factor for `K` with the
corresponding expanded factor for `L`. -/
theorem exists_expandedLowerSubgroup_le_shift
    (h : IsIwahoriContraction K N M Nbar g)
    (hMNbar : M ≤ Subgroup.normalizer Nbar) :
    ∃ s : ℕ, ∀ b : ℕ,
      expandedLowerSubgroup K Nbar g b ≤ expandedLowerSubgroup L Nbar g (b + s) := by
  obtain ⟨s, hs⟩ := h.contract L
  refine ⟨s, fun b => ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxNbar : (g ^ s)⁻¹ * x * g ^ s ∈ Nbar := by
    simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp
        (inv_mem (pow_mem (hMNbar h.mem_levi) s)) x).mp hx.2
  refine ⟨(g ^ s)⁻¹ * x * g ^ s, ⟨hs x hx, hxNbar⟩, ?_⟩
  change g ^ (b + s) * ((g ^ s)⁻¹ * x * g ^ s) * (g ^ (b + s))⁻¹ =
    g ^ b * x * (g ^ b)⁻¹
  rw [pow_add]
  group

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable (hK : IsCompact (K : Set G)) (hL : IsCompact (L : Set G))

/-- Averaging a stable vector from a smaller contraction index to a larger
one preserves the stable image. Stationarity is not needed. -/
theorem averageMap_mem_stableImage
    (h : IsIwahoriContraction K N M Nbar g)
    (h' : IsIwahoriContraction L N M Nbar g) (hLK : L ≤ K)
    (hMNbar : M ≤ Subgroup.normalizer Nbar)
    (hcentral : ∀ m ∈ M, m * g = g * m)
    (v : stableImage ρ hρ L hL g) :
    (⟨Compact.averageMap ρ hρ K hK (v : fixedVectors ρ L.toSubgroup),
        Compact.averageMap_mem_fixedVectors ρ hρ K hK _⟩ :
      fixedVectors ρ K.toSubgroup) ∈ stableImage ρ hρ K hK g := by
  obtain ⟨s, hs⟩ := exists_expandedLowerSubgroup_le_shift (L := L) h hMNbar
  rw [stableImage, Submodule.mem_iInf]
  intro b
  have hv : ((v : fixedVectors ρ L.toSubgroup) : V) ∈
      (LinearMap.range (compressedAction ρ hρ L hL g ^ (b + s))).map
        (fixedVectors ρ L.toSubgroup).subtype :=
    ⟨v.val, (iInf_le (fun r : ℕ =>
      LinearMap.range (compressedAction ρ hρ L hL g ^ r)) (b + s)) v.property, rfl⟩
  rw [compressionRange_eq_average_expandedLower_fixed ρ hρ hL h' hcentral] at hv
  obtain ⟨w, hw, hweq⟩ := hv
  have hkw : Compact.averageMap ρ hρ K hK (v : fixedVectors ρ L.toSubgroup) =
      Compact.averageMap ρ hρ K hK w := by
    rw [← hweq, averageMap_averageMap_of_le ρ hρ K L hK hL hLK]
  have hmem : Compact.averageMap ρ hρ K hK w ∈
      (LinearMap.range (compressedAction ρ hρ K hK g ^ b)).map
        (fixedVectors ρ K.toSubgroup).subtype := by
    rw [compressionRange_eq_average_expandedLower_fixed ρ hρ hK h hcentral]
    exact ⟨w, fixedVectors_antitone ρ (hs b) hw, rfl⟩
  obtain ⟨u, hu, hueq⟩ := hmem
  have heq : u = (⟨Compact.averageMap ρ hρ K hK (v : fixedVectors ρ L.toSubgroup),
      Compact.averageMap_mem_fixedVectors ρ hρ K hK _⟩ :
      fixedVectors ρ K.toSubgroup) :=
    Subtype.ext (hueq.trans hkw.symm)
  exact heq ▸ hu

/-- The actual averaging transition between the stable-image spaces. -/
def stableAverageMap
    (h : IsIwahoriContraction K N M Nbar g)
    (h' : IsIwahoriContraction L N M Nbar g) (hLK : L ≤ K)
    (hMNbar : M ≤ Subgroup.normalizer Nbar)
    (hcentral : ∀ m ∈ M, m * g = g * m) :
    stableImage ρ hρ L hL g →ₗ[ℂ] stableImage ρ hρ K hK g where
  toFun v := ⟨⟨Compact.averageMap ρ hρ K hK (v : fixedVectors ρ L.toSubgroup),
    Compact.averageMap_mem_fixedVectors ρ hρ K hK _⟩,
    averageMap_mem_stableImage ρ hρ hK hL h h' hLK hMNbar hcentral v⟩
  map_add' _ _ := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Compact.averageMap ρ hρ K hK).map_add _ _
  map_smul' _ _ := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Compact.averageMap ρ hρ K hK).map_smul _ _

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Nested averaging preserves every Levi-invariant linear evaluation of the
Jacquet class of a stable vector. Only the two forward contractions are used. -/
theorem map_mk_averageMap_of_stableImage
    (h : IsIwahoriContraction K N M Nbar g)
    (h' : IsIwahoriContraction L N M Nbar g) (hLK : L ≤ K)
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
  obtain ⟨s, hs⟩ := h.contract L
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
  obtain ⟨l, hl, m, hm, a, ha, hk⟩ := h.factor k.val⁻¹ (K.inv_mem k.property)
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

/-- Jacquet images intertwine stable averaging transitions with the actual
compact-open averaging transitions on the Levi. -/
theorem mk_averageMap_eq_leviAverage_of_stableImage
    (h : IsIwahoriContraction K N M Nbar g)
    (h' : IsIwahoriContraction L N M Nbar g) (hLK : L ≤ K)
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
  apply map_mk_averageMap_of_stableImage ρ hρ hK hL h h' hLK hMN hcentral v
  intro m hm
  exact averageMap_apply_of_mem τ hτ KM.1 KM.2 hm _

end Langlands.Jacquet

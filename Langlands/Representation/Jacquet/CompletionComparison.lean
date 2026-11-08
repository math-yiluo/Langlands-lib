import Langlands.Representation.Jacquet.CompletionTransitions
import Langlands.Representation.Jacquet.StableImageCompletion

/-!
# The stable-image completion and the Jacquet completion

The actual stable-image Jacquet isomorphisms assemble to a linear equivalence
of compatible families. Structural inputs and pointwise bijectivity are explicit.
-/

noncomputable section

namespace Langlands.Jacquet

open Langlands.HarishChandraSchwartz Langlands.CompactCompletion

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable (N M Nbar : Subgroup G) (g : G)
variable (hMN : M ≤ Subgroup.normalizer N)
variable (hMNbar : M ≤ Subgroup.normalizer Nbar)
variable (hcentral : ∀ m ∈ M, m * g = g * m)
variable (hM : IsClosed (M : Set G))

local notation "S" => oppositeCompressionIndices N M Nbar g
local notation "τ" => action ρ N M hMN
local notation "hτ" => isSmooth_action ρ N M hMN hρ
local notation "KM" => leviCompactIndex M hM
local notation "SC" => stableImageCompletion ρ hρ N M Nbar g

private def fixedCompletionComponent (v : completion ρ hρ)
    (K : CompactOpenSubgroup G) : fixedVectors ρ K.1.toSubgroup :=
  ⟨v.1 K, by
    rw [← v.property K K le_rfl]
    exact Compact.averageMap_mem_fixedVectors ρ hρ K.1 K.2 _⟩

/-- The component at a good index, regarded as an actual stable vector. -/
def stableCompletionComponent (v : SC) (K : S) :
    stableImage ρ hρ K.1.1 K.1.2 g :=
  ⟨fixedCompletionComponent ρ hρ v.val K.val, by
    obtain ⟨w, hw, hweq⟩ := v.property K.val K.property
    have heq : w = fixedCompletionComponent ρ hρ v.val K.val := Subtype.ext hweq
    exact heq ▸ hw⟩

@[simp]
theorem stableCompletionComponent_apply (v : SC) (K : S) :
    ((stableCompletionComponent ρ hρ N M Nbar g v K :
      fixedVectors ρ K.1.1.toSubgroup) : V) = v.val.val K.val :=
  rfl

include hcentral in
/-- Transition equations for Jacquet classes of stable completion components. -/
theorem stableCompletion_mk_transition (v : SC) (K L : S)
    (hLK : L.1.1 ≤ K.1.1) :
    mk ρ N (v.val.val K.val) =
      Compact.averageMap τ hτ (KM K.val).1 (KM K.val).2
        (mk ρ N (v.val.val L.val)) := by
  rw [← v.val.property K.val L.val hLK]
  exact mk_averageMap_eq_leviAverage_of_stableImage ρ hρ K.1.2 L.1.2
    K.property.1 L.property.1 hLK hMN hcentral hM
      (stableCompletionComponent ρ hρ N M Nbar g v L)

variable (hS : CompactCompletion.IsCofinal
  (oppositeCompressionIndices N M Nbar g))
  (hSM : CompactCompletion.IsCofinal
    (leviCompactIndex M hM '' oppositeCompressionIndices N M Nbar g))

include hSM in
omit [IsTopologicalGroup G] in
private theorem exists_index_levi_le (J : CompactOpenSubgroup M) :
    ∃ K : S, (KM K.val).1 ≤ J.1 := by
  obtain ⟨_, ⟨K, hKS, rfl⟩, hKJ⟩ := hSM J
  exact ⟨⟨K, hKS⟩, hKJ⟩

private def indexLeviBelow (J : CompactOpenSubgroup M) : S :=
  (exists_index_levi_le N M Nbar g hM hSM J).choose

omit [IsTopologicalGroup G] in
private theorem indexLeviBelow_le (J : CompactOpenSubgroup M) :
    (KM (indexLeviBelow N M Nbar g hM hSM J).val).1 ≤ J.1 :=
  (exists_index_levi_le N M Nbar g hM hSM J).choose_spec

include hcentral hS in
/-- The average of a stable completion's Jacquet component is independent of
the good ambient index whose Levi intersection lies below the target. -/
theorem stableCompletion_average_mk_eq (v : SC)
    (J : CompactOpenSubgroup M) (K L : S)
    (hKJ : (KM K.val).1 ≤ J.1) (hLJ : (KM L.val).1 ≤ J.1) :
    Compact.averageMap τ hτ J.1 J.2 (mk ρ N (v.val.val K.val)) =
      Compact.averageMap τ hτ J.1 J.2 (mk ρ N (v.val.val L.val)) := by
  obtain ⟨R, hRS, hRKL⟩ := hS (K.val.inf L.val)
  let R' : S := ⟨R, hRS⟩
  have hRK : R.1 ≤ K.1.1 := hRKL.trans inf_le_left
  have hRL : R.1 ≤ L.1.1 := hRKL.trans inf_le_right
  rw [stableCompletion_mk_transition ρ hρ N M Nbar g hMN hcentral hM v K R' hRK,
    stableCompletion_mk_transition ρ hρ N M Nbar g hMN hcentral hM v L R' hRL,
    averageMap_averageMap_of_le τ hτ J.1 (KM K.val).1 J.2 (KM K.val).2 hKJ,
    averageMap_averageMap_of_le τ hτ J.1 (KM L.val).1 J.2 (KM L.val).2 hLJ]

private def stableJacquetFamily (v : SC) (J : CompactOpenSubgroup M) :
    Coinvariants ρ N :=
  Compact.averageMap τ hτ J.1 J.2
    (mk ρ N (v.val.val (indexLeviBelow N M Nbar g hM hSM J).val))

include hcentral hS in
private theorem stableJacquetFamily_eq (v : SC) (J : CompactOpenSubgroup M)
    (K : S) (hKJ : (KM K.val).1 ≤ J.1) :
    stableJacquetFamily ρ hρ N M Nbar g hMN hM hSM v J =
      Compact.averageMap τ hτ J.1 J.2 (mk ρ N (v.val.val K.val)) :=
  stableCompletion_average_mk_eq ρ hρ N M Nbar g hMN hcentral hM hS v J
    _ K (indexLeviBelow_le N M Nbar g hM hSM J) hKJ

/-- The actual Jacquet map on stable completion families. At an arbitrary Levi
index, average the Jacquet class at any good smaller ambient intersection. -/
def stableCompletionJacquetMap : SC →ₗ[ℂ] completion τ hτ where
  toFun v := ⟨stableJacquetFamily ρ hρ N M Nbar g hMN hM hSM v, by
    intro J I hIJ
    let K := indexLeviBelow N M Nbar g hM hSM I
    have hKI : (KM K.val).1 ≤ I.1 := indexLeviBelow_le N M Nbar g hM hSM I
    rw [stableJacquetFamily_eq ρ hρ N M Nbar g hMN hcentral hM hS hSM v I K hKI,
      stableJacquetFamily_eq ρ hρ N M Nbar g hMN hcentral hM hS hSM v J K
        (hKI.trans hIJ),
      averageMap_averageMap_of_le τ hτ J.1 I.1 J.2 I.2 hIJ]⟩
  map_add' v w := by
    apply Subtype.ext
    funext J
    change Compact.averageMap τ hτ J.1 J.2 (mk ρ N (_ + _)) = _
    rw [map_add, map_add]
    rfl
  map_smul' c v := by
    apply Subtype.ext
    funext J
    change Compact.averageMap τ hτ J.1 J.2 (mk ρ N (c • _)) = _
    rw [map_smul, map_smul]
    rfl

/-- Every good smaller intersection computes a component of the map. -/
theorem stableCompletionJacquetMap_apply (v : SC) (J : CompactOpenSubgroup M)
    (K : S) (hKJ : (KM K.val).1 ≤ J.1) :
    (stableCompletionJacquetMap ρ hρ N M Nbar g hMN hcentral hM hS hSM v).val J =
      Compact.averageMap τ hτ J.1 J.2 (mk ρ N (v.val.val K.val)) :=
  stableJacquetFamily_eq ρ hρ N M Nbar g hMN hcentral hM hS hSM v J K hKJ

/-- On each good Levi intersection the map is literally the Jacquet quotient. -/
theorem stableCompletionJacquetMap_apply_levi (v : SC) (K : S) :
    (stableCompletionJacquetMap ρ hρ N M Nbar g hMN hcentral hM hS hSM v).val
      (KM K.val) = mk ρ N (v.val.val K.val) := by
  rw [stableCompletionJacquetMap_apply ρ hρ N M Nbar g hMN hcentral hM hS hSM v
    (KM K.val) K le_rfl]
  apply Compact.averageMap_id
  intro m
  change action ρ N M hMN m.val (mk ρ N (v.val.val K.val)) = _
  rw [action_mk]
  exact congrArg (mk ρ N) (apply_eq_of_mem_fixedVectors ρ
    (fixedCompletionComponent ρ hρ v.val K.val).property m.property)

variable (hbij : ∀ K : oppositeCompressionIndices N M Nbar g,
  Function.Bijective (stableImageJacquetMap ρ hρ K.1.1 K.1.2 g N M hMN))

private def stableLiftCompletionComponent (y : completion τ hτ) (K : S) :
    stableImage ρ hρ K.1.1 K.1.2 g :=
  (LinearEquiv.ofBijective (stableImageJacquetMap ρ hρ K.1.1 K.1.2 g N M hMN)
    (hbij K)).symm (fixedCompletionComponent τ hτ y (KM K.val))

private theorem mk_stableLiftCompletionComponent (y : completion τ hτ) (K : S) :
    mk ρ N ((stableLiftCompletionComponent ρ hρ N M Nbar g hMN hM hbij y K :
      fixedVectors ρ K.1.1.toSubgroup) : V) = y.val (KM K.val) := by
  have heq := (LinearEquiv.ofBijective
    (stableImageJacquetMap ρ hρ K.1.1 K.1.2 g N M hMN) (hbij K)).apply_symm_apply
      (fixedCompletionComponent τ hτ y (KM K.val))
  exact congrArg Subtype.val heq

include hMNbar hcentral in
private theorem stableLiftCompletionComponent_transition (y : completion τ hτ)
    (K L : S) (hLK : L.1.1 ≤ K.1.1) :
    Compact.averageMap ρ hρ K.1.1 K.1.2
      ((stableLiftCompletionComponent ρ hρ N M Nbar g hMN hM hbij y L :
        fixedVectors ρ L.1.1.toSubgroup) : V) =
      ((stableLiftCompletionComponent ρ hρ N M Nbar g hMN hM hbij y K :
        fixedVectors ρ K.1.1.toSubgroup) : V) := by
  let u := stableAverageMap ρ hρ K.1.2 L.1.2 K.property.1 L.property.1 hLK hMNbar
    hcentral (stableLiftCompletionComponent ρ hρ N M Nbar g hMN hM hbij y L)
  have heq : u = stableLiftCompletionComponent ρ hρ N M Nbar g hMN hM hbij y K := by
    apply (hbij K).injective
    apply Subtype.ext
    change mk ρ N (Compact.averageMap ρ hρ K.1.1 K.1.2
      ((stableLiftCompletionComponent ρ hρ N M Nbar g hMN hM hbij y L :
        fixedVectors ρ L.1.1.toSubgroup) : V)) =
      mk ρ N ((stableLiftCompletionComponent ρ hρ N M Nbar g hMN hM hbij y K :
        fixedVectors ρ K.1.1.toSubgroup) : V)
    rw [mk_averageMap_eq_leviAverage_of_stableImage ρ hρ K.1.2 L.1.2
      K.property.1 L.property.1 hLK hMN hcentral hM,
      mk_stableLiftCompletionComponent ρ hρ N M Nbar g hMN hM hbij y L,
      mk_stableLiftCompletionComponent ρ hρ N M Nbar g hMN hM hbij y K]
    exact y.property (KM K.val) (KM L.val) (leviCompactIndex_mono M hM hLK)
  exact congrArg (fun z : stableImage ρ hρ K.1.1 K.1.2 g =>
    ((z : fixedVectors ρ K.1.1.toSubgroup) : V)) heq

private def stableLiftCompletionOn (y : completion τ hτ) : completionOn ρ hρ S :=
  ⟨fun K => ((stableLiftCompletionComponent ρ hρ N M Nbar g hMN hM hbij y K :
      fixedVectors ρ K.1.1.toSubgroup) : V),
    stableLiftCompletionComponent_transition ρ hρ N M Nbar g hMN hMNbar hcentral
      hM hbij y⟩

private theorem extend_stableLiftCompletionOn_apply (y : completion τ hτ) (K : S) :
    (extend hρ S hS
      (stableLiftCompletionOn ρ hρ N M Nbar g hMN hMNbar hcentral hM hbij y)).val K.val =
      ((stableLiftCompletionComponent ρ hρ N M Nbar g hMN hM hbij y K :
        fixedVectors ρ K.1.1.toSubgroup) : V) := by
  rw [extend_apply hρ S hS _ K.val K le_rfl]
  exact Compact.averageMap_id ρ hρ K.1.1 K.1.2 _
    (stableLiftCompletionComponent ρ hρ N M Nbar g hMN hM hbij y K).val.property

private def stableLiftCompletion (y : completion τ hτ) : SC :=
  ⟨extend hρ S hS
    (stableLiftCompletionOn ρ hρ N M Nbar g hMN hMNbar hcentral hM hbij y), by
    intro K hKS
    rw [extend_stableLiftCompletionOn_apply ρ hρ N M Nbar g hMN hMNbar hcentral
      hM hS hbij y ⟨K, hKS⟩]
    exact ⟨(stableLiftCompletionComponent ρ hρ N M Nbar g hMN hM hbij y ⟨K, hKS⟩).val,
      (stableLiftCompletionComponent ρ hρ N M Nbar g hMN hM hbij y ⟨K, hKS⟩).property,
      rfl⟩⟩

include hMNbar hbij in
/-- Bijectivity of the pointwise stable Jacquet maps gives bijectivity on
the actual compatible completion families. -/
theorem stableCompletionJacquetMap_bijective :
    Function.Bijective
      (stableCompletionJacquetMap ρ hρ N M Nbar g hMN hcentral hM hS hSM) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply (restrictEquiv hρ S hS).injective
    apply Subtype.ext
    funext K
    have hclass : mk ρ N (x.val.val K.val) = mk ρ N (y.val.val K.val) := by
      rw [← stableCompletionJacquetMap_apply_levi ρ hρ N M Nbar g hMN hcentral hM
          hS hSM x K,
        ← stableCompletionJacquetMap_apply_levi ρ hρ N M Nbar g hMN hcentral hM
          hS hSM y K]
      exact congrArg (fun z : completion τ hτ => z.val (KM K.val)) hxy
    have heq := (hbij K).injective
      (a₁ := stableCompletionComponent ρ hρ N M Nbar g x K)
      (a₂ := stableCompletionComponent ρ hρ N M Nbar g y K)
      (Subtype.ext hclass)
    exact congrArg (fun z : stableImage ρ hρ K.1.1 K.1.2 g =>
      ((z : fixedVectors ρ K.1.1.toSubgroup) : V)) heq
  · intro y
    refine ⟨stableLiftCompletion ρ hρ N M Nbar g hMN hMNbar hcentral hM hS hbij y, ?_⟩
    apply Subtype.ext
    funext J
    let K := indexLeviBelow N M Nbar g hM hSM J
    rw [stableCompletionJacquetMap_apply ρ hρ N M Nbar g hMN hcentral hM hS hSM
      _ J K (indexLeviBelow_le N M Nbar g hM hSM J)]
    change Compact.averageMap τ hτ J.1 J.2 (mk ρ N
      ((extend hρ S hS (stableLiftCompletionOn ρ hρ N M Nbar g hMN hMNbar
        hcentral hM hbij y)).val K.val)) = _
    rw [extend_stableLiftCompletionOn_apply ρ hρ N M Nbar g hMN hMNbar hcentral
      hM hS hbij y K,
      mk_stableLiftCompletionComponent ρ hρ N M Nbar g hMN hM hbij y K]
    exact y.property J (KM K.val) (indexLeviBelow_le N M Nbar g hM hSM J)

/-- The stable-image completion is linearly equivalent to the completion of
the actual unnormalized Jacquet representation. -/
def stableCompletionJacquetEquiv : SC ≃ₗ[ℂ] completion τ hτ :=
  LinearEquiv.ofBijective
    (stableCompletionJacquetMap ρ hρ N M Nbar g hMN hcentral hM hS hSM)
    (stableCompletionJacquetMap_bijective ρ hρ N M Nbar g hMN hMNbar hcentral
      hM hS hSM hbij)

end Langlands.Jacquet

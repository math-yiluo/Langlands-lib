import Langlands.Analysis.Local.QuotientTopology
import Langlands.Topology.CompactOpen.NeighborhoodBasis
import Langlands.Representation.Induction.CompactQuotientProof

/-! Compact clopen neighborhoods and cutoffs on the actual left-coset quotient. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open scoped Classical

open Topology Filter Set

namespace Langlands.Induction

universe uR uG uV

variable {G : Type uG} [Group G]

@[simp] theorem quotientRight_one (P : Subgroup G) (y : LeftQuotient P) :
    quotientRight P 1 y = y := by
  induction y using Quotient.inductionOn with
  | h x => change quotientMap P (x * 1) = quotientMap P x; rw [mul_one]

/-- Composition law for the genuine right quotient action. -/
theorem quotientRight_mul (P : Subgroup G) (g h : G) (y : LeftQuotient P) :
    quotientRight P (g * h) y = quotientRight P h (quotientRight P g y) := by
  induction y using Quotient.inductionOn with
  | h x => change quotientMap P (x * (g * h)) = quotientMap P ((x * g) * h)
           rw [mul_assoc]

/-- The subgroup preserving membership in a set of left cosets. -/
def quotientSetStabilizer (P : Subgroup G) (C : Set (LeftQuotient P)) : Subgroup G where
  carrier := {g | ∀ y, quotientRight P g y ∈ C ↔ y ∈ C}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh y
    rw [quotientRight_mul, hh, hg]
  inv_mem' := by
    intro g hg y
    have h := hg (quotientRight P g⁻¹ y)
    rw [← quotientRight_mul, inv_mul_cancel, quotientRight_one] at h
    exact h.symm

@[simp] theorem mem_quotientSetStabilizer (P : Subgroup G) (C : Set (LeftQuotient P))
    (g : G) : g ∈ quotientSetStabilizer P C ↔
      ∀ y, quotientRight P g y ∈ C ↔ y ∈ C := Iff.rfl

variable [TopologicalSpace G]

section Topological

variable [IsTopologicalGroup G]

/-- Right multiplication on left cosets is jointly continuous. -/
theorem continuous_quotientRight_joint (P : Subgroup G) :
    Continuous (fun z : G × LeftQuotient P => quotientRight P z.1 z.2) := by
  rw [← (IsOpenQuotientMap.id.prodMap
    (QuotientIntegration.leftQuotient_isOpenQuotientMap P)).continuous_comp_iff]
  exact continuous_quotient_mk'.comp (continuous_snd.mul continuous_fst)

/-- Compact open sets in the quotient have a uniform open right stabilizer. -/
theorem quotientSetStabilizer_isOpen (P : Subgroup G) (C : Set (LeftQuotient P))
    (hc : IsCompact C) (ho : IsOpen C) : IsOpen (quotientSetStabilizer P C : Set G) := by
  have h : ∀ᶠ g in 𝓝 (1 : G), ∀ y ∈ C, quotientRight P g y ∈ C := by
    apply hc.eventually_forall_of_forall_eventually
    intro y hy
    exact (continuous_quotientRight_joint P).continuousAt.eventually
      (ho.mem_nhds (by simpa using hy))
  have hi : ∀ᶠ g in 𝓝 (1 : G), ∀ y ∈ C, quotientRight P g⁻¹ y ∈ C :=
    (continuous_inv.tendsto (1 : G)).eventually (by simpa using h)
  apply (quotientSetStabilizer P C).isOpen_of_mem_nhds
  filter_upwards [h, hi] with g hg hgi
  intro y
  constructor
  · intro hy
    have h' := hgi (quotientRight P g y) hy
    simpa only [← quotientRight_mul, mul_inv_cancel, quotientRight_one] using h'
  · exact hg y

/-- The actual open setwise stabilizer of a compact open subset of the quotient. -/
def compactQuotientOpenStabilizer (P : Subgroup G) (C : Set (LeftQuotient P))
    (hc : IsCompact C) (ho : IsOpen C) : OpenSubgroup G :=
  ⟨quotientSetStabilizer P C, quotientSetStabilizer_isOpen P C hc ho⟩

@[simp] theorem mem_compactQuotientOpenStabilizer (P : Subgroup G)
    (C : Set (LeftQuotient P)) (hc : IsCompact C) (ho : IsOpen C) (g : G) :
    g ∈ compactQuotientOpenStabilizer P C hc ho ↔
      ∀ y, quotientRight P g y ∈ C ↔ y ∈ C := Iff.rfl

end Topological

section Neighborhoods

variable [NonarchimedeanGroup G] [LocallyCompactSpace G]

/-- Every open neighborhood in a closed-subgroup quotient contains a compact clopen one. -/
theorem exists_compactClopen_quotientNeighborhood (P : Subgroup G)
    (hP : IsClosed (P : Set G)) (y : LeftQuotient P) (U : Set (LeftQuotient P))
    (hU : IsOpen U) (hy : y ∈ U) :
    ∃ C : Set (LeftQuotient P), IsCompact C ∧ IsClopen C ∧ y ∈ C ∧ C ⊆ U := by
  let := QuotientIntegration.leftQuotient_t2Space P hP
  obtain ⟨x, rfl⟩ := Quotient.exists_rep y
  have hq := QuotientIntegration.leftQuotient_isOpenQuotientMap P
  have hn : (fun k : G => quotientMap P (x * k)) ⁻¹' U ∈ 𝓝 (1 : G) :=
    (hq.continuous.comp (continuous_const.mul continuous_id)).continuousAt.preimage_mem_nhds
      (hU.mem_nhds (by
        change quotientMap P (x * 1) ∈ U
        simpa only [mul_one, quotientMap] using hy))
  obtain ⟨K, hKc, hKU⟩ := compactOpenSubgroupBasis G _ hn
  let C := quotientMap P '' ((fun k => x * k) '' (K : Set G))
  have hCc : IsCompact C := (hKc.image (continuous_const.mul continuous_id)).image hq.continuous
  have hCo : IsOpen C := hq.isOpenMap _ (isOpenMap_mul_left x _ K.isOpen)
  refine ⟨C, hCc, ⟨hCc.isClosed, hCo⟩, ?_, ?_⟩
  · exact ⟨x, ⟨1, K.one_mem, mul_one x⟩, rfl⟩
  · rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact hKU hk

/-- Choose a compact clopen neighborhood inside a prescribed open neighborhood. -/
def compactClopenQuotientNeighborhood (P : Subgroup G) (hP : IsClosed (P : Set G))
    (y : LeftQuotient P) (U : Set (LeftQuotient P)) (hU : IsOpen U) (hy : y ∈ U) :
    {C : Set (LeftQuotient P) // IsCompact C ∧ IsClopen C ∧ y ∈ C ∧ C ⊆ U} :=
  ⟨_, (exists_compactClopen_quotientNeighborhood P hP y U hU hy).choose_spec⟩

theorem compactClopenQuotientNeighborhood_spec (P : Subgroup G)
    (hP : IsClosed (P : Set G)) (y : LeftQuotient P) (U : Set (LeftQuotient P))
    (hU : IsOpen U) (hy : y ∈ U) :
    let C := (compactClopenQuotientNeighborhood P hP y U hU hy).val
    IsCompact C ∧ IsClopen C ∧ y ∈ C ∧ C ⊆ U :=
  (compactClopenQuotientNeighborhood P hP y U hU hy).property

end Neighborhoods

section Cutoffs

variable [IsTopologicalGroup G]

variable {R : Type uR} {V : Type uV} [CommRing R] [AddCommGroup V] [Module R V]

/-- Cutting off a smooth covariant function by a compact open set of left cosets. -/
def smoothQuotientCutoff (P : Subgroup G) (σ : Representation R P V)
    (C : Set (LeftQuotient P)) (hc : IsCompact C) (ho : IsOpen C)
    (f : SmoothFunctions P σ) : SmoothFunctions P σ :=
  let K := f.property.choose
  let L := K ⊓ compactQuotientOpenStabilizer P C hc ho
  smoothFunctionOf P σ (fun x => if quotientMap P x ∈ C then eval P σ f x else 0)
    (by
      intro p x
      have hp : quotientMap P ((p : G) * x) = quotientMap P x := by
        apply Quotient.sound
        change (QuotientGroup.rightRel P) ((p : G) * x) x
        rw [QuotientGroup.rightRel_apply]
        simp [mul_inv_rev]
      rw [hp]
      split_ifs with hx
      · exact eval_covariant P σ f p x
      · exact (map_zero (σ p)).symm)
    L (by
      intro k x
      have hk : eval P σ f (x * (k : G)) = eval P σ f x :=
        congrArg (fun F : EquivariantFunctions P σ => F.1 x)
          (f.property.choose_spec ⟨k, k.property.1⟩)
      have hC : quotientMap P (x * (k : G)) ∈ C ↔ quotientMap P x ∈ C :=
        k.property.2 (quotientMap P x)
      simp only [hC, hk])

@[simp] theorem eval_smoothQuotientCutoff (P : Subgroup G) (σ : Representation R P V)
    (C : Set (LeftQuotient P)) (hc : IsCompact C) (ho : IsOpen C)
    (f : SmoothFunctions P σ) (x : G) :
    eval P σ (smoothQuotientCutoff P σ C hc ho f) x =
      if quotientMap P x ∈ C then eval P σ f x else 0 := rfl

/-- The projected support of the cutoff is exactly the old support intersected with C. -/
theorem quotientSupport_smoothQuotientCutoff (P : Subgroup G) (σ : Representation R P V)
    (C : Set (LeftQuotient P)) (hc : IsCompact C) (ho : IsOpen C)
    (f : SmoothFunctions P σ) :
    quotientSupport P (eval P σ (smoothQuotientCutoff P σ C hc ho f)) =
      C ∩ quotientSupport P (eval P σ f) := by
  classical
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (if quotientMap P x ∈ C then eval P σ f x else 0) ≠ 0 at hx
    by_cases hC : quotientMap P x ∈ C
    · rw [ite_eq_left hC] at hx
      exact ⟨hC, x, hx, rfl⟩
    · rw [ite_eq_right hC] at hx
      exact (hx rfl).elim
  · rintro ⟨hC, x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    change (if quotientMap P x ∈ C then eval P σ f x else 0) ≠ 0
    rw [ite_eq_left hC]
    exact hx

/-- A compact clopen cutoff of an actual compactly induced function. -/
def compactQuotientCutoff (P : Subgroup G) (σ : Representation R P V)
    (C : Set (LeftQuotient P)) (hc : IsCompact C) (hcl : IsClopen C)
    (f : CompactFunctions P σ) : CompactFunctions P σ :=
  ⟨smoothQuotientCutoff P σ C hc hcl.isOpen f.val, by
    apply hc.of_isClosed_subset (isClosed_quotientSupport P σ _)
    rw [quotientSupport_smoothQuotientCutoff]
    exact inter_subset_left⟩

@[simp] theorem eval_compactQuotientCutoff (P : Subgroup G) (σ : Representation R P V)
    (C : Set (LeftQuotient P)) (hc : IsCompact C) (hcl : IsClopen C)
    (f : CompactFunctions P σ) (x : G) :
    eval P σ (compactQuotientCutoff P σ C hc hcl f).val x =
      if quotientMap P x ∈ C then eval P σ f.val x else 0 := rfl

/-- Exact projected support formula for a compact clopen cutoff. -/
theorem quotientSupport_compactQuotientCutoff (P : Subgroup G) (σ : Representation R P V)
    (C : Set (LeftQuotient P)) (hc : IsCompact C) (hcl : IsClopen C)
    (f : CompactFunctions P σ) :
    quotientSupport P (eval P σ (compactQuotientCutoff P σ C hc hcl f).val) =
      C ∩ quotientSupport P (eval P σ f.val) :=
  quotientSupport_smoothQuotientCutoff P σ C hc hcl.isOpen f.val

/-- Cutting off introduces no projected support outside C or the original support. -/
theorem quotientSupport_compactQuotientCutoff_subset (P : Subgroup G)
    (σ : Representation R P V) (C : Set (LeftQuotient P)) (hc : IsCompact C)
    (hcl : IsClopen C) (f : CompactFunctions P σ) :
    quotientSupport P (eval P σ (compactQuotientCutoff P σ C hc hcl f).val) ⊆ C ∧
    quotientSupport P (eval P σ (compactQuotientCutoff P σ C hc hcl f).val) ⊆
      quotientSupport P (eval P σ f.val) := by
  rw [quotientSupport_compactQuotientCutoff]
  exact ⟨inter_subset_left, inter_subset_right⟩

/-- One open subgroup fixes the whole cutoff under right translation. -/
theorem compactQuotientCutoff_uniform_stabilizer (P : Subgroup G)
    (σ : Representation R P V) (C : Set (LeftQuotient P)) (hc : IsCompact C)
    (hcl : IsClopen C) (f : CompactFunctions P σ) :
    ∃ K : OpenSubgroup G, ∀ (k : K) (x : G),
      eval P σ (compactQuotientCutoff P σ C hc hcl f).val (x * (k : G)) =
        eval P σ (compactQuotientCutoff P σ C hc hcl f).val x := by
  obtain ⟨K, hK⟩ := (compactQuotientCutoff P σ C hc hcl f).val.property
  exact ⟨K, fun k x => congrArg (fun F : EquivariantFunctions P σ => F.1 x) (hK k)⟩

end Cutoffs

end Langlands.Induction

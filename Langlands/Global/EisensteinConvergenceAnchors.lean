import Langlands.Representation.Families.FiniteHolomorphicSections
import Mathlib.Order.Filter.Bases.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Constructions

/-! # Common open convergence anchors for finite holomorphic families -/

noncomputable section

open Filter Set

set_option autoImplicit false

namespace Langlands.Global.EisensteinJet

section AnchorFilter

variable {E : Type*} [TopologicalSpace E]
  (C : ℝ → Set E) (hC : Antitone C)

/-- The parameter filter used for convergence-region identities. Its basic sets
are the intersections of sufficiently regular regions with open dense sets. -/
def convergenceAnchorFilter : Filter E :=
  FilterBasis.filter
    { sets := {S | ∃ R U, IsOpen U ∧ Dense U ∧ S = C R ∩ U}
      nonempty := ⟨C 0 ∩ univ, 0, univ, isOpen_univ, dense_univ, rfl⟩
      inter_sets := by
        rintro _ _ ⟨R, U, hUo, hUd, rfl⟩ ⟨S, V, hVo, hVd, rfl⟩
        refine ⟨C (max R S) ∩ (U ∩ V), ⟨max R S, U ∩ V, hUo.inter hVo,
          hUd.inter_of_isOpen_left hVd hUo, rfl⟩, ?_⟩
        intro x hx
        exact ⟨⟨hC (le_max_left _ _) hx.1, hx.2.1⟩, ⟨hC (le_max_right _ _) hx.1, hx.2.2⟩⟩ }

theorem eventually_convergenceAnchorFilter_iff {P : E → Prop} :
    (∀ᶠ t in convergenceAnchorFilter C hC, P t) ↔
      ∃ R U, IsOpen U ∧ Dense U ∧ ∀ t ∈ C R ∩ U, P t := by
  constructor
  · rintro ⟨_, ⟨R, U, hUo, hUd, rfl⟩, hsub⟩
    exact ⟨R, U, hUo, hUd, hsub⟩
  · rintro ⟨R, U, hUo, hUd, hsub⟩
    exact ⟨C R ∩ U, ⟨R, U, hUo, hUd, rfl⟩, hsub⟩

/-- Eventual identities on this filter hold on an actual nonempty open set
if every sufficiently regular region is open and nonempty. -/
theorem exists_open_of_eventually_convergenceAnchorFilter
    (hCo : ∀ R, IsOpen (C R)) (hCne : ∀ R, (C R).Nonempty)
    {P : E → Prop} (hP : ∀ᶠ t in convergenceAnchorFilter C hC, P t) :
    ∃ U : Set E, IsOpen U ∧ U.Nonempty ∧ ∀ t ∈ U, P t := by
  obtain ⟨R, U, hUo, hUd, h⟩ := (eventually_convergenceAnchorFilter_iff C hC).mp hP
  exact ⟨C R ∩ U, (hCo R).inter hUo, hUd.inter_open_nonempty _ (hCo R) (hCne R), h⟩

/-- Local open dense parameter sets for a property give one ambient open
dense set, by taking the interior of the full locus. -/
theorem exists_open_dense_of_local {P : E → Prop}
    (hP : ∀ t : E, ∃ U : TopologicalSpace.Opens E, t ∈ U ∧
      ∃ D : Set U, IsOpen D ∧ Dense D ∧ ∀ s ∈ D, P s.val) :
    ∃ D : Set E, IsOpen D ∧ Dense D ∧ ∀ t ∈ D, P t := by
  refine ⟨interior {t | P t}, isOpen_interior, fun t => ?_, fun _ ht => interior_subset ht⟩
  obtain ⟨U, ht, D, hDo, hDd, hDP⟩ := hP t
  have hUi : Subtype.val '' D ⊆ interior {s | P s} :=
    interior_maximal (by rintro _ ⟨s, hs, rfl⟩; exact hDP s hs)
      (U.isOpen.isOpenMap_subtype_val D hDo)
  exact closure_mono hUi (image_closure_subset_closure_image continuous_subtype_val
    ⟨⟨t, ht⟩, hDd ⟨t, ht⟩, rfl⟩)

end AnchorFilter

section OperatorPairs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (ℱ : Filter E) (P : E → Submodule ℂ V)

/-- Eventual inclusion of constant sections in submodules implies eventual inclusion
of all finite holomorphic section families. -/
theorem eventually_mem_of_finiteHolomorphicSections
    (hP : ∀ v, ∀ᶠ t in ℱ, v ∈ P t) {f : E → V}
    (hf : f ∈ finiteHolomorphicSections E V) :
    ∀ᶠ t in ℱ, f t ∈ P t := by
  obtain ⟨n, a, v, _, heq⟩ := FiniteHolomorphicSections.mem_iff.mp hf
  have hv : ∀ᶠ t in ℱ, ∀ i, v i ∈ P t := eventually_all.mpr (fun i => hP (v i))
  filter_upwards [hv] with t ht
  rw [heq t]
  exact Submodule.sum_mem _ fun i _ => (P t).smul_mem (a i t) (ht i)

variable (J : ∀ t, P t →ₗ[ℂ] W)

/-- Evaluate a section whenever it lies in the convergence domain, and give
it the value zero elsewhere. -/
def sectionOutput (t : E) (v : V) : W := by
  classical
  exact if h : v ∈ P t then J t ⟨v, h⟩ else 0

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem sectionOutput_of_mem {t : E} {v : V} (h : v ∈ P t) :
    sectionOutput P J t v = J t ⟨v, h⟩ := by simp [sectionOutput, h]

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
private theorem sectionOutput_zero (t : E) : sectionOutput P J t 0 = 0 := by
  rw [sectionOutput_of_mem P J (P t).zero_mem]
  exact (J t).map_zero

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
private theorem sectionOutput_add {t : E} {v w : V} (hv : v ∈ P t) (hw : w ∈ P t) :
    sectionOutput P J t (v + w) = sectionOutput P J t v + sectionOutput P J t w := by
  rw [sectionOutput_of_mem P J ((P t).add_mem hv hw),
    sectionOutput_of_mem P J hv, sectionOutput_of_mem P J hw]
  exact (J t).map_add ⟨v, hv⟩ ⟨w, hw⟩

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
private theorem sectionOutput_smul {t : E} {v : V} (hv : v ∈ P t) (z : ℂ) :
    sectionOutput P J t (z • v) = z • sectionOutput P J t v := by
  rw [sectionOutput_of_mem P J ((P t).smul_mem z hv), sectionOutput_of_mem P J hv]
  exact (J t).map_smul z ⟨v, hv⟩

/-- The pairs of a varying section operator and a fixed output operator
that preserve finite holomorphic sections and commute with evaluation
eventually on every such family. -/
def sectionCovarianceAlgebra (hP : ∀ v, ∀ᶠ t in ℱ, v ∈ P t) :
    Subalgebra ℂ ((E → Module.End ℂ V) × Module.End ℂ W) where
  carrier := {b | (∀ v, (fun t => b.1 t v) ∈ finiteHolomorphicSections E V) ∧
    ∀ f ∈ finiteHolomorphicSections E V,
      ∀ᶠ t in ℱ, b.2 (sectionOutput P J t (f t)) = sectionOutput P J t (b.1 t (f t))}
  zero_mem' := by
    refine ⟨fun v => ?_, fun f hf => .of_forall fun t => ?_⟩
    · simpa only [Prod.fst_zero, Pi.zero_apply, LinearMap.zero_apply] using
        FiniteHolomorphicSections.const_mem (E := E) (0 : V)
    · simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, LinearMap.zero_apply, sectionOutput_zero]
  one_mem' := by
    refine ⟨fun v => ?_, fun f hf => .of_forall fun t => ?_⟩
    · simpa only [Prod.fst_one, Pi.one_apply, Module.End.one_apply] using
        FiniteHolomorphicSections.const_mem (E := E) v
    · simp only [Prod.fst_one, Prod.snd_one, Pi.one_apply, Module.End.one_apply]
  add_mem' {a b} ha hb := by
    refine ⟨fun v => (finiteHolomorphicSections E V).add_mem (ha.1 v) (hb.1 v), fun f hf => ?_⟩
    have hva := eventually_mem_of_finiteHolomorphicSections ℱ P hP
      (FiniteHolomorphicSections.apply_mem a.1 ha.1 hf)
    have hvb := eventually_mem_of_finiteHolomorphicSections ℱ P hP
      (FiniteHolomorphicSections.apply_mem b.1 hb.1 hf)
    filter_upwards [ha.2 f hf, hb.2 f hf, hva, hvb] with t haₜ hbₜ hpa hpb
    change a.2 (sectionOutput P J t (f t)) + b.2 (sectionOutput P J t (f t)) =
      sectionOutput P J t (a.1 t (f t) + b.1 t (f t))
    rw [sectionOutput_add P J hpa hpb, haₜ, hbₜ]
  mul_mem' {a b} ha hb := by
    refine ⟨fun v => FiniteHolomorphicSections.apply_mem a.1 ha.1 (hb.1 v), fun f hf => ?_⟩
    have hbf := FiniteHolomorphicSections.apply_mem b.1 hb.1 hf
    filter_upwards [ha.2 _ hbf, hb.2 f hf] with t haₜ hbₜ
    change a.2 (b.2 (sectionOutput P J t (f t))) =
      sectionOutput P J t (a.1 t (b.1 t (f t)))
    rw [hbₜ]
    exact haₜ
  algebraMap_mem' z := by
    refine ⟨fun v => ?_, fun f hf => ?_⟩
    · change (fun _ : E => z • v) ∈ finiteHolomorphicSections E V
      exact FiniteHolomorphicSections.const_mem _
    · filter_upwards [eventually_mem_of_finiteHolomorphicSections ℱ P hP hf] with t ht
      change z • sectionOutput P J t (f t) = sectionOutput P J t (z • f t)
      exact (sectionOutput_smul P J ht z).symm

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
private theorem sectionOutput_sum_smul {t : E} {I : Type*} [Fintype I]
    (c : I → ℂ) (v : I → V) (hv : ∀ i, v i ∈ P t) :
    sectionOutput P J t (∑ i, c i • v i) = ∑ i, c i • sectionOutput P J t (v i) := by
  let w (i : I) : P t := ⟨v i, hv i⟩
  have h : (∑ i, c i • v i) ∈ P t :=
    (P t).sum_mem fun i _ => (P t).smul_mem (c i) (hv i)
  have heq : (⟨_, h⟩ : P t) = ∑ i, c i • w i := by
    apply Subtype.ext
    simp [w]
  rw [sectionOutput_of_mem P J h, heq, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, sectionOutput_of_mem P J (hv i)]

/-- For an operator preserving finite holomorphic expansions, eventual commutation
on constant sections implies eventual commutation on every such section family. -/
theorem mem_sectionCovarianceAlgebra_of_const
    (hP : ∀ v, ∀ᶠ t in ℱ, v ∈ P t)
    (b : (E → Module.End ℂ V) × Module.End ℂ W)
    (hhol : ∀ v, (fun t => b.1 t v) ∈ finiteHolomorphicSections E V)
    (hconst : ∀ v, ∀ᶠ t in ℱ, b.2 (sectionOutput P J t v) = sectionOutput P J t (b.1 t v)) :
    b ∈ sectionCovarianceAlgebra ℱ P J hP := by
  refine ⟨hhol, fun f hf => ?_⟩
  obtain ⟨m, c, v, _, heq⟩ := FiniteHolomorphicSections.mem_iff.mp hf
  have hV : ∀ᶠ t in ℱ, ∀ i, v i ∈ P t :=
    eventually_all.mpr fun i => hP (v i)
  have hB : ∀ᶠ t in ℱ, ∀ i, b.1 t (v i) ∈ P t :=
    eventually_all.mpr fun i => eventually_mem_of_finiteHolomorphicSections ℱ P hP (hhol (v i))
  have hEq : ∀ᶠ t in ℱ, ∀ i, b.2 (sectionOutput P J t (v i)) =
      sectionOutput P J t (b.1 t (v i)) :=
    eventually_all.mpr fun i => hconst (v i)
  filter_upwards [hV, hB, hEq] with t htV htB htEq
  rw [heq t, sectionOutput_sum_smul P J _ _ htV, map_sum, map_sum,
    show (∑ i, b.1 t (c i t • v i)) = ∑ i, c i t • b.1 t (v i) by simp only [map_smul],
    sectionOutput_sum_smul P J _ _ htB]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, htEq]

end OperatorPairs

end Langlands.Global.EisensteinJet

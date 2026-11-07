import Langlands.Representation.CuspidalSupport.NormalSubgroupHecke
import Langlands.Algebra.RankOneGradedAlgebra
import Langlands.Representation.Schur.CountableDimensionProof

/-!
# The grading of `End (ind_H^G ρ)` by a degree on `G`

Let `H` be an open normal subgroup of a topological group `G`, `ρ` an irreducible smooth
complex representation of `H` and `I = ind_H^G ρ`. A degree `p : G → ι` into an additive
commutative group, additive and with kernel exactly `H`, grades `End I`: the piece of degree
`a` consists of the endomorphisms `α` all of whose values `α(f_w)(g)` vanish unless
`p g = a` (Renard VI.4.3, with `ι` a copy of `G/H`). Each piece has rank at most one when `ρ`
has countable dimension (Schur's lemma), and every nonzero homogeneous element is a unit.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory DirectSum

namespace Langlands.CuspidalSupport.NormalHecke

universe uG uV

open Induction

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Subgroup G) (ρ : SmoothRep.{0, uG, uV} ℂ H) (hH : IsOpen (H : Set G))

section Linear

theorem endValue_add (α β : End (inducedRep H ρ)) (g : G) :
    endValue H ρ hH (α + β) g = endValue H ρ hH α g + endValue H ρ hH β g :=
  LinearMap.ext fun _ => rfl

theorem endValue_smul (c : ℂ) (α : End (inducedRep H ρ)) (g : G) :
    endValue H ρ hH (c • α) g = c • endValue H ρ hH α g :=
  LinearMap.ext fun _ => rfl

theorem endValue_zero (g : G) : endValue H ρ hH 0 g = 0 :=
  LinearMap.ext fun _ => rfl

/-- `α ↦ φ_α(g)`, as a linear map. -/
def endValueLinear (g : G) : End (inducedRep H ρ) →ₗ[ℂ] Module.End ℂ ρ where
  toFun α := endValue H ρ hH α g
  map_add' α β := endValue_add H ρ hH α β g
  map_smul' c α := endValue_smul H ρ hH c α g

theorem endValue_sum {κ : Type*} (s : Finset κ) (α : κ → End (inducedRep H ρ)) (g : G) :
    endValue H ρ hH (∑ i ∈ s, α i) g = ∑ i ∈ s, endValue H ρ hH (α i) g :=
  map_sum (endValueLinear H ρ hH g) α s

theorem endValue_one_one : endValue H ρ hH 1 1 = 1 :=
  LinearMap.ext fun w => eval_unitFunction_one H hH ρ.representation ρ.isSmooth w

theorem endValue_one_of_not_mem {g : G} (hg : g ∉ H) : endValue H ρ hH 1 g = 0 :=
  LinearMap.ext fun w => by
    change eval H ρ.representation (unitFunction H hH ρ.representation ρ.isSmooth w).1 g = 0
    rw [eval_unitFunction, dite_eq_right hg]

theorem endValue_conj (α : End (inducedRep H ρ)) (g₀ : G) (h k : H)
    (hk : (k : G) = g₀ * h * g₀⁻¹) (w : ρ) :
    endValue H ρ hH α g₀ (ρ.representation h w) =
      ρ.representation k (endValue H ρ hH α g₀ w) := by
  rw [← endValue_mul_right, ← endValue_mul_left]
  congr 1
  rw [hk]
  group

end Linear

section Twisted

variable [ρ.representation.IsIrreducible]

/-- A nonzero value `φ_α(g₀)` is bijective. -/
theorem bijective_endValue (α : End (inducedRep H ρ)) (g₀ : G) [hN : H.Normal]
    (h0 : endValue H ρ hH α g₀ ≠ 0) : Function.Bijective (endValue H ρ hH α g₀) := by
  let c : H → H := fun h => ⟨g₀ * h * g₀⁻¹, hN.conj_mem _ h.2 g₀⟩
  refine ⟨injective_of_twisted ρ.representation _ c
    (fun h w => endValue_conj H ρ hH α g₀ h (c h) rfl w) h0, fun v => ?_⟩
  obtain ⟨u₀, hu₀⟩ : ∃ u, endValue H ρ hH α g₀ u ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (LinearMap.ext hc)
  have hmem := mem_of_isIrreducible ρ.representation (LinearMap.range (endValue H ρ hH α g₀))
    (fun k v hv => ?_) (LinearMap.mem_range_self _ u₀) hu₀ v
  · exact LinearMap.mem_range.mp hmem
  · obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hv
    let k' : H := ⟨g₀⁻¹ * k * g₀, by simpa using hN.conj_mem _ k.2 g₀⁻¹⟩
    refine ⟨ρ.representation k' u, ?_⟩
    rw [endValue_conj H ρ hH α g₀ k' k (by simp only [k']; group)]

include hH in
/-- `End (ind_H^G ρ)` is nontrivial. -/
theorem nontrivial_end : Nontrivial (End (inducedRep H ρ)) := by
  obtain ⟨w, hw⟩ := exists_ne_zero_of_isIrreducible ρ.representation
  refine ⟨⟨1, 0, fun h => hw ?_⟩⟩
  have := congrArg (fun α => endValue H ρ hH α 1 w) h
  change endValue H ρ hH 1 1 w = endValue H ρ hH 0 1 w at this
  rwa [endValue_one_one, endValue_zero] at this

end Twisted

section Grading

variable {ι : Type*} [AddCommGroup ι]

/-- A degree `p : G → ι` for the subgroup `H`: an additive map whose kernel is exactly `H`. -/
structure IsDegree (p : G → ι) : Prop where
  map_mul : ∀ x y, p (x * y) = p x + p y
  eq_zero_iff : ∀ g, p g = 0 ↔ g ∈ H

variable {H} {p : G → ι}

namespace IsDegree

variable (hp : IsDegree H p)
include hp
omit [IsTopologicalGroup G] [TopologicalSpace G]

theorem map_one : p 1 = 0 := by
  have h := hp.map_mul 1 1
  rw [mul_one] at h
  exact left_eq_add.mp h

theorem map_inv (g : G) : p g⁻¹ = -p g := by
  have h := hp.map_mul g⁻¹ g
  rw [inv_mul_cancel, hp.map_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem map_mem {h : G} (hh : h ∈ H) : p h = 0 := (hp.eq_zero_iff h).mpr hh

theorem inv_mul_mem {g g₀ : G} (hg : p g = p g₀) : g₀⁻¹ * g ∈ H := by
  rw [← hp.eq_zero_iff, hp.map_mul, hp.map_inv, hg, neg_add_cancel]

theorem map_bi (h h' : H) (g : G) : p ((h : G) * g * h') = p g := by
  rw [hp.map_mul, hp.map_mul, hp.map_mem h.2, hp.map_mem h'.2, zero_add, add_zero]

end IsDegree

variable (H p)

/-- The piece of degree `a`: endomorphisms `α` all of whose values `α(f_w)(g)` vanish unless
`p g = a`. -/
def component (a : ι) : Submodule ℂ (End (inducedRep H ρ)) where
  carrier := {α | ∀ g, p g ≠ a → endValue H ρ hH α g = 0}
  add_mem' := by
    intro α β hα hβ g hg
    rw [endValue_add, hα g hg, hβ g hg, add_zero]
  zero_mem' := fun g _ => endValue_zero H ρ hH g
  smul_mem' := by
    intro c α hα g hg
    rw [endValue_smul, hα g hg, smul_zero]

omit [AddCommGroup ι] in
theorem mem_component_iff (a : ι) (α : End (inducedRep H ρ)) :
    α ∈ component H ρ hH p a ↔ ∀ g, p g ≠ a → endValue H ρ hH α g = 0 :=
  Iff.rfl

variable {H ρ p}
variable (hp : IsDegree H p)
include hp

theorem one_mem_component : (1 : End (inducedRep H ρ)) ∈ component H ρ hH p 0 :=
  fun _ hg => endValue_one_of_not_mem H ρ hH fun hmem => hg (hp.map_mem hmem)

/-- Two elements of the same piece agreeing at one point `g₀` of degree `a` are equal. -/
theorem eq_of_mem_component {a : ι} {α β : End (inducedRep H ρ)}
    (hα : α ∈ component H ρ hH p a) (hβ : β ∈ component H ρ hH p a) {g₀ : G} (hg₀ : p g₀ = a)
    (h : endValue H ρ hH α g₀ = endValue H ρ hH β g₀) : α = β := by
  refine end_ext H ρ hH fun g w => ?_
  by_cases hg : p g = a
  · have hk := hp.inv_mul_mem (hg.trans hg₀.symm)
    have hgk : g = g₀ * ((⟨g₀⁻¹ * g, hk⟩ : H) : G) := by simp
    rw [hgk, endValue_mul_right, endValue_mul_right, h]
  · rw [hα g hg, hβ g hg]

variable [hN : H.Normal] [ρ.representation.IsIrreducible]

theorem mul_mem_component {a b : ι} {α β : End (inducedRep H ρ)}
    (hα : α ∈ component H ρ hH p a) (hβ : β ∈ component H ρ hH p b) :
    α * β ∈ component H ρ hH p (a + b) := by
  intro x hx
  have e := congrFun (heckeEquiv_mul H ρ hH α β) x
  change endValue H ρ hH (α * β) x =
    ∑ᶠ q : G ⧸ H, endValue H ρ hH α q.out * endValue H ρ hH β (q.out⁻¹ * x) at e
  rw [e]
  refine finsum_eq_zero_of_forall_eq_zero fun q => ?_
  by_cases hq : p q.out = a
  · have hb : p (q.out⁻¹ * x) ≠ b := by
      intro hb
      apply hx
      rw [← hb, hp.map_mul, hp.map_inv, hq, add_neg_cancel_left]
    rw [hβ _ hb, mul_zero]
  · rw [hα _ hq, zero_mul]

/-- The values of `α` on the points of degree `a`, extended by zero. -/
theorem projFunction_mem [DecidableEq ι] (a : ι) (α : End (inducedRep H ρ)) :
    (fun g => if p g = a then endValue H ρ hH α g else 0) ∈ heckeSubmodule H ρ := by
  refine ⟨fun h h' g => ?_, ?_⟩
  · simp only [hp.map_bi]
    split_ifs
    · exact endValue_bi H ρ hH α h h' g
    · rw [mul_zero, zero_mul]
  · refine (endValue_finite H ρ hH α).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x, fun h0 => hx ?_, rfl⟩
    change (if p x = a then endValue H ρ hH α x else 0) = 0
    rw [h0, ite_self]

/-- The component of `α` of degree `a`. -/
def proj [DecidableEq ι] (a : ι) (α : End (inducedRep H ρ)) : End (inducedRep H ρ) :=
  endOfHecke H ρ hH ⟨_, projFunction_mem hH hp a α⟩

theorem endValue_proj [DecidableEq ι] (a : ι) (α : End (inducedRep H ρ)) (g : G) :
    endValue H ρ hH (proj hH hp a α) g = if p g = a then endValue H ρ hH α g else 0 :=
  LinearMap.ext fun w => endValue_endOfHecke H ρ hH _ g w

theorem proj_mem [DecidableEq ι] (a : ι) (α : End (inducedRep H ρ)) : proj hH hp a α ∈ component H ρ hH p a :=
  fun g hg => by rw [endValue_proj, ite_eq_right hg]

/-- The finitely many degrees of points where `φ_α` does not vanish. -/
theorem exists_finset_degrees (α : End (inducedRep H ρ)) :
    ∃ s : Finset ι, ∀ g, endValue H ρ hH α g ≠ 0 → p g ∈ s := by
  refine ⟨((endValue_finite H ρ hH α).image fun q : G ⧸ H => p q.out).toFinset, fun g hg => ?_⟩
  rw [Set.Finite.mem_toFinset]
  refine ⟨(g : G ⧸ H), ⟨g, hg, rfl⟩, ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  change p (Quotient.out (g : G ⧸ H)) = p g
  rw [hh, hp.map_mul, hp.map_mem h.2, add_zero]

theorem sum_proj [DecidableEq ι] (α : End (inducedRep H ρ)) {s : Finset ι}
    (hs : ∀ g, endValue H ρ hH α g ≠ 0 → p g ∈ s) : ∑ a ∈ s, proj hH hp a α = α := by
  refine end_ext H ρ hH fun g w => ?_
  rw [endValue_sum]
  simp only [endValue_proj]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_cases h0 : endValue H ρ hH α g = 0
    · rw [h0]
    · exact absurd (hs g h0) h

omit [AddCommGroup ι] hp hN [ρ.representation.IsIrreducible] in
variable (ρ) in
theorem iSupIndep_component : iSupIndep (component H ρ hH p) := by
  rw [iSupIndep_def]
  intro a
  let N : Submodule ℂ (End (inducedRep H ρ)) :=
    { carrier := {α | ∀ g, p g = a → endValue H ρ hH α g = 0}
      add_mem' := by
        intro α β hα hβ g hg
        rw [endValue_add, hα g hg, hβ g hg, add_zero]
      zero_mem' := fun g _ => endValue_zero H ρ hH g
      smul_mem' := by
        intro c α hα g hg
        rw [endValue_smul, hα g hg, smul_zero] }
  have hle : ⨆ (b) (_ : b ≠ a), component H ρ hH p b ≤ N :=
    iSup₂_le fun b hb α hα g hg => hα g (hg ▸ fun h => hb h.symm)
  refine Disjoint.mono_right hle ?_
  rw [Submodule.disjoint_def]
  intro α hα hN'
  refine end_ext H ρ hH fun g w => ?_
  rw [endValue_zero]
  by_cases hg : p g = a
  · rw [(hN' : ∀ g, p g = a → endValue H ρ hH α g = 0) g hg]
  · rw [hα g hg]

variable (ρ) in
theorem iSup_component : ⨆ a, component H ρ hH p a = ⊤ := by
  classical
  refine eq_top_iff.mpr fun α _ => ?_
  obtain ⟨s, hs⟩ := exists_finset_degrees hH hp α
  rw [← sum_proj hH hp α hs]
  exact Submodule.sum_mem _ fun a _ =>
    Submodule.mem_iSup_of_mem a (proj_mem hH hp a α)

variable (ρ) in
theorem isInternal_component [DecidableEq ι] : DirectSum.IsInternal (component H ρ hH p) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨iSupIndep_component ρ hH, iSup_component ρ hH hp⟩

variable (ρ) in
/-- The grading of `End (ind_H^G ρ)` by the degree `p`. -/
abbrev gradedAlgebra [DecidableEq ι] : GradedAlgebra (component H ρ hH p) where
  toDecomposition := (isInternal_component ρ hH hp).chooseDecomposition
  one_mem := one_mem_component hH hp
  mul_mem := fun _ _ _ _ hα hβ => mul_mem_component hH hp hα hβ

/-- The homogeneous component of degree `a` of `α` has the values of `α` at the points of
degree `a`, and vanishes elsewhere. -/
theorem endValue_decompose [DecidableEq ι] (α : End (inducedRep H ρ)) (a : ι) (g : G) :
    letI := gradedAlgebra ρ hH hp
    endValue H ρ hH (decompose (component H ρ hH p) α a) g =
      if p g = a then endValue H ρ hH α g else 0 := by
  let _ := gradedAlgebra ρ hH hp
  classical
  split_ifs with hg
  · conv_rhs => rw [← sum_support_decompose (component H ρ hH p) α]
    rw [endValue_sum, Finset.sum_eq_single a]
    · intro b _ hb
      exact (decompose (component H ρ hH p) α b).2 g (hg.trans_ne hb.symm)
    · intro ha
      rw [DFinsupp.notMem_support_iff.mp ha, ZeroMemClass.coe_zero, endValue_zero]
  · exact (decompose (component H ρ hH p) α a).2 g hg

omit [IsTopologicalGroup G] hp [ρ.representation.IsIrreducible] in
open Classical in
/-- The inverse of a nonzero homogeneous element of degree `a`: the function supported on
`H g₀⁻¹` with value `ρ(x g₀) T` at `x`, where `T` inverts `φ_α(g₀)`. -/
theorem inverseFunction_mem (g₀ : G) (T : Module.End ℂ ρ)
    (hT : ∀ h k : H, (k : G) = g₀⁻¹ * h * g₀ →
      ρ.representation k * T = T * ρ.representation h) :
    (fun x => if hx : x * g₀ ∈ H then ρ.representation ⟨x * g₀, hx⟩ * T else 0) ∈
      heckeSubmodule H ρ := by
  refine ⟨fun h h' g => ?_, ?_⟩
  · by_cases hx : g * g₀ ∈ H
    · let k : H := ⟨g₀⁻¹ * h' * g₀, by simpa using hN.conj_mem _ h'.2 g₀⁻¹⟩
      have hx' : (h : G) * g * h' * g₀ ∈ H := by
        have : (h : G) * g * h' * g₀ = h * (g * g₀) * k := by simp [k, mul_assoc]
        rw [this]
        exact H.mul_mem (H.mul_mem h.2 hx) k.2
      simp only [hx, hx', dite_true]
      have e : (⟨(h : G) * g * h' * g₀, hx'⟩ : H) = h * ⟨g * g₀, hx⟩ * k :=
        Subtype.ext (by simp [k, mul_assoc])
      rw [e, map_mul, map_mul, mul_assoc, mul_assoc, hT h' k rfl]
      simp only [mul_assoc]
    · have hx' : (h : G) * g * h' * g₀ ∉ H := by
        intro hmem
        apply hx
        have : g * g₀ = (h : G)⁻¹ * ((h : G) * g * h' * g₀) * (g₀⁻¹ * (h' : G)⁻¹ * g₀) := by
          group
        rw [this]
        exact H.mul_mem (H.mul_mem (H.inv_mem h.2) hmem)
          (by simpa using hN.conj_mem _ (H.inv_mem h'.2) g₀⁻¹)
      simp only [hx, hx', dite_false, mul_zero, zero_mul]
  · refine (Set.finite_singleton ((g₀⁻¹ : G) : G ⧸ H)).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    have hxg : x * g₀ ∈ H := by
      by_contra hc
      exact hx (dite_eq_right hc)
    rw [Set.mem_singleton_iff, QuotientGroup.eq]
    have : x⁻¹ * g₀⁻¹ = g₀ * (x * g₀)⁻¹ * g₀⁻¹ := by group
    rw [this]
    exact hN.conj_mem _ (H.inv_mem hxg) g₀

/-- A nonzero homogeneous element of degree `a` has a right inverse of degree `-a`. -/
theorem exists_mul_eq_one {a : ι} {α : End (inducedRep H ρ)}
    (hα : α ∈ component H ρ hH p a) (h0 : α ≠ 0) :
    ∃ β ∈ component H ρ hH p (-a), α * β = 1 := by
  classical
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, endValue H ρ hH α g₀ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (end_ext H ρ hH fun g w => by rw [hc g, endValue_zero])
  have hpg₀ : p g₀ = a := by
    by_contra hc
    exact hg₀ (hα g₀ hc)
  let e := LinearEquiv.ofBijective _ (bijective_endValue H ρ hH α g₀ hg₀)
  let T : Module.End ℂ ρ := e.symm.toLinearMap
  have hT0 : endValue H ρ hH α g₀ * T = 1 :=
    LinearMap.ext fun v => e.apply_symm_apply v
  have hT : ∀ h k : H, (k : G) = g₀⁻¹ * h * g₀ →
      ρ.representation k * T = T * ρ.representation h := by
    intro h k hk
    refine LinearMap.ext fun v => e.injective ?_
    change endValue H ρ hH α g₀ (ρ.representation k (T v)) =
      endValue H ρ hH α g₀ (T (ρ.representation h v))
    rw [endValue_conj H ρ hH α g₀ k h (by rw [hk]; group)]
    change ρ.representation h (e (e.symm v)) = e (e.symm (ρ.representation h v))
    rw [e.apply_symm_apply, e.apply_symm_apply]
  let β := endOfHecke H ρ hH ⟨_, inverseFunction_mem g₀ T hT⟩
  have hβ : ∀ x, endValue H ρ hH β x =
      if hx : x * g₀ ∈ H then ρ.representation ⟨x * g₀, hx⟩ * T else 0 :=
    fun x => LinearMap.ext fun w => endValue_endOfHecke H ρ hH _ x w
  have hβmem : β ∈ component H ρ hH p (-a) := by
    intro x hx
    rw [hβ, dite_eq_right]
    intro hmem
    apply hx
    have h1 := hp.map_mem hmem
    rw [hp.map_mul, hpg₀] at h1
    exact eq_neg_of_add_eq_zero_left h1
  refine ⟨β, hβmem, ?_⟩
  have hmul := mul_mem_component hH hp hα hβmem
  rw [add_neg_cancel] at hmul
  refine eq_of_mem_component hH hp hmul (one_mem_component hH hp) hp.map_one ?_
  rw [endValue_one_one]
  have e1 := congrFun (heckeEquiv_mul H ρ hH α β) 1
  change endValue H ρ hH (α * β) 1 =
    ∑ᶠ q : G ⧸ H, endValue H ρ hH α q.out * endValue H ρ hH β (q.out⁻¹ * 1) at e1
  rw [e1, finsum_eq_single _ (g₀ : G ⧸ H)]
  · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul H g₀
    have hmem : (Quotient.out (g₀ : G ⧸ H))⁻¹ * 1 * g₀ ∈ H := by
      rw [hk]
      simp
    change endValue H ρ hH α (Quotient.out (g₀ : G ⧸ H)) *
      endValue H ρ hH β ((Quotient.out (g₀ : G ⧸ H))⁻¹ * 1) = 1
    rw [hβ, dite_eq_left hmem, ← mul_assoc]
    have e2 : endValue H ρ hH α (Quotient.out (g₀ : G ⧸ H)) *
        ρ.representation ⟨_, hmem⟩ = endValue H ρ hH α g₀ := by
      rw [← endValue_mul_right']
      congr 1
      change Quotient.out (g₀ : G ⧸ H) * ((Quotient.out (g₀ : G ⧸ H))⁻¹ * 1 * g₀) = g₀
      group
    rw [e2, hT0]
  · intro q hq
    have hq' : p q.out ≠ a := by
      intro h
      apply hq
      rw [← QuotientGroup.out_eq' q, QuotientGroup.eq]
      exact hp.inv_mul_mem (hpg₀.trans h.symm)
    rw [hα _ hq', zero_mul]

/-- Every nonzero homogeneous element is a unit. -/
theorem isUnit_of_mem_component {a : ι} {α : End (inducedRep H ρ)}
    (hα : α ∈ component H ρ hH p a) (h0 : α ≠ 0) : IsUnit α := by
  obtain ⟨β, hβ, hαβ⟩ := exists_mul_eq_one hH hp hα h0
  have hβ0 : β ≠ 0 := by
    rintro rfl
    apply h0
    rw [← mul_one α, ← hαβ, mul_zero, mul_zero]
  obtain ⟨γ, -, hβγ⟩ := exists_mul_eq_one hH hp hβ hβ0
  have hγ : γ = α := by
    calc γ = α * β * γ := by rw [hαβ, one_mul]
      _ = α := by rw [mul_assoc, hβγ, mul_one]
  exact ⟨⟨α, β, hαβ, hγ ▸ hβγ⟩, rfl⟩

variable (ρ) in
/-- Schur's lemma: two elements of a piece are proportional, for `ρ` of countable
dimension. -/
theorem rank_component_le_one (hrank : Module.rank ℂ ρ ≤ Cardinal.aleph0) (a : ι) :
    Module.rank ℂ (component H ρ hH p a) ≤ 1 := by
  rw [rank_submodule_le_one_iff']
  by_cases hex : ∃ α ∈ component H ρ hH p a, α ≠ 0
  · obtain ⟨α₀, hα₀, hne⟩ := hex
    refine ⟨α₀, fun β hβ => ?_⟩
    obtain ⟨g₀, hg₀⟩ : ∃ g₀, endValue H ρ hH α₀ g₀ ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hne (end_ext H ρ hH fun g w => by rw [hc g, endValue_zero])
    have hpg₀ : p g₀ = a := by
      by_contra hc
      exact hg₀ (hα₀ g₀ hc)
    let e := LinearEquiv.ofBijective _ (bijective_endValue H ρ hH α₀ g₀ hg₀)
    let S : ρ.representation.IntertwiningMap ρ.representation :=
      { toLinearMap := e.symm.toLinearMap ∘ₗ endValue H ρ hH β g₀
        isIntertwining' := fun h => by
          refine LinearMap.ext fun v => e.injective ?_
          let k : H := ⟨g₀ * h * g₀⁻¹, hN.conj_mem _ h.2 g₀⟩
          change e (e.symm (endValue H ρ hH β g₀ (ρ.representation h v))) =
            endValue H ρ hH α₀ g₀ (ρ.representation h (e.symm (endValue H ρ hH β g₀ v)))
          rw [endValue_conj H ρ hH β g₀ h k rfl, endValue_conj H ρ hH α₀ g₀ h k rfl,
            e.apply_symm_apply]
          change _ = ρ.representation k (e (e.symm _))
          rw [e.apply_symm_apply] }
    obtain ⟨c, hc, -⟩ := countableDimensionalSchur ρ.representation hrank inferInstance S
    have hval : endValue H ρ hH β g₀ = endValue H ρ hH (c • α₀) g₀ := by
      rw [endValue_smul]
      refine LinearMap.ext fun v => ?_
      have h1 := congrArg (fun φ : ρ.representation.IntertwiningMap ρ.representation => φ v) hc
      simp only [Representation.IntertwiningMap.smul_apply] at h1
      change e.symm (endValue H ρ hH β g₀ v) = _ at h1
      rw [LinearMap.smul_apply, ← e.apply_symm_apply (endValue H ρ hH β g₀ v), h1]
      change e (c • v) = c • e v
      rw [map_smul]
    rw [Submodule.mem_span_singleton]
    exact ⟨c, (eq_of_mem_component hH hp hβ (Submodule.smul_mem _ c hα₀) hpg₀ hval).symm⟩
  · push Not at hex
    refine ⟨0, fun β hβ => ?_⟩
    rw [hex β hβ]
    exact Submodule.zero_mem _

variable (ρ) in
/-- `End (ind_H^G ρ)` graded by `p` is a rank-one grading. -/
theorem isRankOneGrading [DecidableEq ι] (hrank : Module.rank ℂ ρ ≤ Cardinal.aleph0) :
    letI := gradedAlgebra ρ hH hp
    RankOneGraded.IsRankOneGrading (component H ρ hH p) := by
  let _ := gradedAlgebra ρ hH hp
  exact ⟨rank_component_le_one ρ hH hp hrank, fun _ _ hα h0 => isUnit_of_mem_component hH hp hα h0⟩

end Grading

end Langlands.CuspidalSupport.NormalHecke

import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Group

/-! # Decomposing right cosets over an intermediate subgroup -/

noncomputable section

namespace Langlands.Global.ArthurTruncation

open QuotientGroup

variable {Γ : Type*} [Group Γ] {H K : Subgroup Γ}

private theorem mk_rightCoset_subgroup_mul (k : Γ) (hk : k ∈ K) (g : Γ) :
    (Quotient.mk (rightRel K) (k * g)) = Quotient.mk (rightRel K) g := by
  apply Quotient.sound
  apply rightRel_apply.mpr
  rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
  exact K.inv_mem hk

/-- A choice of representatives for the outer right cosets identifies the right
cosets of the smaller subgroup with pairs of outer and relative right cosets. -/
def rightCosetTower (h : H ≤ K) :
    Quotient (rightRel K) × Quotient (rightRel (H.subgroupOf K)) ≃ Quotient (rightRel H) := by
  let f (p : Quotient (rightRel K) × Quotient (rightRel (H.subgroupOf K))) : Quotient (rightRel H) :=
    Quotient.mk _ ((Quotient.out p.2 : K).val * Quotient.out p.1)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro ⟨c, d⟩ ⟨c', d'⟩ he
    have hr : ((Quotient.out d' : K).val * Quotient.out c') *
        ((Quotient.out d : K).val * Quotient.out c)⁻¹ ∈ H :=
      rightRel_apply.mp (Quotient.exact he)
    have houter : (Quotient.mk (rightRel K) ((Quotient.out d : K).val * Quotient.out c)) =
        Quotient.mk (rightRel K) ((Quotient.out d' : K).val * Quotient.out c') :=
      Quotient.sound (rightRel_apply.mpr (h hr))
    rw [mk_rightCoset_subgroup_mul _ (Quotient.out d).property,
      mk_rightCoset_subgroup_mul _ (Quotient.out d').property,
      Quotient.out_eq, Quotient.out_eq] at houter
    subst c'
    have hrel : Quotient.out d' * (Quotient.out d)⁻¹ ∈ H.subgroupOf K := by
      change (Quotient.out d' : K).val * (Quotient.out d : K).val⁻¹ ∈ H
      convert hr using 1
      group
    have hdd : Quotient.mk _ (Quotient.out d) = Quotient.mk _ (Quotient.out d') :=
      Quotient.sound (rightRel_apply.mpr hrel)
    rw [Quotient.out_eq, Quotient.out_eq] at hdd
    rw [hdd]
  · intro q
    let c := Quotient.mk (rightRel K) (Quotient.out q)
    have hc : Quotient.mk (rightRel K) (Quotient.out c) =
        Quotient.mk (rightRel K) (Quotient.out q) := Quotient.out_eq c
    have hk : Quotient.out q * (Quotient.out c)⁻¹ ∈ K :=
      rightRel_apply.mp (Quotient.exact hc)
    let k : K := ⟨Quotient.out q * (Quotient.out c)⁻¹, hk⟩
    let d := Quotient.mk (rightRel (H.subgroupOf K)) k
    have hkd' : Quotient.out d * k⁻¹ ∈ H.subgroupOf K :=
      rightRel_apply.mp (Quotient.exact (Quotient.out_eq d).symm)
    have hkd : (Quotient.out d : K).val * k.val⁻¹ ∈ H := hkd'
    have hrel : Quotient.out q * ((Quotient.out d : K).val * Quotient.out c)⁻¹ ∈ H := by
      have heq : Quotient.out q * ((Quotient.out d : K).val * Quotient.out c)⁻¹ =
          ((Quotient.out d : K).val * k.val⁻¹)⁻¹ := by
        dsimp only [k]
        group
      rw [heq]
      exact H.inv_mem hkd
    refine ⟨(c, d), (Quotient.sound (rightRel_apply.mpr hrel)).trans (Quotient.out_eq q)⟩

@[simp] theorem rightCosetTower_apply (h : H ≤ K) (c : Quotient (rightRel K))
    (d : Quotient (rightRel (H.subgroupOf K))) :
    rightCosetTower h (c, d) = Quotient.mk _ ((Quotient.out d : K).val * Quotient.out c) := rfl

/-- For a function on the smaller right cosets, a finitely supported sum indexed
by the two stages equals the sum over the smaller right cosets. -/
theorem finiteSupport_tsum_rightCosetTower {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [T3Space E]
    [ContinuousAdd E] (h : H ≤ K) (f : Quotient (rightRel H) → E)
    (S : Set (Quotient (rightRel K))) (hS : S.Finite)
    (hzero : ∀ c ∉ S, ∀ d, f (rightCosetTower h (c, d)) = 0)
    (hf : ∀ c, (Function.support (fun d => f (rightCosetTower h (c, d)))).Finite) :
    (Function.support f).Finite ∧
      (∑' c : Quotient (rightRel H), f c) = ∑' c, ∑' d, f (rightCosetTower h (c, d)) := by
  let F (p : Quotient (rightRel K) × Quotient (rightRel (H.subgroupOf K))) := f (rightCosetTower h p)
  have hfin : (Function.support F).Finite := by
    refine (hS.biUnion (fun c _ => (hf c).image (fun d => (c, d)))).subset ?_
    rintro ⟨c, d⟩ hp
    have hc : c ∈ S := Classical.byContradiction (fun hc => hp (hzero c hc d))
    exact Set.mem_iUnion₂.mpr ⟨c, hc, d, hp, rfl⟩
  refine ⟨(hfin.image (rightCosetTower h)).subset ?_, ?_⟩
  · intro q hq
    exact ⟨(rightCosetTower h).symm q, by simpa [F] using hq, Equiv.apply_symm_apply _ _⟩
  calc
    _ = ∑' p, F p := ((rightCosetTower h).tsum_eq f).symm
    _ = _ := (summable_of_hasFiniteSupport hfin).tsum_prod'
      (fun c => summable_of_hasFiniteSupport (hf c))

section Partition

universe u v

local notation "Cosets" S => Quotient (rightRel S)

/-- Finite partitions of unity on relative right cosets regroup an outer sum
as a sum on the smaller coset spaces. -/
def RightCosetPartitionRegroupingStatement : Prop :=
  ∀ (ι : Type u) [DecidableEq ι] (Γ : Type v) [Group Γ] (Δ : Finset ι)
    (P : Finset ι → Subgroup Γ) (a : Finset ι → Γ → ℂ) (b : Finset ι → Finset ι → Γ → ℂ),
    (∀ R S : Finset ι, R ⊆ S → S ⊆ Δ → P R ≤ P S) →
    (∀ S ⊆ Δ, ∀ p ∈ P S, ∀ g, a S (p * g) = a S g) →
    (∀ S ⊆ Δ, ∀ R ⊆ S, ∀ p ∈ P R, ∀ g, b R S (p * g) = b R S g) →
    (∀ S ⊆ Δ, (Function.support (fun c : Cosets (P S) => a S (Quotient.out c))).Finite) →
    (∀ S ⊆ Δ, ∀ c : Cosets (P S),
      (∀ R ⊆ S, (Function.support (fun d : Cosets ((P R).subgroupOf (P S)) =>
        b R S ((Quotient.out d : P S).val * Quotient.out c))).Finite) ∧
      ∑ R ∈ S.powerset, ∑' d : Cosets ((P R).subgroupOf (P S)),
        b R S ((Quotient.out d : P S).val * Quotient.out c) = 1) →
    (∀ S ⊆ Δ, ∀ R ⊆ S, (Function.support (fun c : Cosets (P R) =>
      a S (Quotient.out c) * b R S (Quotient.out c))).Finite) ∧
    (∑ S ∈ Δ.powerset, ∑' c : Cosets (P S), a S (Quotient.out c)) =
      ∑ R ∈ Δ.powerset, ∑ S ∈ Δ.powerset.filter (R ⊆ ·), ∑' c : Cosets (P R),
        a S (Quotient.out c) * b R S (Quotient.out c)

/-- Apply the tower equivalence after inserting the partition and use finite
support to commute the parabolic and coset sums. -/
theorem rightCosetPartitionRegrouping : RightCosetPartitionRegroupingStatement.{u,v} := by
  classical
  intro ι _ Γ _ Δ P a b hmono ha hb hfa hp
  let term (R S : Finset ι) (c : Cosets (P R)) :=
    a S (Quotient.out c) * b R S (Quotient.out c)
  let inner (R S : Finset ι) (c : Cosets (P S)) :=
    ∑' d : Cosets ((P R).subgroupOf (P S)),
      a S (Quotient.out c) * b R S ((Quotient.out d : P S).val * Quotient.out c)
  have htower (S : Finset ι) (hS : S ⊆ Δ) (R : Finset ι) (hR : R ⊆ S) :
      (Function.support (term R S)).Finite ∧
        (∑' c, term R S c) = ∑' c, inner R S c := by
    let h := hmono R S hR hS
    have hval (c : Cosets (P S)) (d : Cosets ((P R).subgroupOf (P S))) :
        term R S (rightCosetTower h (c, d)) =
          a S (Quotient.out c) * b R S ((Quotient.out d : P S).val * Quotient.out c) := by
      let g := (Quotient.out d : P S).val * Quotient.out c
      let g' := Quotient.out (rightCosetTower h (c, d))
      have he : Quotient.mk (rightRel (P R)) g = Quotient.mk (rightRel (P R)) g' := by
        change rightCosetTower h (c, d) = _
        exact (Quotient.out_eq (rightCosetTower h (c, d))).symm
      have he' : g' * g⁻¹ ∈ P R := rightRel_apply.mp (Quotient.exact he)
      have hg : (g' * g⁻¹) * g = g' := inv_mul_cancel_right _ _
      have ha' := ha S hS _ (h he') g
      have hb' := hb S hS R hR _ he' g
      rw [hg] at ha' hb'
      change a S g' * b R S g' = _
      rw [ha', hb']
      exact congrArg (· * b R S g) (ha S hS _ (Quotient.out d).property _)
    have hh := finiteSupport_tsum_rightCosetTower h (term R S)
      (Function.support (fun c : Cosets (P S) => a S (Quotient.out c))) (hfa S hS)
      (fun c hc d => by
        have hzero : a S (Quotient.out c) = 0 := not_not.mp hc
        rw [hval, hzero, zero_mul])
      (fun c => ((hp S hS c).1 R hR).subset (fun d hd => by
        intro hzero
        change b R S ((Quotient.out d : P S).val * Quotient.out c) = 0 at hzero
        apply hd
        change term R S (rightCosetTower h (c, d)) = 0
        rw [hval, hzero, mul_zero]))
    exact ⟨hh.1, hh.2.trans (tsum_congr fun c => tsum_congr (hval c))⟩
  refine ⟨fun S hS R hR => (htower S hS R hR).1, ?_⟩
  calc
    _ = ∑ S ∈ Δ.powerset, ∑ R ∈ S.powerset, ∑' c, inner R S c := by
      refine Finset.sum_congr rfl fun S hS => ?_
      have hS' := Finset.mem_powerset.mp hS
      have hsum (R : Finset ι) : Summable (inner R S) := by
        apply summable_of_hasFiniteSupport
        refine (hfa S hS').subset fun c hc => ?_
        intro hzero
        exact hc (by simp [inner, hzero])
      rw [← Summable.tsum_finsetSum fun R _ => hsum R]
      apply tsum_congr
      intro c
      simp only [inner, tsum_mul_left, ← Finset.mul_sum, (hp S hS' c).2, mul_one]
    _ = ∑ S ∈ Δ.powerset, ∑ R ∈ S.powerset, ∑' c, term R S c := by
      refine Finset.sum_congr rfl fun S hS => Finset.sum_congr rfl fun R hR => ?_
      exact (htower S (Finset.mem_powerset.mp hS) R (Finset.mem_powerset.mp hR)).2.symm
    _ = _ := by
      refine Finset.sum_comm' fun S R => ?_
      simp only [Finset.mem_powerset, Finset.mem_filter]
      exact ⟨fun ⟨hS, hR⟩ => ⟨⟨hS, hR⟩, hR.trans hS⟩, fun ⟨⟨hS, hR⟩, _⟩ => ⟨hS, hR⟩⟩

end Partition

end Langlands.Global.ArthurTruncation

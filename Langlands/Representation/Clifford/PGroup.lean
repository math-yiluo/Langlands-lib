import Langlands.Representation.Clifford.Orbit
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Irreducible representations of finite `p`-groups have `p`-power dimension
-/

noncomputable section

namespace Langlands.Clifford

open Representation FiniteRepresentation

universe uG uW

section Discrete

variable {Q : Type uG} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]

/-- A discrete group is nonarchimedean. -/
theorem nonarchimedeanGroup_of_discrete : NonarchimedeanGroup Q := by
  have : IsTopologicalGroup Q := inferInstance
  refine { is_nonarchimedean := fun U hU => ?_ }
  refine ⟨⟨⊥, isOpen_discrete _⟩, ?_⟩
  intro x hx
  have hx1 : x = 1 := Subgroup.mem_bot.mp hx
  rw [hx1]
  exact mem_of_mem_nhds hU

end Discrete

/-- Every irreducible finite-dimensional complex representation of a finite `p`-group has
dimension a power of `p`. -/
theorem exists_finrank_eq_pow_of_isPGroup {p : ℕ} [hp : Fact p.Prime] :
    ∀ (n : ℕ) (Q : Type uG) [Group Q] [Finite Q], Nat.card Q = p ^ n →
      ∀ (V : Type uW) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
        (ρ : Representation ℂ Q V), ρ.IsIrreducible → ∃ a : ℕ, Module.finrank ℂ V = p ^ a := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q _ _ hQ V _ _ _ ρ hρ
    rcases n with _ | n
    · -- the trivial group
      have : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp (by simpa using hQ)).1
      have : IsMulCommutative Q := ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
      exact ⟨0, by
        rw [pow_zero]
        exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative (ρ := ρ)⟩
    · have hpQ : IsPGroup p Q := IsPGroup.of_card hQ
      obtain ⟨N, hN⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card hp.out hpQ
        (n := n) (by rw [hQ]; exact Nat.pow_le_pow_right hp.out.pos (Nat.le_succ n))
      have hindex : N.index = p := by
        have h1 := N.card_mul_index
        rw [hN, hQ, pow_succ] at h1
        exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos n) h1
      have hNn : N.Normal := by
        apply Subgroup.normal_of_index_eq_minFac_card
        rw [hindex, hQ, Nat.Prime.pow_minFac hp.out (Nat.succ_ne_zero n)]
      let _ : TopologicalSpace Q := ⊥
      have : DiscreteTopology Q := ⟨rfl⟩
      have : NonarchimedeanGroup Q := nonarchimedeanGroup_of_discrete
      have hcardQN : Nat.card (Q ⧸ N) = p := by rw [← Subgroup.index_eq_card, hindex]
      have hcyc' : IsCyclic (Q ⧸ N) := isCyclic_of_prime_card hcardQN
      obtain ⟨g₀, hg₀⟩ := hcyc'.exists_generator
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g₀
      have hgen : ∀ x : Q, ∃ i : ℤ, x * (g ^ i)⁻¹ ∈ N := by
        intro x
        obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ (QuotientGroup.mk x))
        refine ⟨i, ?_⟩
        rw [← QuotientGroup.mk_zpow, QuotientGroup.eq] at hi
        exact hNn.mem_comm hi
      have hab : CommutatorsIn N := by
        intro x y
        have hcomm : ∀ a b : Q ⧸ N, a * b = b * a := by
          intro a b
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ a)
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ b)
          rw [← zpow_add, ← zpow_add, add_comm]
        have h1 := hcomm (QuotientGroup.mk x) (QuotientGroup.mk y)
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
        have h2 := hNn.mem_comm h1
        simpa [mul_assoc] using N.inv_mem h2
      have hcyc : CyclicOpenQuotients N := fun U hNU _ => ⟨g, fun x => by
        obtain ⟨i, hi⟩ := hgen x
        exact ⟨i, hNU hi⟩⟩
      let B : TypeObj.{uG, uW} Q :=
        ⟨FiniteRepresentation.of ρ, by
          let _ : TopologicalSpace (Module.End ℂ V) := moduleTopology ℂ (Module.End ℂ V)
          change Continuous ρ
          exact continuous_of_discreteTopology, hρ⟩
      obtain ⟨A, hA⟩ := exists_over (N := N) B
      have hrank := finrank_of_over hab hcyc B A hA
      have hNcard : Nat.card N < Nat.card Q := by
        rw [hN, hQ]
        exact Nat.pow_lt_pow_right hp.out.one_lt (Nat.lt_succ_self n)
      have : Finite N := inferInstance
      obtain ⟨b, hb⟩ := ih n (Nat.lt_succ_self n) N hN A.1 A.1.representation A.2.1
      have hdvd : (MulAction.stabilizer Q (wildClass A)).index ∣ p ^ 1 := by
        rw [pow_one, ← hindex]
        exact Subgroup.index_dvd_of_le (le_stabilizer _)
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
      refine ⟨k + b, ?_⟩
      change Module.finrank ℂ B.1 = _
      rw [hrank, hk, hb, pow_add]

section PPower

/-- Every open subgroup contains the `p ^ b`-th powers of all elements, for some `b` depending on
the subgroup. For a prime `p` and a profinite group this says that the group is pro-`p`. -/
def PPowerOpen (p : ℕ) (N : Type uG) [Group N] [TopologicalSpace N] : Prop :=
  ∀ M : Subgroup N, IsOpen (M : Set N) → ∃ b : ℕ, ∀ n : N, n ^ p ^ b ∈ M

variable {p : ℕ} {N : Type uG} [Group N] [TopologicalSpace N]

/-- A character with open kernel is killed by some power of `p`. -/
theorem PPowerOpen.char_pow (h : PPowerOpen p N) (χ : N →* ℂˣ) (hχ : IsOpen (χ.ker : Set N)) :
    ∃ b : ℕ, ∀ n : N, χ n ^ p ^ b = 1 := by
  obtain ⟨b, hb⟩ := h χ.ker hχ
  exact ⟨b, fun n => by rw [← map_pow]; exact hb n⟩

/-- The property transfers along a group isomorphism `N ≃* N'` that is continuous. -/
theorem PPowerOpen.of_continuous {N' : Type uW} [Group N'] [TopologicalSpace N']
    (h : PPowerOpen p N) (e : N ≃* N') (he : Continuous e) : PPowerOpen p N' := by
  intro M hM
  obtain ⟨b, hb⟩ := h (M.comap e.toMonoidHom) (hM.preimage he)
  refine ⟨b, fun n => ?_⟩
  have h1 := hb (e.symm n)
  rw [Subgroup.mem_comap] at h1
  have h2 : e.toMonoidHom (e.symm n ^ p ^ b) = n ^ p ^ b := by
    rw [map_pow]
    exact congrArg (· ^ p ^ b) (e.apply_symm_apply n)
  rwa [h2] at h1

/-- For a prime `p`, irreducible finite-dimensional representations with open kernel of a compact
group with the `p`-power property have `p`-power dimension. -/
theorem PPowerOpen.finrank [hp : Fact p.Prime] [IsTopologicalGroup N] [CompactSpace N]
    (h : PPowerOpen p N) {V : Type uW} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ N V) (hρ : ρ.IsIrreducible) (ho : IsOpen (ρ.ker : Set N)) :
    ∃ a : ℕ, Module.finrank ℂ V = p ^ a := by
  have : ρ.ker.FiniteIndex := finiteIndex_of_isOpen ho
  have : Finite (N ⧸ ρ.ker) := inferInstance
  obtain ⟨b, hb⟩ := h ρ.ker ho
  have hQ : IsPGroup p (N ⧸ ρ.ker) := by
    intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨b, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hb n
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  let ρ' : Representation ℂ (N ⧸ ρ.ker) V := QuotientGroup.lift ρ.ker ρ le_rfl
  have hcomp : ρ'.comp (QuotientGroup.mk' ρ.ker) = ρ := MonoidHom.ext fun _ => rfl
  have hρ' : ρ'.IsIrreducible := by
    apply Langlands.FiniteRepresentation.SplitDegree.isIrreducible_of_comp ρ' (QuotientGroup.mk' ρ.ker)
    rw [hcomp]
    exact hρ
  exact exists_finrank_eq_pow_of_isPGroup n (N ⧸ ρ.ker) hn V ρ' hρ'

/-- For a prime `p`, classes of irreducible representations with open kernel of a compact group
with the `p`-power property have `p`-power rank. -/
theorem PPowerOpen.rank [Fact p.Prime] [IsTopologicalGroup N] [CompactSpace N]
    (h : PPowerOpen p N) (c : OpenKernelIrreducibleClasses.{uG, uW} N) :
    ∃ a : ℕ, openKernelIrreducibleRank N c = p ^ a := by
  induction c using Quotient.inductionOn with
  | h A =>
    have := A.2.1
    exact h.finrank A.1.representation A.2.1 A.2.2

end PPower

end Langlands.Clifford

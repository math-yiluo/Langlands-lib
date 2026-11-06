import Langlands.Representation.Finite.DegreeZeroBrauerSupport
import Langlands.Representation.Finite.DegreeZeroMonomial
import Langlands.Representation.Finite.VirtualCharacterProof
import Langlands.AnthropicFLT.P2M.Sol.S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter

/-!
# Finite degree-zero Brauer induction

Proof of the unchanged genuine split representation-group statement, using
centered characters, Solomon induction, and retained-subgroup monomiality.
-/

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000

noncomputable section
open scoped Classical IsMulCommutative
open Module

namespace Langlands.FiniteRep.DegreeZeroBrauer

universe uG uQ uV
variable {G : Type uG} [Group G] [Fintype G]

/-- Subtract the value at the identity as a constant function. -/
def augment (G : Type uG) [Group G] : (G → ℂ) →ₗ[ℤ] (G → ℂ) where
  toFun f g := f g - f 1
  map_add' f h := by ext g; simp only [Pi.add_apply]; ring
  map_smul' a f := by ext g; simp only [Pi.smul_apply, zsmul_eq_mul, RingHom.id_apply]; ring

omit [Fintype G] in
@[simp] theorem augment_apply (f : G → ℂ) (g : G) : augment G f g = f g - f 1 := rfl

omit [Fintype G] in
theorem augment_pullback {Q : Type uQ} [Group Q] [Fintype Q]
    (π : G →* Q) (f : Q → ℂ) :
    augment G (pullback π f) = pullback π (augment Q f) := by
  ext g
  simp [augment, pullback]

theorem ind_at_one (S : Subgroup G) (f : S → ℂ) :
    ind S f 1 = (Nat.card S : ℂ)⁻¹ * (Nat.card G : ℂ) * f 1 := by
  rw [ind_apply]
  have hc : ∀ x : G,
      (if hx : x⁻¹ * (1 : G) * x ∈ S then f ⟨x⁻¹ * 1 * x, hx⟩ else 0) = f 1 := by
    intro x
    rw [dite_eq_left (by simp)]
    exact congrArg f (Subtype.ext (by simp))
  have hs : (∑ x : G, if hx : x⁻¹ * (1 : G) * x ∈ S then
      f ⟨x⁻¹ * 1 * x, hx⟩ else 0) = (Nat.card G : ℂ) * f 1 := by
    calc
      _ = ∑ _x : G, f 1 := Finset.sum_congr rfl (fun x _ => hc x)
      _ = _ := by simp [← Nat.card_eq_fintype_card]
  rw [hs]
  ring

theorem augment_ind_scalar (S : Subgroup G) (χ : S →* ℂˣ)
    (h : augment G (ind S 1) ∈ characterSpan G) :
    augment G (ind S (fun s => (χ s : ℂ))) ∈ characterSpan G := by
  have hm := generator_mem S χ 1
  have he : augment G (ind S (fun s => (χ s : ℂ))) =
      ind S ((fun s => (χ s : ℂ)) - 1) + augment G (ind S 1) := by
    ext g
    simp only [augment_apply, map_sub, Pi.sub_apply, Pi.add_apply, ind_at_one,
      map_one, Units.val_one, Pi.one_apply]
    ring
  rw [he]
  exact Submodule.add_mem _ hm h

/-- The quotient permutation character descends whenever the subgroup contains the kernel. -/
theorem augment_permutation_mem (A S : Subgroup G) [A.Normal] (hAS : A ≤ S)
    (hQ : ∀ (V : FDRep ℂ (G ⧸ A)), augment (G ⧸ A) V.character ∈ characterSpan (G ⧸ A)) :
    augment G (ind S 1) ∈ characterSpan G := by
  let π : G →* G ⧸ A := QuotientGroup.mk' A
  let T : Subgroup (G ⧸ A) := S.map π
  have hc : T.comap π = S := Subgroup.comap_map_eq_self (by
    rw [QuotientGroup.ker_mk']
    exact hAS)
  have hi := ind_comap π (QuotientGroup.mk'_surjective A) T (1 : T → ℂ)
  change ind (T.comap π) 1 = pullback π (ind T 1) at hi
  rw [hc] at hi
  rw [hi, augment_pullback]
  apply pullback_mem π (QuotientGroup.mk'_surjective A)
  have he : (oneDimensional (1 : T →* ℂˣ)).character = 1 := by ext t; simp
  rw [← he, ind_character]
  exact hQ _

section Native
variable {K : Type} [Group K] [Fintype K]

/-- A retained normal abelian subgroup makes every monomial summand descend. -/
theorem augment_monomial_mem (A : Subgroup K) [A.Normal]
    (hQ : ∀ (V : FDRep ℂ (K ⧸ A)), augment (K ⧸ A) V.character ∈ characterSpan (K ⧸ A))
    (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ K W) (hm : DegreeZeroMonomial.Monomial A W σ) :
    augment K σ.character ∈ characterSpan K := by
  open P2MW.S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem.MonomialProof in
    obtain ⟨l, hl, he⟩ := hm
    have heq : σ.character = lsum l := funext he
    rw [heq]
    clear he heq
    induction l with
    | nil => simpa only [lsum_nil, map_zero] using (Submodule.zero_mem (characterSpan K))
    | cons e l ih =>
      rw [lsum_cons, map_add]
      refine Submodule.add_mem _ ?_ (ih (fun d hd => hl d (List.mem_cons_of_mem e hd)))
      have hA : A ≤ e.1 := hl e (List.mem_cons_self)
      have hgen := augment_ind_scalar e.1 e.2 (augment_permutation_mem A e.1 hA hQ)
      convert hgen using 1
      congr 1

/-- Induction on the order applies to a quotient by a nontrivial retained subgroup. -/
theorem augment_of_normal (p : ℕ) (hp : p.Prime)
    (A : Subgroup K) [A.Normal] (hA : A ≠ ⊥)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hpow : ∀ k : K, ∃ n : ℕ, k ^ p ^ n ∈ A)
    (ih : ∀ (Q : Type) [Group Q] [Fintype Q], Nat.card Q < Nat.card K →
      ∀ V : FDRep ℂ Q, augment Q V.character ∈ characterSpan Q)
    (V : FDRep ℂ K) : augment K V.character ∈ characterSpan K := by
  have hlt : Nat.card (K ⧸ A) < Nat.card K := by
    have hc := A.card_eq_card_quotient_mul_card_subgroup
    have ha := A.one_lt_card_iff_ne_bot.mpr hA
    have hq : 0 < Nat.card (K ⧸ A) := Nat.card_pos
    nlinarith
  apply augment_monomial_mem A (ih (K ⧸ A) hlt) V V.ρ
  exact DegreeZeroMonomial.engine hp _ K V V.ρ (le_refl _) A hcomm hpow

/-- A nontrivial hyperelementary group has a nontrivial normal abelian subgroup
with prime-power quotient, using the center in the pure p-group case. -/
theorem augment_of_hyper [Nontrivial K] (p : ℕ) (hp : p.Prime)
    (C : Subgroup K) (hcyc : IsCyclic C)
    (hn : ∀ h : K, ∀ c ∈ C, h * c * h⁻¹ ∈ C)
    (hpow : ∀ h : K, ∃ m : ℕ, h ^ p ^ m ∈ C)
    (ih : ∀ (Q : Type) [Group Q] [Fintype Q], Nat.card Q < Nat.card K →
      ∀ V : FDRep ℂ Q, augment Q V.character ∈ characterSpan Q)
    (V : FDRep ℂ K) : augment K V.character ∈ characterSpan K := by
  by_cases hc : C = ⊥
  · have hg : IsPGroup p K := by
      rw [isPGroup_iff_pow_pow_eq_one]
      intro k
      obtain ⟨m, hm⟩ := hpow k
      exact ⟨m, by simpa [hc] using hm⟩
    have : Fact p.Prime := ⟨hp⟩
    have : Nontrivial (Subgroup.center K) := hg.center_nontrivial
    have hcenter : Subgroup.center K ≠ ⊥ := by
      rw [← Subgroup.one_lt_card_iff_ne_bot]
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
    apply augment_of_normal p hp (Subgroup.center K) hcenter ?_ ?_ ih V
    · intro a ha b _
      exact (Subgroup.mem_center_iff.mp ha b).symm
    · intro k
      obtain ⟨m, hm⟩ := (isPGroup_iff_pow_pow_eq_one.mp hg) k
      exact ⟨m, hm ▸ (Subgroup.center K).one_mem⟩
  · have : C.Normal := ⟨fun c hc h => hn h c hc⟩
    have : IsCyclic C := hcyc
    apply augment_of_normal p hp C hc ?_ hpow ih V
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : C) ⟨b, hb⟩)

/-- The projection formula for a centered character. -/
theorem ind_augment_restrict (S : Subgroup K) (V : FDRep ℂ K) (g : K) :
    ind S (augment S ((FDRep.of (V.ρ.comp S.subtype)).character)) g =
      ClassFunction.induced S (fun _ => (1 : ℂ)) g * augment K V.character g := by
  rw [ind_apply, ClassFunction.induced_apply]
  have he : ∀ x : K,
      (if hx : x⁻¹ * g * x ∈ S then
        augment S (FDRep.of (V.ρ.comp S.subtype)).character ⟨x⁻¹ * g * x, hx⟩ else 0) =
      (if x⁻¹ * g * x ∈ S then (1 : ℂ) else 0) * augment K V.character g := by
    intro x
    split_ifs with hx
    · change V.character (x⁻¹ * g * x) - V.character 1 =
        1 * (V.character g - V.character 1)
      rw [one_mul, show V.character (x⁻¹ * g * x) = V.character g by
        simpa using V.char_conj g x⁻¹]
    · simp
  rw [Finset.sum_congr rfl (fun x _ => he x), ← Finset.sum_mul]
  ring

/-- Strong induction on finite group order for centered actual characters. -/
theorem augment_native (n : ℕ) :
    ∀ (K : Type) [Group K] [Fintype K], Nat.card K = n →
      ∀ V : FDRep ℂ K, augment K V.character ∈ characterSpan K := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K _ _ hcard V
    by_cases hK : Subsingleton K
    · have : Subsingleton K := hK
      have hz : augment K V.character = 0 := by
        ext g
        change V.character g - V.character 1 = 0
        rw [Subsingleton.elim g 1, sub_self]
      rw [hz]
      exact Submodule.zero_mem _
    have : Nontrivial K := not_subsingleton_iff_nontrivial.mp hK
    have hrec : ∀ (Q : Type) [Group Q] [Fintype Q], Nat.card Q < Nat.card K →
        ∀ W : FDRep ℂ Q, augment Q W.character ∈ characterSpan Q := by
      intro Q _ _ hQ W
      exact ih (Nat.card Q) (hQ.trans_eq hcard) Q rfl W
    obtain ⟨k, H, a, hH, h1⟩ :=
      P2MW.S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.BrauerProof.solomon_complex
        (G := K)
    by_cases htop : ∃ i, H i = ⊤
    · obtain ⟨i, hi⟩ := htop
      obtain ⟨p, hp, C, _, hcyc, _, hn, hpow⟩ := hH i
      have hh : ∀ h : K, h ∈ H i := by simp [hi]
      exact augment_of_hyper p hp C hcyc (fun h => hn h (hh h))
        (fun h => hpow h (hh h)) hrec V
    have hproper : ∀ i, H i ≠ ⊤ := fun i hi => htop ⟨i, hi⟩
    have heq : augment K V.character =
        ∑ i : Fin k, a i • ind (H i)
          (augment (H i) (FDRep.of (V.ρ.comp (H i).subtype)).character) := by
      ext g
      simp only [Finset.sum_apply, Pi.smul_apply]
      simp only [zsmul_eq_mul, ind_augment_restrict]
      have hh := congrArg (fun z : ℂ => z * augment K V.character g) (h1 g)
      simpa only [one_mul, Finset.sum_mul, mul_assoc] using hh
    rw [heq]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply ind_mem
    apply hrec (H i)
    have hc := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr (hproper i))
    simpa using hc

end Native
/-- Every centered actual character lies in the character image, in every group universe. -/
theorem augment_character_mem (V : FDRep ℂ G) :
    augment G V.character ∈ characterSpan G := by
  obtain ⟨K, _, _, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{uG, 0} G
  let W : FDRep ℂ K := FDRep.of (V.ρ.comp e.symm.toMonoidHom)
  have he : pullback e.toMonoidHom W.character = V.character := by
    ext g
    change V.character (e.symm (e g)) = V.character g
    rw [MulEquiv.symm_apply_apply]
  rw [← he, augment_pullback]
  exact pullback_mem e.toMonoidHom e.surjective (augment_native _ K rfl W)

/-- Each actual induced rank-one difference has virtual degree zero. -/
theorem span_le_degreeZero : degreeZeroBrauerSpan G ≤ degreeZeroVirtualReps G := by
  apply Submodule.span_le.mpr
  intro x hx
  obtain ⟨S, χ, χ', rfl⟩ := hx
  change virtualCharacter (k := ℂ) (virtualInduce S
    (ofClass (classOf (oneDimensional χ)) - ofClass (classOf (oneDimensional χ')))) 1 = 0
  rw [virtualCharacter_induce, ind_at_one]
  simp only [map_sub, Pi.sub_apply, virtualCharacter_ofClass, character_classOf,
    character_oneDimensional, map_one, Units.val_one, sub_self, mul_zero]

/-- Centering actual classes and character faithfulness give generation in the genuine group. -/
theorem degreeZero_le_span : degreeZeroVirtualReps G ≤ degreeZeroBrauerSpan G := by
  intro x hx
  have hx0 : virtualCharacter (k := ℂ) x 1 = 0 := hx
  have hm : augment G (virtualCharacter (k := ℂ) x) ∈ characterSpan G := by
    obtain ⟨a, b, rfl⟩ := virtualRep_exists_difference x
    induction a using Quotient.inductionOn with | h V =>
    induction b using Quotient.inductionOn with | h W =>
    change augment G (virtualCharacter (k := ℂ)
      (ofClass (classOf V) - ofClass (classOf W))) ∈ characterSpan G
    simpa only [map_sub, virtualCharacter_ofClass, character_classOf] using
      Submodule.sub_mem (characterSpan G) (augment_character_mem V) (augment_character_mem W)
  have he : augment G (virtualCharacter (k := ℂ) x) = virtualCharacter (k := ℂ) x := by
    ext g
    simp only [augment_apply, hx0, sub_zero]
  rw [he] at hm
  obtain ⟨y, hy, hyx⟩ := hm
  have hyx' : y = x := VirtualCharacter.faithfulness hyx
  exact hyx' ▸ hy

/-- Deligne's finite degree-zero Brauer theorem for the genuine split representation group. -/
theorem finiteDegreeZeroBrauer (G : Type uG) [Group G] [Fintype G] :
    FiniteDegreeZeroBrauerStatement G :=
  le_antisymm span_le_degreeZero degreeZero_le_span

end Langlands.FiniteRep.DegreeZeroBrauer

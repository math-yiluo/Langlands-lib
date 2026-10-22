import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.Order.Filter.Finite

/-!
# Ramification through the actual maximal-ideal quotients

The generic construction applies to an action on a local ring. The finite
separated case supplies the termination proof used by the conductor sums.
-/

namespace Langlands.Ramification

open IsLocalRing

universe u v

variable (R : Type u) (G : Type v) [CommRing R] [IsLocalRing R]
  [Group G] [MulSemiringAction G R]

/-- The actual quotient by the `n`th power of the maximal ideal. -/
abbrev CongruenceQuotient (n : ℕ) := R ⧸ maximalIdeal R ^ n

/-- Automorphisms acting trivially modulo the `n`th maximal-ideal power.
The index `n = 0` gives the entire group. -/
def congruenceGroup (n : ℕ) : Subgroup G :=
  (maximalIdeal R ^ n).inertia G

@[simp] theorem mem_congruenceGroup (n : ℕ) (g : G) :
    g ∈ congruenceGroup R G n ↔
      ∀ x : R, g • x - x ∈ maximalIdeal R ^ n := Iff.rfl

private theorem map_maximalIdeal_pow (n : ℕ) (g : G) :
    (maximalIdeal R ^ n).map (MulSemiringAction.toRingAut G R g).toRingHom =
      maximalIdeal R ^ n := by
  rw [Ideal.map_pow]
  exact congrArg (fun I : Ideal R => I ^ n)
    (map_maximalIdeal_of_surjective
      (MulSemiringAction.toRingAut G R g).toRingHom
      (MulSemiringAction.toRingAut G R g).surjective)

/-- The induced action on the actual ring quotient, not a supplied action. -/
def quotientAction (n : ℕ) : G →* RingAut (CongruenceQuotient R n) where
  toFun g := Ideal.quotientEquiv _ _ (MulSemiringAction.toRingAut G R g)
    (map_maximalIdeal_pow R G n g).symm
  map_one' := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ ((1 : G) • x) = Ideal.Quotient.mk _ x
    rw [one_smul]
  map_mul' g h := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ ((g * h) • x) =
      Ideal.Quotient.mk _ (g • h • x)
    rw [mul_smul]

@[simp] theorem quotientAction_mk (n : ℕ) (g : G) (x : R) :
    quotientAction R G n g (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (g • x) := rfl

theorem congruenceGroup_eq_ker (n : ℕ) :
    congruenceGroup R G n = (quotientAction R G n).ker := by
  ext g
  rw [mem_congruenceGroup, MonoidHom.mem_ker]
  constructor
  · intro hg
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq.mpr (hg x)
  · intro hg x
    exact Ideal.Quotient.eq.mp (congrArg
      (fun e : RingAut (CongruenceQuotient R n) =>
        e (Ideal.Quotient.mk _ x)) hg)

instance congruenceGroup_normal (n : ℕ) : (congruenceGroup R G n).Normal := by
  rw [congruenceGroup_eq_ker]
  infer_instance

@[simp] theorem congruenceGroup_zero : congruenceGroup R G 0 = ⊤ := by
  ext g
  simp [mem_congruenceGroup]

theorem congruenceGroup_antitone : Antitone (congruenceGroup R G) := by
  intro m n h g hg x
  exact Ideal.pow_le_pow_right h (hg x)

/-- Lower numbering for nonnegative indices: `G_i` acts trivially on
`R / m^(i+1)`. -/
def lowerGroup (i : ℕ) : Subgroup G := congruenceGroup R G (i + 1)

/-- Integer lower numbering, extended constantly to indices below `-1`. -/
def lowerGroupInt (i : ℤ) : Subgroup G :=
  if i < 0 then ⊤ else lowerGroup R G i.toNat

@[simp] theorem lowerGroupInt_neg_one : lowerGroupInt R G (-1) = ⊤ := by
  simp [lowerGroupInt]

@[simp] theorem lowerGroupInt_nat (i : ℕ) :
    lowerGroupInt R G (i : ℤ) = lowerGroup R G i := by
  simp [lowerGroupInt]

instance lowerGroup_normal (i : ℕ) : (lowerGroup R G i).Normal :=
  congruenceGroup_normal R G (i + 1)

theorem lowerGroup_antitone : Antitone (lowerGroup R G) :=
  fun _ _ h => congruenceGroup_antitone R G (Nat.add_le_add_right h 1)

/-- Zeroth ramification is the kernel of the actual action on the residue field. -/
theorem lowerGroup_zero :
    lowerGroup R G 0 = (maximalIdeal R).inertia G := by
  simp [lowerGroup, congruenceGroup]

section Separated

variable [IsNoetherianRing R] [FaithfulSMul G R]

theorem iInf_congruenceGroup : (⨅ n : ℕ, congruenceGroup R G n) = ⊥ := by
  apply le_antisymm
  · intro g hg
    apply Subgroup.mem_bot.mpr
    apply FaithfulSMul.eq_of_smul_eq_smul (α := R)
    intro x
    have hx : g • x - x ∈ ⨅ n : ℕ, maximalIdeal R ^ n := by
      exact Ideal.mem_iInf.mpr fun n =>
        (Subgroup.mem_iInf.mp hg n) x
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _
      (maximalIdeal.isMaximal R).ne_top] at hx
    simpa using sub_eq_zero.mp (Ideal.mem_bot.mp hx)
  · exact bot_le

variable [Finite G]

/-- Termination follows from Krull intersection, faithfulness, and finiteness
of the acting group; it is not an extra field of a ramification-data record. -/
theorem exists_congruenceGroup_eq_bot :
    ∃ b : ℕ, ∀ n ≥ b, congruenceGroup R G n = ⊥ := by
  classical
  have hg (g : G) : ∀ᶠ n in Filter.atTop, g ∈ congruenceGroup R G n → g = 1 := by
    by_cases h : g = 1
    · exact Filter.Eventually.of_forall (fun _ _ => h)
    · have hn : ∃ n, g ∉ congruenceGroup R G n := by
        by_contra! hall
        have : g ∈ ⨅ n, congruenceGroup R G n := Subgroup.mem_iInf.mpr hall
        rw [iInf_congruenceGroup R G] at this
        exact h (Subgroup.mem_bot.mp this)
      obtain ⟨n, hn⟩ := hn
      exact Filter.eventually_atTop.mpr ⟨n, fun m hm hgm =>
        (hn (congruenceGroup_antitone R G hm hgm)).elim⟩
  have hall := Filter.eventually_all.mpr hg
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.mp hall
  refine ⟨b, fun n hn => le_antisymm (fun g hg => ?_) bot_le⟩
  exact Subgroup.mem_bot.mpr (hb n hn g hg)

theorem exists_lowerGroup_eq_bot :
    ∃ b : ℕ, ∀ i ≥ b, lowerGroup R G i = ⊥ := by
  obtain ⟨b, hb⟩ := exists_congruenceGroup_eq_bot R G
  exact ⟨b, fun i hi => hb (i + 1) (hi.trans (Nat.le_succ i))⟩

end Separated

end Langlands.Ramification

import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.RingTheory.Finiteness.Subalgebra
import Mathlib.RingTheory.FilteredAlgebra.Basic
import Mathlib.Tactic.NoncommRing

/-! # The degree filtration of the actual universal enveloping algebra -/

noncomputable section
universe u v
set_option autoImplicit false

namespace Langlands.Algebra.UniversalEnveloping

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => UniversalEnvelopingAlgebra R L

/-- Constants together with the actual Lie generators. -/
def degreeOne : Submodule R U :=
  1 ⊔ LinearMap.range (UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap

/-- Products of at most `d` actual Lie generators, with their `R`-linear span. -/
def degreeFiltration (d : ℕ) : Submodule R U := degreeOne R L ^ d

@[simp]
theorem degreeFiltration_zero : degreeFiltration R L 0 = 1 := pow_zero _

@[simp]
theorem degreeFiltration_one : degreeFiltration R L 1 = degreeOne R L := pow_one _

theorem one_le_degreeOne : (1 : Submodule R U) ≤ degreeOne R L := le_sup_left

theorem generator_mem_degreeOne (x : L) :
    UniversalEnvelopingAlgebra.ι R x ∈ degreeOne R L :=
  (le_sup_right : LinearMap.range (UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap ≤
    degreeOne R L) (LinearMap.mem_range_self _ x)

theorem degreeFiltration_mono : Monotone (degreeFiltration R L) :=
  pow_right_monotone (one_le_degreeOne R L)

theorem degreeFiltration_mul (p q : ℕ) :
    degreeFiltration R L p * degreeFiltration R L q =
      degreeFiltration R L (p + q) := (pow_add _ _ _).symm

theorem mul_mem_degreeFiltration {p q : ℕ} {a b : U}
    (ha : a ∈ degreeFiltration R L p) (hb : b ∈ degreeFiltration R L q) :
    a * b ∈ degreeFiltration R L (p + q) := by
  rw [← degreeFiltration_mul]
  exact Submodule.mul_mem_mul ha hb

theorem algebraMap_mem_degreeFiltration (r : R) (d : ℕ) :
    algebraMap R U r ∈ degreeFiltration R L d :=
  degreeFiltration_mono R L (Nat.zero_le d) (Submodule.algebraMap_mem r)

instance degreeFiltration_gradedMonoid : SetLike.GradedMonoid (degreeFiltration R L) where
  one_mem := Submodule.one_le.mp le_rfl
  mul_mem := fun {_ _ _ _} ha hb => mul_mem_degreeFiltration R L ha hb

/-- The strict part of the filtration; the degree-zero strict part is zero. -/
def degreeFiltrationLT (d : ℕ) : Submodule R U := ⨆ i < d, degreeFiltration R L i

instance degreeFiltration_isRingFiltration :
    IsRingFiltration (degreeFiltration R L) (degreeFiltrationLT R L) where
  mono := degreeFiltration_mono R L
  is_le h := le_iSup_of_le _ (le_iSup_of_le h le_rfl)
  is_sup _ _ h := iSup_le fun i => iSup_le fun hi => h i hi

/-- Every element of the genuine quotient algebra lies in some finite degree. -/
theorem exists_mem_degreeFiltration (a : U) :
    ∃ d, a ∈ degreeFiltration R L d := by
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := R)
    (UniversalEnvelopingAlgebra.ringCon R L) a
  change ∃ d, UniversalEnvelopingAlgebra.mkAlgHom R L t ∈ degreeFiltration R L d
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    exact ⟨0, by simp⟩
  | ι x =>
    exact ⟨1, by simpa using generator_mem_degreeOne R L x⟩
  | mul a b ha hb =>
    obtain ⟨p, hp⟩ := ha
    obtain ⟨q, hq⟩ := hb
    exact ⟨p + q, by simpa using mul_mem_degreeFiltration R L hp hq⟩
  | add a b ha hb =>
    obtain ⟨p, hp⟩ := ha
    obtain ⟨q, hq⟩ := hb
    refine ⟨max p q, ?_⟩
    rw [map_add]
    exact (degreeFiltration R L _).add_mem
      (degreeFiltration_mono R L (le_max_left _ _) hp)
      (degreeFiltration_mono R L (le_max_right _ _) hq)

theorem iSup_degreeFiltration : (⨆ d, degreeFiltration R L d) = ⊤ := by
  apply top_unique
  intro a _
  obtain ⟨d, hd⟩ := exists_mem_degreeFiltration R L a
  exact Submodule.mem_iSup_of_mem d hd

/-- Commutators of degree-one elements remain in degree one. -/
theorem commutator_mem_degreeOne {a b : U}
    (ha : a ∈ degreeOne R L) (hb : b ∈ degreeOne R L) :
    a * b - b * a ∈ degreeOne R L := by
  obtain ⟨c, hc, x, hx, rfl⟩ := Submodule.mem_sup.mp ha
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hc
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨c, hc, y, hy, rfl⟩ := Submodule.mem_sup.mp hb
  obtain ⟨s, rfl⟩ := Submodule.mem_one.mp hc
  obtain ⟨y, rfl⟩ := hy
  have h :
      (algebraMap R U r + UniversalEnvelopingAlgebra.ι R x) *
          (algebraMap R U s + UniversalEnvelopingAlgebra.ι R y) -
        (algebraMap R U s + UniversalEnvelopingAlgebra.ι R y) *
          (algebraMap R U r + UniversalEnvelopingAlgebra.ι R x) =
        UniversalEnvelopingAlgebra.ι R x * UniversalEnvelopingAlgebra.ι R y -
          UniversalEnvelopingAlgebra.ι R y * UniversalEnvelopingAlgebra.ι R x := by
    noncomm_ring [Algebra.commutes r (algebraMap R U s),
      Algebra.commutes r (UniversalEnvelopingAlgebra.ι R y),
      Algebra.commutes s (UniversalEnvelopingAlgebra.ι R x)]
  change (algebraMap R U r + UniversalEnvelopingAlgebra.ι R x) *
      (algebraMap R U s + UniversalEnvelopingAlgebra.ι R y) -
      (algebraMap R U s + UniversalEnvelopingAlgebra.ι R y) *
        (algebraMap R U r + UniversalEnvelopingAlgebra.ι R x) ∈ degreeOne R L
  have hxy : UniversalEnvelopingAlgebra.ι R ⁅x, y⁆ =
      UniversalEnvelopingAlgebra.ι R x * UniversalEnvelopingAlgebra.ι R y -
        UniversalEnvelopingAlgebra.ι R y * UniversalEnvelopingAlgebra.ι R x :=
    (UniversalEnvelopingAlgebra.ι R).map_lie x y
  rw [h, ← hxy]
  exact generator_mem_degreeOne R L _

/-- A degree-one commutator preserves every filtration piece. -/
theorem commutator_degreeOne_mem {a b : U} {d : ℕ}
    (ha : a ∈ degreeOne R L) (hb : b ∈ degreeFiltration R L d) :
    a * b - b * a ∈ degreeFiltration R L d := by
  induction hb using Submodule.pow_induction_on_right' with
  | algebraMap r =>
    rw [← Algebra.commutes r a, sub_self]
    exact (degreeFiltration R L 0).zero_mem
  | add x y i hx hy ihx ihy =>
    have h : a * (x + y) - (x + y) * a =
        (a * x - x * a) + (a * y - y * a) := by noncomm_ring
    rw [h]
    exact (degreeFiltration R L i).add_mem ihx ihy
  | mul_mem i x hx ih m hm =>
    have h : a * (x * m) - (x * m) * a =
        (a * x - x * a) * m + x * (a * m - m * a) := by noncomm_ring
    rw [h]
    exact (degreeFiltration R L (i + 1)).add_mem
      (mul_mem_degreeFiltration R L ih (show m ∈ degreeFiltration R L 1 by simpa using hm))
      (mul_mem_degreeFiltration R L hx
        (show a * m - m * a ∈ degreeFiltration R L 1 from
          by simpa using commutator_mem_degreeOne R L ha hm))

/-- Commutators lower the total degree by one when the second degree is positive. -/
theorem commutator_mem_degreeFiltration_succ {p q : ℕ} {a b : U}
    (ha : a ∈ degreeFiltration R L p) (hb : b ∈ degreeFiltration R L (q + 1)) :
    a * b - b * a ∈ degreeFiltration R L (p + q) := by
  induction ha using Submodule.pow_induction_on_right' with
  | algebraMap r =>
    rw [Algebra.commutes r b, sub_self]
    exact (degreeFiltration R L (0 + q)).zero_mem
  | add x y i hx hy ihx ihy =>
    have h : (x + y) * b - b * (x + y) =
        (x * b - b * x) + (y * b - b * y) := by noncomm_ring
    rw [h]
    exact (degreeFiltration R L (i + q)).add_mem ihx ihy
  | mul_mem i x hx ih m hm =>
    have h : (x * m) * b - b * (x * m) =
        x * (m * b - b * m) + (x * b - b * x) * m := by noncomm_ring
    rw [h]
    apply (degreeFiltration R L (i + 1 + q)).add_mem
    · simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        mul_mem_degreeFiltration R L hx (commutator_degreeOne_mem R L hm hb)
    · simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        mul_mem_degreeFiltration R L ih (show m ∈ degreeFiltration R L 1 by simpa using hm)

/-- The commutator of pieces `p` and `q` lies in piece `p+q-1`. -/
theorem commutator_mem_degreeFiltration {p q : ℕ} {a b : U}
    (ha : a ∈ degreeFiltration R L p) (hb : b ∈ degreeFiltration R L q) :
    a * b - b * a ∈ degreeFiltration R L (p + q - 1) := by
  cases q with
  | zero =>
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hb
    rw [← Algebra.commutes r a, sub_self]
    exact (degreeFiltration R L _).zero_mem
  | succ q =>
    simpa only [Nat.succ_eq_add_one, ← Nat.add_assoc, Nat.add_sub_cancel] using
      commutator_mem_degreeFiltration_succ R L ha hb

theorem degreeOne_fg [Module.Finite R L] : (degreeOne R L).FG := by
  have h : (1 : Submodule R U).FG := by
    simpa only [Submodule.one_eq_span] using
      Submodule.fg_span_singleton (R := R) (1 : U)
  exact h.sup
    (Submodule.fg_range (UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap)

theorem degreeFiltration_fg [Module.Finite R L] (d : ℕ) :
    (degreeFiltration R L d).FG := (degreeOne_fg R L).pow d

instance degreeFiltration_finite [Module.Finite R L] (d : ℕ) :
    Module.Finite R (degreeFiltration R L d) :=
  Module.Finite.of_fg (degreeFiltration_fg R L d)

end Langlands.Algebra.UniversalEnveloping

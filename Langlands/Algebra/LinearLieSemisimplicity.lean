import Mathlib.Algebra.Lie.LieTheorem
import Langlands.Algebra.WeylCompleteReducibility
import Langlands.LinearAlgebra.JordanChevalleyFunctoriality

/-!
# Complete reducibility for Jordan-closed linear Lie algebras

Authors: Worker 1429
-/

noncomputable section

open Module LieModule LieAlgebra

universe u v w

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Langlands.Algebra

/-- Over an algebraically closed field of characteristic zero, every element of `⁅L, rad L⁆` acts
nilpotently on every finite-dimensional representation of `L`. The proof is by strong induction on
the dimension, using Lie's theorem for the radical and the invariance of its weight spaces. -/
theorem isNilpotent_toEnd_of_mem_lie_radical {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {L : Type v} [LieRing L] [LieAlgebra k L] [FiniteDimensional k L] (n : ℕ) :
    ∀ (M : Type w) [AddCommGroup M] [Module k M] [LieRingModule L M] [LieModule k L M]
      [FiniteDimensional k M], finrank k M = n →
      ∀ y ∈ ⁅(⊤ : LieIdeal k L), radical k L⁆, IsNilpotent (toEnd k L M y) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ _ _ _ _ hn y hy
  rcases subsingleton_or_nontrivial M with hM | hM
  · exact ⟨1, Subsingleton.elim _ _⟩
  obtain ⟨χ, hχ⟩ := exists_nontrivial_weightSpace_of_isSolvable k (radical k L) M
  let N : LieSubmodule k L M := weightSpaceOfIsLieTower k M χ
  have hNt : Nontrivial N := hχ
  have hNr : ∀ (r : L) (hr : r ∈ radical k L) (m : M), m ∈ N → ⁅r, m⁆ = χ ⟨r, hr⟩ • m :=
    fun r hr m hm => (mem_weightSpace χ m).mp hm ⟨r, hr⟩
  have hker : ⁅(⊤ : LieIdeal k L), radical k L⁆ ≤ LieModule.ker k L N := by
    rw [LieSubmodule.lie_le_iff]
    intro x _ r hr
    rw [LieModule.mem_ker]
    intro m
    apply Subtype.ext
    rw [LieSubmodule.coe_bracket, lie_lie, hNr r hr m m.2,
      hNr r hr _ (N.lie_mem m.2), lie_smul, sub_self, LieSubmodule.coe_zero]
  have hlt : finrank k (M ⧸ N) < n := by
    have h1 := Submodule.finrank_quotient_add_finrank N.toSubmodule
    have h2 : 0 < finrank k N := Module.finrank_pos
    change finrank k (M ⧸ N.toSubmodule) < n
    change 0 < finrank k N.toSubmodule at h2
    omega
  obtain ⟨b, hb⟩ := ih _ hlt (M ⧸ N) rfl y hy
  have hbN : ∀ m : M, ((toEnd k L M y) ^ b) m ∈ N := by
    intro m
    rw [← LieSubmodule.Quotient.mk_eq_zero]
    have := LinearMap.congr_fun
      (Module.End.commute_pow_left_of_commute (LieSubmodule.Quotient.toEnd_comp_mk' N y) b) m
    rw [hb] at this
    exact this.symm
  refine ⟨b + 1, ?_⟩
  ext m
  rw [pow_succ', Module.End.mul_apply, LinearMap.zero_apply]
  have h := (LieModule.mem_ker k L N y).mp (hker hy) ⟨_, hbN m⟩
  exact congrArg Subtype.val h

/-- **Complete reducibility for Jordan-closed linear Lie algebras.** Let `k` be an algebraically
closed field of characteristic zero and `h` a Lie subalgebra of `End V` for a finite-dimensional
`V`. If `h` has no nonzero ideal consisting of nilpotent endomorphisms, and `h` contains the
semisimple Jordan part of each of its elements, then every `h`-invariant subspace of `V` has an
`h`-invariant complement. -/
theorem complementedLattice_lieSubmodule_of_jordanClosed
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (h : LieSubalgebra k (Module.End k V))
    (hnil : ∀ I : LieIdeal k h, (∀ x ∈ I, IsNilpotent ((x : h) : Module.End k V)) → I = ⊥)
    (hjordan : ∀ x ∈ h, Langlands.LinearAlgebra.jordanSemisimplePart x ∈ h) :
    ComplementedLattice (LieSubmodule k h V) := by
  have htoEnd : ∀ x : h, toEnd k h V x = (x : Module.End k V) := fun _ => rfl
  -- The radical of `h` is central.
  have hI : ⁅(⊤ : LieIdeal k h), radical k h⁆ = ⊥ := by
    apply hnil
    intro x hx
    rw [← htoEnd]
    exact isNilpotent_toEnd_of_mem_lie_radical _ V rfl x hx
  have : HasCentralRadical k h := by
    apply hasCentralRadical_of_radical_le
    intro r hr
    rw [LieModule.mem_maxTrivSubmodule]
    intro x
    have hxr : ⁅x, r⁆ ∈ ⁅(⊤ : LieIdeal k h), radical k h⁆ :=
      LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) hr
    rw [hI] at hxr
    exact (LieSubmodule.mem_bot _).mp hxr
  -- Central elements act semisimply.
  apply WeylCompleteReducibility.complementedLattice_of_isSemisimple_center
  intro z hz
  rw [htoEnd]
  obtain ⟨hsad, hnilp, hss, -⟩ := LinearAlgebra.jordanSemisimplePart_properties (z : Module.End k V)
  have hcomm : ∀ y ∈ h, Commute y (z : Module.End k V) := by
    intro y hy
    have h0 := congrArg Subtype.val ((LieModule.mem_maxTrivSubmodule k h h z).mp hz ⟨y, hy⟩)
    rw [LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket] at h0
    exact sub_eq_zero.mp h0
  let nn : h := ⟨(z : Module.End k V) - LinearAlgebra.jordanSemisimplePart (z : Module.End k V),
    h.sub_mem z.2 (hjordan _ z.2)⟩
  have hncen : ∀ y : h, ⁅y, nn⁆ = 0 := by
    intro y
    apply Subtype.ext
    rw [LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket]
    change _ - _ = (0 : Module.End k V)
    rw [sub_eq_zero]
    exact ((hcomm y y.2).sub_right
      (Algebra.commute_of_mem_adjoin_singleton_of_commute hsad (hcomm y y.2))).eq
  let I : LieIdeal k h :=
    { toSubmodule := k ∙ nn
      lie_mem := fun {y m} hm => by
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hm
        rw [lie_smul, hncen, smul_zero]
        exact Submodule.zero_mem _ }
  have hI0 : I = ⊥ := by
    apply hnil
    intro y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact hnilp.smul c
  have hn0 : nn = 0 := by
    have hmem : nn ∈ I := Submodule.mem_span_singleton_self nn
    rw [hI0] at hmem
    exact (LieSubmodule.mem_bot _).mp hmem
  have hx : (z : Module.End k V) = LinearAlgebra.jordanSemisimplePart (z : Module.End k V) :=
    sub_eq_zero.mp (congrArg Subtype.val hn0)
  rw [hx]
  exact hss

end Langlands.Algebra

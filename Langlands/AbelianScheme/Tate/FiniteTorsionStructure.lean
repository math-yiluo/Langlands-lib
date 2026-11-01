import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.ZMod.Basic

/-! # Finite torsion structure from torsion cardinalities -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Module

namespace Langlands.AbelianScheme.Tate

private theorem subgroup_eq_top_of_nilpotent_nsmul
    {M : Type*} [AddCommGroup M] (H : AddSubgroup M) (p e : ℕ)
    (hkill : ∀ x : M, p ^ e • x = 0)
    (hmod : ∀ x : M, ∃ y : M, x - p • y ∈ H) : H = ⊤ := by
  have hiter (k : ℕ) (x : M) : ∃ y : M, x - p ^ k • y ∈ H := by
    induction k with
    | zero => exact ⟨x, by simp⟩
    | succ k ih =>
      obtain ⟨y, hy⟩ := ih
      obtain ⟨z, hz⟩ := hmod y
      refine ⟨z, ?_⟩
      have h := H.add_mem hy (H.nsmul_mem hz (p ^ k))
      simpa only [nsmul_sub, pow_succ', mul_nsmul, sub_add_sub_cancel] using h
  apply top_unique
  intro x _
  obtain ⟨y, hy⟩ := hiter e x
  simpa only [hkill, sub_zero] using hy

/-- A finite abelian group killed by `p^e` is a power of `ZMod (p^e)` if
its order and its `p`-torsion order have the corresponding values. -/
theorem nonempty_pi_zmod_equiv_of_prime_power_card
    (M : Type*) [AddCommGroup M] [_root_.Finite M] (p e r : ℕ) (hp : p.Prime)
    (hkill : ∀ x : M, p ^ e • x = 0)
    (hcard : Nat.card M = (p ^ e) ^ r)
    (hpcard : Nat.card (nsmulAddMonoidHom (α := M) p).ker = p ^ r) :
    Nonempty ((Fin r → ZMod (p ^ e)) ≃+ M) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let modM : Module (ZMod (p ^ e)) M := AddCommGroup.zmodModule hkill
  let P : AddSubgroup M := (nsmulAddMonoidHom (α := M) p).range
  let Q := M ⧸ P
  let π : M →+ Q := QuotientAddGroup.mk' P
  let modQ : Module (ZMod p) Q := QuotientAddGroup.zmodModule
    (fun x => show p • x ∈ P from ⟨x, rfl⟩)
  let : _root_.Finite Q := inferInstance
  let finQ : Module.Finite (ZMod p) Q := Module.Finite.of_finite
  let freeQ : Module.Free (ZMod p) Q :=
    @Module.Free.of_divisionRing (ZMod p) Q _ _ modQ
  have hQ : Nat.card Q = p ^ r := by
    change P.index = p ^ r
    exact (AddSubgroup.index_range (f := nsmulAddMonoidHom (α := M) p)).trans hpcard
  have hdim : Module.finrank (ZMod p) Q = r := by
    apply (Nat.pow_right_injective hp.two_le)
    rw [@Module.natCard_eq_pow_finrank (ZMod p) Q inferInstance inferInstance modQ finQ,
      Nat.card_zmod] at hQ
    exact hQ
  let b : Basis (Fin r) (ZMod p) Q :=
    @Module.finBasisOfFinrankEq (ZMod p) Q _ _ modQ freeQ _ finQ r hdim
  let bv : Fin r → Q := fun i => b.repr.symm.toFun (Finsupp.single i 1)
  choose v hv using fun i : Fin r => QuotientAddGroup.mk'_surjective P (bv i)
  let f : (Fin r → ZMod (p ^ e)) →ₗ[ZMod (p ^ e)] M :=
    { toFun := fun a => ∑ i, a i • v i
      map_add' := by intro a c; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro c a; simp [Pi.smul_apply, smul_smul, Finset.smul_sum] }
  let H : AddSubgroup M := f.range.toAddSubgroup
  have hvH (i : Fin r) : v i ∈ H := by
    refine ⟨Pi.single i 1, ?_⟩
    simp [f, Pi.single_apply]
  have hmod (x : M) : ∃ y : M, x - p • y ∈ H := by
    let z : M := ∑ i, (b.repr.toFun (π x) i).val • v i
    have hzH : z ∈ H := H.sum_mem fun i _ => H.nsmul_mem (hvH i) _
    have hπ : π z = π x := by
      change π (∑ i, (b.repr.toFun (π x) i).val • v i) = π x
      rw [map_sum]
      simp_rw [map_nsmul, show ∀ i, π (v i) = bv i from hv]
      simpa only [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val, bv,
        LinearEquiv.toFun_eq_coe, Basis.repr_symm_single_one] using
        b.sum_repr (π x)
    have hmem : x - z ∈ P := by
      apply (QuotientAddGroup.eq_zero_iff (x - z)).mp
      change π (x - z) = 0
      rw [map_sub, hπ, sub_self]
    obtain ⟨y, hy⟩ := hmem
    refine ⟨y, ?_⟩
    change p • y = x - z at hy
    simpa only [hy, sub_sub_cancel] using hzH
  have hH : H = ⊤ := subgroup_eq_top_of_nilpotent_nsmul H p e hkill hmod
  have hsurj : Function.Surjective f.toFun := by
    intro x
    have hx : x ∈ H := hH ▸ AddSubgroup.mem_top x
    exact hx
  have hsize : Nat.card (Fin r → ZMod (p ^ e)) = Nat.card M := by
    rw [hcard, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  exact ⟨AddEquiv.ofBijective f.toAddMonoidHom
    ((Nat.bijective_iff_surjective_and_card f.toFun).mpr ⟨hsurj, hsize⟩)⟩

/-- Choose the additive equivalence supplied by the prime-power cardinality criterion. -/
def piZmodEquivOfPrimePowerCard
    (M : Type*) [AddCommGroup M] [_root_.Finite M] (p e r : ℕ) (hp : p.Prime)
    (hkill : ∀ x : M, p ^ e • x = 0)
    (hcard : Nat.card M = (p ^ e) ^ r)
    (hpcard : Nat.card (nsmulAddMonoidHom (α := M) p).ker = p ^ r) :
    (Fin r → ZMod (p ^ e)) ≃+ M :=
  Classical.choice
    (nonempty_pi_zmod_equiv_of_prime_power_card M p e r hp hkill hcard hpcard)

end Langlands.AbelianScheme.Tate

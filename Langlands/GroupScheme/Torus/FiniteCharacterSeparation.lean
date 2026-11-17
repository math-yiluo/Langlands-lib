import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Int.Basic

/-! # Finite characteristic quotients separating finite character sets -/

noncomputable section

universe u

open scoped DirectSum

namespace Langlands.GroupScheme.FiniteCharacterSeparation

variable {M : Type u} [AddCommGroup M]

/-- The characteristic subgroup of multiples of a positive integer. -/
abbrev multiples (n : ℕ) : AddSubgroup M := (nsmulAddMonoidHom (α := M) n).range

/-- Every nonzero element of a finitely generated abelian group is excluded
by some subgroup of integer multiples. -/
theorem exists_not_mem_multiples [AddGroup.FG M] {x : M} (hx : x ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ x ∉ multiples n := by
  classical
  obtain ⟨r, I, _, p, hp, e, ⟨b⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod M
  let T := ⨁ i : I, ZMod (p i ^ e i)
  let : ∀ i : I, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let : Finite T := Finite.of_equiv (∀ i : I, ZMod (p i ^ e i))
    (DirectSum.addEquivProd (fun i : I => ZMod (p i ^ e i))).symm.toEquiv
  by_cases hfree : (b x).1 = 0
  · refine ⟨Nat.card T, Nat.card_pos, ?_⟩
    rintro ⟨y, hy⟩
    have htor : (b x).2 = 0 := by
      rw [← hy, nsmulAddMonoidHom_apply, map_nsmul]
      change (Nat.card T) • (b y).2 = 0
      exact card_nsmul_eq_zero' (x := (b y).2)
    apply hx
    apply b.injective
    exact (Prod.ext hfree htor).trans b.map_zero.symm
  · obtain ⟨i, hi⟩ : ∃ i : Fin r, (b x).1 i ≠ 0 := by
      by_contra! h
      exact hfree (Finsupp.ext h)
    let n := ((b x).1 i).natAbs + 1
    refine ⟨n, Nat.zero_lt_succ _, ?_⟩
    rintro ⟨y, hy⟩
    have hcoord : (n : ℤ) * (b y).1 i = (b x).1 i := by
      have h := congrArg (fun z => (b z).1 i) hy
      simp only [nsmulAddMonoidHom_apply, map_nsmul] at h
      change n • (b y).1 i = (b x).1 i at h
      simpa only [nsmul_eq_mul] using h
    have hdvd : (n : ℤ) ∣ (b x).1 i := ⟨(b y).1 i, hcoord.symm⟩
    have hz : ((b x).1 i).natAbs = 0 :=
      Nat.eq_zero_of_dvd_of_lt (Int.natCast_dvd.mp hdvd) (Nat.lt_succ_self _)
    exact hi (Int.natAbs_eq_zero.mp hz)

/-- Reduction modulo integer multiples distinguishes the chosen finite set. -/
def Separates (n : ℕ) (S : Finset M) : Prop :=
  Set.InjOn (QuotientAddGroup.mk' (multiples (M := M) n)) (S : Set M)

/-- One characteristic quotient simultaneously separates any finite set of
characters in a finitely generated abelian group. -/
theorem exists_separates [AddGroup.FG M] (S : Finset M) :
    ∃ n : ℕ, 0 < n ∧ Separates n S := by
  classical
  have hsep (d : M) : ∃ n : ℕ, 0 < n ∧ (d ≠ 0 → d ∉ multiples n) := by
    by_cases hd : d = 0
    · exact ⟨1, Nat.zero_lt_one, fun h => False.elim (h hd)⟩
    · obtain ⟨n, hn, hd⟩ := exists_not_mem_multiples hd
      exact ⟨n, hn, fun _ => hd⟩
  choose k hk hksep using hsep
  let D : Finset M := (S.product S).image fun xy => xy.1 - xy.2
  let n := ∏ d ∈ D, k d
  have hn : n ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun d _ => (hk d).ne')
  refine ⟨n, Nat.pos_of_ne_zero hn, ?_⟩
  intro x hx y hy hxy
  by_contra hne
  have hd : x - y ∈ D :=
    Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩
  have hdiv : k (x - y) ∣ n := Finset.dvd_prod_of_mem k hd
  have hz : x - y ∈ multiples n := by
    apply (QuotientAddGroup.eq_zero_iff _).mp
    change (QuotientAddGroup.mk' (multiples n)) (x - y) = 0
    rw [map_sub, hxy, sub_self]
  apply hksep (x - y) (sub_ne_zero.mpr hne)
  obtain ⟨z, hz⟩ := hz
  obtain ⟨a, ha⟩ := hdiv
  refine ⟨a • z, ?_⟩
  change k (x - y) • (a • z) = x - y
  rw [← mul_nsmul, mul_comm a, ← ha]
  exact hz

/-- Every positive integer multiple subgroup has finite index. -/
theorem finite_quotient [AddGroup.FG M] {n : ℕ} (hn : n ≠ 0) :
    Finite (M ⧸ multiples n) := by
  let : (multiples (M := M) n).FiniteIndex :=
    AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg M hn
  infer_instance

/-- A finite-character projection loses no coefficient information on a
specified finite support on which the projection is injective. -/
theorem mapDomain_eq_zero_iff_of_support
    {A N : Type u} [Semiring A] (f : M → N) (S : Set M) (hf : Set.InjOn f S)
    (w : AddMonoidAlgebra A M) (hw : (w.coeff.support : Set M) ⊆ S) :
    AddMonoidAlgebra.mapDomain f w = 0 ↔ w = 0 := by
  constructor
  · intro h
    apply AddMonoidAlgebra.coeff_injective
    apply Finsupp.mapDomain_injOn S hf hw (by simp)
    exact congrArg AddMonoidAlgebra.coeff h
  · rintro rfl
    exact AddMonoidAlgebra.mapDomain_zero f

end Langlands.GroupScheme.FiniteCharacterSeparation

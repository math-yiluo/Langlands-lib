import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.Order.ModularLattice
import Mathlib.RingTheory.Nilpotent.Defs

/-! # Extending an intertwining equivalence from the image of an endomorphism -/

noncomputable section

open LinearMap Module

set_option autoImplicit false

namespace Langlands

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- An endomorphism restricts to an endomorphism of its range. -/
def linearEndomorphismOnRange (f : Module.End K V) : Module.End K (LinearMap.range f) :=
  f.rangeRestrict.comp f.range.subtype

@[simp]
theorem coe_linearEndomorphismOnRange_apply (f : Module.End K V) (x : LinearMap.range f) :
    (linearEndomorphismOnRange f x : V) = f x := rfl

private theorem ker_linearEndomorphismOnRange (f : Module.End K V) :
    LinearMap.ker (linearEndomorphismOnRange f) = (f.range ⊓ f.ker).comap f.range.subtype := by
  ext x
  change linearEndomorphismOnRange f x = 0 ↔ (x : V) ∈ f.range ⊓ f.ker
  rw [Submodule.mem_inf]
  exact ⟨fun h => ⟨x.property, congrArg Subtype.val h⟩,
    fun h => Subtype.ext h.2⟩

private theorem exists_kernelComplement (f : Module.End K V) :
    ∃ P : Submodule K V, Disjoint f.range P ∧ f.range ⊓ f.ker ⊔ P = f.ker := by
  obtain ⟨P, hP, hsup⟩ := IsModularLattice.exists_disjoint_and_sup_eq
    (inf_le_right : f.range ⊓ f.ker ≤ f.ker)
  have hle : P ≤ f.ker := hsup ▸ le_sup_right
  refine ⟨P, Submodule.disjoint_def.mpr (fun x hx hxp => ?_), hsup⟩
  exact Submodule.disjoint_def.mp hP x ⟨hx, hle hxp⟩ hxp

private theorem finrank_range_inf_ker_eq [FiniteDimensional K V] [FiniteDimensional K W]
    (f : Module.End K V) (g : Module.End K W) (e : f.range ≃ₗ[K] g.range)
    (he : ∀ x, e (linearEndomorphismOnRange f x) = linearEndomorphismOnRange g (e x)) :
    finrank K (f.range ⊓ f.ker : Submodule K V) = finrank K (g.range ⊓ g.ker : Submodule K W) := by
  have hk : (LinearMap.ker (linearEndomorphismOnRange f)).map e.toLinearMap =
      LinearMap.ker (linearEndomorphismOnRange g) := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      change linearEndomorphismOnRange g (e v) = 0
      rw [← he, mem_ker.mp hv, map_zero]
    · intro hw
      refine ⟨e.symm w, mem_ker.mpr ?_, e.apply_symm_apply w⟩
      apply e.injective
      rw [he, e.apply_symm_apply, map_zero]
      exact mem_ker.mp hw
  have h := (e.finrank_map_eq (ker (linearEndomorphismOnRange f))).symm
  rw [hk, ker_linearEndomorphismOnRange, ker_linearEndomorphismOnRange] at h
  rw [← (Submodule.comapSubtypeEquivOfLe (inf_le_left : f.range ⊓ f.ker ≤ f.range)).finrank_eq,
    ← (Submodule.comapSubtypeEquivOfLe (inf_le_left : g.range ⊓ g.ker ≤ g.range)).finrank_eq]
  exact h

/-- A linear equivalence intertwining the restrictions to the two ranges extends to a
linear equivalence of the full spaces, provided the ambient dimensions agree. -/
theorem exists_intertwiningLinearEquiv_of_range [FiniteDimensional K V] [FiniteDimensional K W]
    (f : Module.End K V) (g : Module.End K W) (hdim : finrank K V = finrank K W)
    (e : f.range ≃ₗ[K] g.range)
    (he : ∀ x, e (linearEndomorphismOnRange f x) = linearEndomorphismOnRange g (e x)) :
    ∃ E : V ≃ₗ[K] W, (∀ x : f.range, E x = (e x : W)) ∧ ∀ v, E (f v) = g (E v) := by
  obtain ⟨P, hP, hPs⟩ := exists_kernelComplement f
  obtain ⟨Q, hQ, hQs⟩ := exists_kernelComplement g
  have hPk : P ≤ f.ker := hPs ▸ le_sup_right
  have hQk : Q ≤ g.ker := hQs ▸ le_sup_right
  have hkr : finrank K f.ker = finrank K g.ker := by
    have hf := f.finrank_range_add_finrank_ker
    have hg := g.finrank_range_add_finrank_ker
    rw [e.finrank_eq, hdim, ← hg] at hf
    exact Nat.add_left_cancel hf
  have hleft := Submodule.finrank_sup_add_finrank_inf_eq (f.range ⊓ f.ker) P
  have hright := Submodule.finrank_sup_add_finrank_inf_eq (g.range ⊓ g.ker) Q
  rw [hPs, (hP.mono_left inf_le_left).eq_bot, finrank_bot, add_zero] at hleft
  rw [hQs, (hQ.mono_left inf_le_left).eq_bot, finrank_bot, add_zero] at hright
  have hPQ : finrank K P = finrank K Q := by
    rw [finrank_range_inf_ker_eq f g e he, hkr] at hleft
    omega
  let eK : P ≃ₗ[K] Q := LinearEquiv.ofFinrankEq _ _ hPQ
  obtain ⟨U, hU⟩ := f.range.exists_isCompl
  let p : V →ₗ[K] f.range := f.range.projectionOnto U hU
  obtain ⟨J, hJ⟩ := g.rangeRestrict.exists_rightInverse_of_surjective g.range_rangeRestrict
  have hJ' (w : g.range) : g.rangeRestrict (J w) = w := LinearMap.congr_fun hJ w
  let L : V →ₗ[K] W := g.range.subtype.comp (e.toLinearMap.comp p)
  let E₀ : V →ₗ[K] W := L + J.comp (e.toLinearMap.comp f.rangeRestrict - g.rangeRestrict.comp L)
  have hE₀ (v : V) : g.rangeRestrict (E₀ v) = e (f.rangeRestrict v) := by
    change g.rangeRestrict (L v + J (e (f.rangeRestrict v) - g.rangeRestrict (L v))) = _
    rw [map_add, hJ']
    abel
  have hE₀r (x : f.range) : E₀ x = (e x : W) := by
    have hp : p x = x := Submodule.projectionOnto_apply_left hU x
    change (e (p x) : W) + J (e (linearEndomorphismOnRange f x) -
      linearEndomorphismOnRange g (e (p x))) = (e x : W)
    rw [hp, he, sub_self, map_zero, add_zero]
  obtain ⟨U', hU'le, hU'⟩ := hP.exists_isCompl
  let q := P.projectionOnto U' hU'.symm
  let D := Q.subtype.comp eK.toLinearMap
  let F : V →ₗ[K] W := E₀ + (D - E₀.comp P.subtype).comp q
  have hFr (x : f.range) : F x = (e x : W) := by
    have hq : q x = 0 := Submodule.projectionOnto_apply_right hU'.symm ⟨x, hU'le x.property⟩
    change E₀ x + (D - E₀.comp P.subtype) (q x) = (e x : W)
    rw [hq, map_zero, add_zero, hE₀r]
  have hFp (x : P) : F x = (eK x : W) := by
    have hq : q x = x := Submodule.projectionOnto_apply_left hU'.symm x
    change E₀ x + (D - E₀.comp P.subtype) (q x) = (eK x : W)
    rw [hq]
    change E₀ x + ((eK x : W) - E₀ x) = (eK x : W)
    abel
  have hF (v : V) : g.rangeRestrict (F v) = e (f.rangeRestrict v) := by
    have hf0 : f.rangeRestrict (q v) = 0 := Subtype.ext (hPk (q v).property)
    have hg0 : g.rangeRestrict (D (q v)) = 0 := Subtype.ext (hQk (eK (q v)).property)
    change g.rangeRestrict (E₀ v + (D (q v) - E₀ (q v))) = _
    rw [map_add, map_sub, hE₀, hg0, hE₀, hf0, map_zero, sub_zero, add_zero]
  have hFinj : Function.Injective F := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro v hv
    have hfv : f.rangeRestrict v = 0 := by
      apply e.injective
      rw [map_zero, ← hF, mem_ker.mp hv, map_zero]
    have hvk : v ∈ f.ker := congrArg Subtype.val hfv
    rw [← hPs] at hvk
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hvk
    let a' : f.range := ⟨a, ha.1⟩
    let b' : P := ⟨b, hb⟩
    have hfa : F a = (e a' : W) := hFr a'
    have hfb : F b = (eK b' : W) := hFp b'
    have hzero : (e a' : W) + (eK b' : W) = 0 := by
      rw [← hfa, ← hfb, ← map_add]
      exact mem_ker.mp hv
    have hneg : (e a' : W) = -(eK b' : W) := eq_neg_of_add_eq_zero_left hzero
    have ha0 : (e a' : W) = 0 := Submodule.disjoint_def.mp hQ _ (e a').property
      (hneg ▸ Q.neg_mem (eK b').property)
    have hb0 : (eK b' : W) = 0 := by simpa only [ha0, zero_add] using hzero
    have ha' : a' = 0 := e.injective (by simpa only [map_zero] using Subtype.ext ha0)
    have hb' : b' = 0 := eK.injective (by simpa only [map_zero] using Subtype.ext hb0)
    exact (Submodule.mem_bot K).mpr (by
      change (a' : V) + (b' : V) = 0
      simp [ha', hb'])
  let E := LinearEquiv.ofBijective F
    ⟨hFinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hFinj⟩
  refine ⟨E, hFr, fun v => ?_⟩
  change F (f v) = g (F v)
  exact (hFr (f.rangeRestrict v)).trans (congrArg Subtype.val (hF v)).symm

theorem coe_linearEndomorphismOnRange_pow_apply (f : Module.End K V) (k : ℕ) (x : f.range) :
    (((linearEndomorphismOnRange f) ^ k) x : V) = (f ^ k) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ', Module.End.mul_apply, coe_linearEndomorphismOnRange_apply, ih]

theorem finrank_range_linearEndomorphismOnRange_pow (f : Module.End K V) (k : ℕ) :
    finrank K (LinearMap.range (linearEndomorphismOnRange f ^ k)) =
      finrank K (LinearMap.range (f ^ (k + 1))) := by
  have h : (LinearMap.range (linearEndomorphismOnRange f ^ k)).map f.range.subtype =
      LinearMap.range (f ^ (k + 1)) := by
    ext x
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      obtain ⟨u, hu⟩ := v.property
      refine ⟨u, ?_⟩
      change (f ^ (k + 1)) u = ((linearEndomorphismOnRange f ^ k) v : V)
      rw [pow_succ, Module.End.mul_apply, hu, coe_linearEndomorphismOnRange_pow_apply]
    · rintro ⟨u, rfl⟩
      let v := f.rangeRestrict u
      refine ⟨(linearEndomorphismOnRange f ^ k) v, ⟨v, rfl⟩, ?_⟩
      rw [Submodule.subtype_apply, coe_linearEndomorphismOnRange_pow_apply, pow_succ, Module.End.mul_apply]
      rfl
  rw [← h]
  exact (Submodule.equivMapOfInjective _ f.range.injective_subtype _).finrank_eq

private theorem isNilpotent_linearEndomorphismOnRange {f : Module.End K V} (hf : IsNilpotent f) :
    IsNilpotent (linearEndomorphismOnRange f) := by
  obtain ⟨k, hk⟩ := hf
  refine ⟨k, ?_⟩
  ext1 x
  apply Subtype.ext
  rw [coe_linearEndomorphismOnRange_pow_apply, hk]
  rfl

private theorem finrank_range_lt_of_isNilpotent [FiniteDimensional K V]
    {f : Module.End K V} (hf : IsNilpotent f) (hV : 0 < finrank K V) :
    finrank K f.range < finrank K V := by
  apply Submodule.finrank_lt
  intro hr
  obtain ⟨k, hk⟩ := hf
  have hs : Function.Surjective (f ^ k : Module.End K V) := by
    rw [Module.End.coe_pow]
    exact (LinearMap.range_eq_top.mp hr).iterate k
  rw [hk] at hs
  apply (Nat.ne_of_gt hV)
  apply finrank_zero_iff_forall_zero.mpr
  intro x
  obtain ⟨y, hy⟩ := hs x
  exact hy.symm

private theorem finrank_eq_of_finrank_range_pow_zero [FiniteDimensional K V] [FiniteDimensional K W]
    (f : Module.End K V) (g : Module.End K W)
    (h : finrank K (LinearMap.range (f ^ 0)) = finrank K (LinearMap.range (g ^ 0))) :
    finrank K V = finrank K W := by
  have hf : Function.Injective (f ^ (0 : ℕ) : Module.End K V) := by
    rw [pow_zero, Module.End.one_eq_id]
    exact Function.injective_id
  have hg : Function.Injective (g ^ (0 : ℕ) : Module.End K W) := by
    rw [pow_zero, Module.End.one_eq_id]
    exact Function.injective_id
  exact (LinearMap.finrank_range_of_inj hf).symm.trans
    (h.trans (LinearMap.finrank_range_of_inj hg))

/-- Nilpotent endomorphisms with the same ranks of powers up to the first space's dimension
are intertwined by a linear equivalence. The rank of the zeroth power compares the dimensions. -/
theorem exists_intertwiningLinearEquiv_of_nilpotent_rankPowers
    [FiniteDimensional K V] [FiniteDimensional K W] (f : Module.End K V) (g : Module.End K W)
    (hf : IsNilpotent f) (hg : IsNilpotent g)
    (h : ∀ k ≤ finrank K V,
      finrank K (LinearMap.range (f ^ k)) = finrank K (LinearMap.range (g ^ k))) :
    ∃ e : V ≃ₗ[K] W, ∀ v, e (f v) = g (e v) := by
  generalize hd : finrank K V = d at h ⊢
  induction d using Nat.strong_induction_on generalizing V W with
  | h d ih =>
    by_cases hd0 : d = 0
    · have hdim := finrank_eq_of_finrank_range_pow_zero f g (h 0 (Nat.zero_le _))
      let e : V ≃ₗ[K] W := LinearEquiv.ofFinrankEq _ _ hdim
      have hz : ∀ w : W, w = 0 := finrank_zero_iff_forall_zero.mp (hdim.symm.trans (hd.trans hd0))
      exact ⟨e, fun v => (hz _).trans (hz _).symm⟩
    · have hlt : finrank K f.range < d :=
        hd ▸ finrank_range_lt_of_isNilpotent hf (hd.symm ▸ Nat.pos_of_ne_zero hd0)
      have hR (k : ℕ) (hk : k ≤ finrank K f.range) :
          finrank K (LinearMap.range (linearEndomorphismOnRange f ^ k)) =
            finrank K (LinearMap.range (linearEndomorphismOnRange g ^ k)) := by
        rw [finrank_range_linearEndomorphismOnRange_pow, finrank_range_linearEndomorphismOnRange_pow]
        exact h (k + 1) (Nat.succ_le_of_lt (hk.trans_lt hlt))
      obtain ⟨e, he⟩ := ih (finrank K f.range) hlt (linearEndomorphismOnRange f)
        (linearEndomorphismOnRange g) (isNilpotent_linearEndomorphismOnRange hf)
        (isNilpotent_linearEndomorphismOnRange hg) rfl hR
      have hdim := finrank_eq_of_finrank_range_pow_zero f g (h 0 (Nat.zero_le _))
      obtain ⟨E, _, hE⟩ := exists_intertwiningLinearEquiv_of_range f g hdim e he
      exact ⟨E, hE⟩

end Langlands

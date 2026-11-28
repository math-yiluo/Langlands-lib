import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Nilpotent endomorphism conjugacy from the ranks of powers -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Function LinearMap Module

universe u v

variable {D : Type u} [DivisionRing D]
  {V V' : Type v} [AddCommGroup V] [Module D V] [AddCommGroup V'] [Module D V']

private def rangeRestriction (f : End D V) : End D f.range :=
  f.rangeRestrict.comp f.range.subtype

private theorem rangeRestriction_pow_apply (f : End D V) (m : ℕ) (x : f.range) :
    ((rangeRestriction f ^ m) x : V) = (f ^ m) x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    change f (((rangeRestriction f ^ m) x : f.range) : V) = f ((f ^ m) x)
    rw [ih]

private theorem finrank_rangeRestriction_pow (f : End D V) (m : ℕ) :
    finrank D (range (rangeRestriction f ^ m)) = finrank D (range (f ^ (m + 1))) := by
  have hcomp :
      f.range.subtype.comp ((rangeRestriction f ^ m).comp f.rangeRestrict) = f ^ (m + 1) := by
    ext x
    change ((rangeRestriction f ^ m) (f.rangeRestrict x) : V) = (f ^ (m + 1)) x
    rw [rangeRestriction_pow_apply, pow_succ, Module.End.mul_apply]
    rfl
  have hmap : (range (rangeRestriction f ^ m)).map f.range.subtype = range (f ^ (m + 1)) := by
    rw [← range_comp, ← range_comp_of_range_eq_top _ (range_rangeRestrict f),
      LinearMap.comp_assoc, hcomp]
  rw [← hmap]
  exact (Submodule.equivMapOfInjective _ f.range.subtype_injective _).finrank_eq

/-- Splitting the image and kernel presents an endomorphism by a restriction and a lift
of a complement of the image of that restriction. -/
private theorem exists_rangeCoordinates (f : End D V)
    {W : Type v} [AddCommGroup W] [Module D W] (i : W →ₗ[D] f.range)
    (hi : Injective i) (hW : IsCompl (range (rangeRestriction f)) i.range) :
    ∃ Z : Submodule D (ker f), ∃ E : (f.range × W × Z) ≃ₗ[D] V,
      ∀ x, f (E x) = E (rangeRestriction f x.1 + i x.2.1, 0, 0) := by
  let P := f.range
  let K := ker f
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective (range_rangeRestrict f)
  have hsi (w : W) : f.rangeRestrict (s (i w)) = i w :=
    DFunLike.congr_fun hs (i w)
  obtain ⟨Z, hZ⟩ := (P.comap K.subtype).exists_isCompl
  let E : (P × W × Z) →ₗ[D] V :=
    P.subtype.coprod ((s.comp i).coprod (K.subtype.comp Z.subtype))
  have hE (p : P) (w : W) (z : Z) : E (p, w, z) = (p : V) + (s (i w) + (z.1 : V)) := rfl
  have hz0 (z : Z) : f (z.1 : V) = 0 := z.1.property
  have hn (p : P) (w : W) (z : Z) : f.rangeRestrict (E (p, w, z)) =
      rangeRestriction f p + i w := by
    have hz : f.rangeRestrict (z.1 : V) = 0 := Subtype.ext (hz0 z)
    rw [hE, map_add, map_add, hsi, hz, add_zero]
    rfl
  have hinj : Injective E := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    rintro ⟨p, w, z⟩ hx
    have hzero : E (p, w, z) = 0 := mem_ker.mp hx
    have hpw := hn p w z
    rw [hzero, map_zero, eq_comm, add_eq_zero_iff_eq_neg] at hpw
    have hw : i w = 0 := Submodule.disjoint_def.mp hW.disjoint.symm (i w)
      (mem_range_self i w) (by rw [← neg_neg (i w), ← hpw]; exact Submodule.neg_mem _ (mem_range_self _ _))
    have hw' : w = 0 := i.map_eq_zero_iff hi |>.mp hw
    rw [hE, hw', map_zero, map_zero, zero_add, add_eq_zero_iff_eq_neg] at hzero
    have hz : z.1 = 0 := Submodule.disjoint_def.mp hZ.disjoint.symm z.1 z.2 (by
      change (z.1 : V) ∈ P
      rw [← neg_neg (z.1 : V), ← hzero]
      exact P.neg_mem p.property)
    have hz' : z = 0 := Subtype.ext hz
    rw [hz', Submodule.coe_zero, Submodule.coe_zero, neg_zero] at hzero
    have hp : p = 0 := Subtype.ext hzero
    simp [hp, hw', hz']
  have hsurj : Surjective E := by
    intro x
    obtain ⟨a, b, hab, _⟩ := (range (rangeRestriction f)).existsUnique_add_of_isCompl hW
      (f.rangeRestrict x)
    obtain ⟨p, hp⟩ := a.property
    obtain ⟨w, hw⟩ := b.property
    have heq : rangeRestriction f p + i w = f.rangeRestrict x := by
      rwa [hp, hw]
    let r : K := ⟨x - (p : V) - s (i w), by
      apply mem_ker.mpr
      have h := congrArg Subtype.val heq
      change f p + (i w : V) = f x at h
      have h' : f (s (i w)) = (i w : V) := congrArg Subtype.val (hsi w)
      simp only [map_sub, h', ← h, add_sub_cancel_left, sub_self]⟩
    obtain ⟨q, z, hqz, _⟩ := (P.comap K.subtype).existsUnique_add_of_isCompl hZ r
    have hq : (q.1 : V) ∈ P := q.property
    have hr := congrArg (fun x : K => (x : V)) hqz
    change (q.1 : V) + (z.1 : V) = x - (p : V) - s (i w) at hr
    refine ⟨(p + ⟨(q.1 : V), hq⟩, w, z), ?_⟩
    rw [hE, Submodule.coe_add]
    change (p : V) + (q.1 : V) + (s (i w) + (z.1 : V)) = x
    rw [show (p : V) + (q.1 : V) + (s (i w) + (z.1 : V)) =
      (q.1 : V) + (z.1 : V) + (p : V) + s (i w) by abel, hr]
    abel
  refine ⟨Z, LinearEquiv.ofBijective E ⟨hinj, hsurj⟩, ?_⟩
  rintro ⟨p, w, z⟩
  change f (E (p, w, z)) = E (rangeRestriction f p + i w, 0, 0)
  rw [hE (rangeRestriction f p + i w) 0 0, map_zero, map_zero]
  simp only [Submodule.coe_zero, add_zero]
  exact congrArg Subtype.val (hn p w z)

private theorem finrank_range_pow_zero (f : End D V) :
    finrank D (range (f ^ (0 : ℕ))) = finrank D V := by
  have hf : f ^ (0 : ℕ) = LinearMap.id := pow_zero f
  rw [hf, range_id, finrank_top]

private theorem exists_intertwiningEquiv_of_pow_eq_zero
    (n : ℕ) :
    ∀ {V V' : Type v} [AddCommGroup V] [Module D V] [FiniteDimensional D V]
      [AddCommGroup V'] [Module D V'] [FiniteDimensional D V']
      (f : End D V) (g : End D V'), f ^ n = 0 → g ^ n = 0 →
      (∀ m : ℕ, finrank D (range (f ^ m)) = finrank D (range (g ^ m))) →
        ∃ e : V ≃ₗ[D] V', ∀ x, e (f x) = g (e x) := by
  induction n with
  | zero =>
    intro V V' _ _ _ _ _ _ f g hf hg hr
    have hV' : Subsingleton V' := by
      refine ⟨fun x y => ?_⟩
      simpa using (DFunLike.congr_fun hg x).trans (DFunLike.congr_fun hg y).symm
    have hdim : finrank D V = finrank D V' := by
      simpa only [finrank_range_pow_zero] using hr 0
    exact ⟨LinearEquiv.ofFinrankEq _ _ hdim, fun _ => Subsingleton.elim _ _⟩
  | succ n ih =>
    intro V V' _ _ _ _ _ _ f g hf hg hr
    have hpow {U : Type v} [AddCommGroup U] [Module D U] (h : End D U)
        (hz : h ^ (n + 1) = 0) : rangeRestriction h ^ n = 0 := by
      ext x
      obtain ⟨y, hy⟩ := x.property
      change ((rangeRestriction h ^ n) x : U) = 0
      rw [rangeRestriction_pow_apply, ← hy, ← Module.End.mul_apply, ← pow_succ, hz]
      rfl
    obtain ⟨e, he⟩ := ih (rangeRestriction f) (rangeRestriction g) (hpow f hf) (hpow g hg)
      (fun m => by rw [finrank_rangeRestriction_pow, finrank_rangeRestriction_pow, hr])
    have himage : (range (rangeRestriction f)).map e.toLinearMap = range (rangeRestriction g) := by
      ext x
      constructor
      · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
        exact ⟨e y, (he y).symm⟩
      · rintro ⟨y, rfl⟩
        obtain ⟨x, rfl⟩ := e.surjective y
        exact ⟨rangeRestriction f x, mem_range_self _ x, he x⟩
    obtain ⟨W, hW⟩ := (range (rangeRestriction f)).exists_isCompl
    have hW' : IsCompl (range (rangeRestriction g)) (range (e.toLinearMap.comp W.subtype)) := by
      rw [range_comp, Submodule.range_subtype, ← himage]
      exact Submodule.isCompl_map e hW
    obtain ⟨Z, E, hE⟩ := exists_rangeCoordinates f W.subtype W.subtype_injective (by simpa using hW)
    obtain ⟨Z', E', hE'⟩ := exists_rangeCoordinates g (e.toLinearMap.comp W.subtype)
      (e.injective.comp W.subtype_injective) hW'
    have hdim : finrank D V = finrank D V' := by
      simpa only [finrank_range_pow_zero] using hr 0
    have hz : finrank D Z = finrank D Z' := by
      have h := E.finrank_eq
      have h' := E'.finrank_eq
      simp only [Module.finrank_prod] at h h'
      have he' := e.finrank_eq
      omega
    let eZ : Z ≃ₗ[D] Z' := LinearEquiv.ofFinrankEq _ _ hz
    let eprod := e.prodCongr ((LinearEquiv.refl D W).prodCongr eZ)
    refine ⟨E.symm.trans (eprod.trans E'), ?_⟩
    intro x
    obtain ⟨⟨p, w, z⟩, rfl⟩ := E.surjective x
    rw [hE]
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [hE']
    congr 1
    change (e (rangeRestriction f p + (w : f.range)), (0 : W), eZ 0) =
      (rangeRestriction g (e p) + e (w : f.range), 0, 0)
    simp only [map_add, he, map_zero]

/-- Nilpotent endomorphisms whose powers have the same ranks are linearly conjugate.
The coefficient division ring can be noncommutative. -/
theorem exists_intertwiningEquiv_of_nilpotent_rank_powers
    [FiniteDimensional D V] [FiniteDimensional D V']
    (f : End D V) (g : End D V') (hf : IsNilpotent f) (hg : IsNilpotent g)
    (hr : ∀ m : ℕ, finrank D (range (f ^ m)) = finrank D (range (g ^ m))) :
    ∃ e : V ≃ₗ[D] V', ∀ x, e (f x) = g (e x) := by
  obtain ⟨m, hm⟩ := hf
  obtain ⟨n, hn⟩ := hg
  exact exists_intertwiningEquiv_of_pow_eq_zero (m + n) f g
    (by rw [pow_add, hm, zero_mul]) (by rw [pow_add, hn, mul_zero]) hr

end Langlands.HarmonicAnalysis.UnitConjugation

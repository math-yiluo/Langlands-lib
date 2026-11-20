import Langlands.BaseChange.Norm
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.RingTheory.Artinian.Instances

/-! # Residue-field coordinates for a cyclic algebra -/

namespace Langlands.BaseChange

universe u v

noncomputable section
open Matrix

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E]

namespace CyclicAlgebraStructure

/-- Pullback of maximal ideals along an automorphism. -/
private def pullback (σ : E ≃ₐ[F] E) : Equiv.Perm (MaximalSpectrum E) where
  toFun I := ⟨I.asIdeal.comap σ.toRingHom,
    Ideal.comap_isMaximal_of_surjective _ σ.surjective⟩
  invFun I := ⟨I.asIdeal.comap σ.symm.toRingHom,
    Ideal.comap_isMaximal_of_surjective _ σ.symm.surjective⟩
  left_inv I := by
    apply MaximalSpectrum.ext
    ext x
    change σ (σ.symm x) ∈ I.asIdeal ↔ x ∈ I.asIdeal
    rw [σ.apply_symm_apply]
  right_inv I := by
    apply MaximalSpectrum.ext
    ext x
    change σ.symm (σ x) ∈ I.asIdeal ↔ x ∈ I.asIdeal
    rw [σ.symm_apply_apply]

private theorem pullback_pow (σ : E ≃ₐ[F] E) (i : ℕ) (I : MaximalSpectrum E) :
    ((pullback σ ^ i) I).asIdeal = I.asIdeal.comap (σ ^ i).toRingHom := by
  induction i generalizing I with
  | zero =>
    simp only [pow_zero, Equiv.Perm.one_apply]
    exact (Ideal.comap_id _).symm
  | succ i ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ']
    rfl

private theorem nontrivial_of_cyclic {σ : E ≃ₐ[F] E} {l : ℕ}
    (h : IsCyclicAlgebra σ l) : Nontrivial E := by
  let : Module.Finite F E := h.1
  by_contra! he
  have hz : Module.finrank F E = 0 := Module.finrank_zero_of_subsingleton
  exact h.pos.ne' (h.2.1.symm.trans hz)

private theorem pullback_isCycleOn [IsArtinianRing E] [IsReduced E]
    (σ : E ≃ₐ[F] E) (hfix : ∀ x, σ x = x → x ∈ (algebraMap F E).range) :
    (pullback σ).IsCycleOn Set.univ := by
  classical
  refine ⟨(pullback σ).bijective.bijOn_univ, fun m _ n _ => ?_⟩
  let p := pullback σ
  let e := IsArtinianRing.equivPi E
  let x := e.symm (fun j => if p.SameCycle m j then 1 else 0)
  have hx (j : MaximalSpectrum E) : Ideal.Quotient.mk j.asIdeal x =
      if p.SameCycle m j then 1 else 0 := congrFun (e.apply_symm_apply _) j
  have hσx : σ x = x := by
    apply e.injective
    funext j
    change Ideal.Quotient.mk j.asIdeal (σ x) = Ideal.Quotient.mk j.asIdeal x
    rw [hx]
    by_cases hj : p.SameCycle m j
    · simp only [hj, ite_true]
      have hj' := (Equiv.Perm.sameCycle_apply_right (f := p)).2 hj
      have h := hx (p j)
      rw [ite_eq_left hj', ← map_one (Ideal.Quotient.mk (p j).asIdeal),
        ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem] at h
      have hh : σ (x - 1) ∈ j.asIdeal := h
      rw [map_sub, map_one] at hh
      rw [← map_one (Ideal.Quotient.mk j.asIdeal), ← sub_eq_zero, ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hh
    · simp only [hj, ite_false]
      have hj' : ¬p.SameCycle m (p j) := fun h => hj (Equiv.Perm.sameCycle_apply_right.mp h)
      have h := hx (p j)
      rw [ite_eq_right hj', Ideal.Quotient.eq_zero_iff_mem] at h
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h
  obtain ⟨a, ha⟩ := hfix x hσx
  let : m.asIdeal.IsMaximal := m.isMaximal
  have ha' : a = 1 := (algebraMap F (E ⧸ m.asIdeal)).injective (by
    rw [map_one]
    change Ideal.Quotient.mk m.asIdeal (algebraMap F E a) = 1
    rw [ha, hx, ite_eq_left (Equiv.Perm.SameCycle.refl p m)])
  have h1 : x = 1 := by rw [← ha, ha', map_one]
  by_contra hn
  have h := hx n
  rw [ite_eq_right hn, h1, map_one] at h
  let : n.asIdeal.IsMaximal := n.isMaximal
  exact one_ne_zero h

/-- The decomposition data used by the norm reduction. The coordinates are numbered by
successive powers of `σ`, with `τ` acting at the wraparound. -/
structure Coordinates (σ : E ≃ₐ[F] E) (l : ℕ) where
  m : MaximalSpectrum E
  r : ℕ
  d : ℕ
  r_pos : 0 < r
  degree_eq : l = r * d
  τ : (E ⧸ m.asIdeal) ≃ₐ[F] (E ⧸ m.asIdeal)
  cyclic : IsCyclicAlgebra τ d
  coords : E ≃ₐ[F] (Fin r → E ⧸ m.asIdeal)
  coords_apply (i : Fin r) (x : E) : coords x i = Ideal.Quotient.mk m.asIdeal ((σ ^ i.val) x)
  wrap (x : E) : Ideal.Quotient.mk m.asIdeal ((σ ^ r) x) = τ (Ideal.Quotient.mk m.asIdeal x)

/-- A finite reduced cyclic algebra is a product of copies of one cyclic field extension. -/
theorem exists_coordinates {σ : E ≃ₐ[F] E} {l : ℕ} (h : IsCyclicAlgebra σ l) :
    Nonempty (Coordinates σ l) := by
  classical
  have : Module.Finite F E := h.1
  have : IsReduced E := h.2.2.1
  have : Nontrivial E := nontrivial_of_cyclic h
  have : IsArtinianRing E := isArtinian_of_tower F (inferInstance : IsArtinian F E)
  let m : MaximalSpectrum E := Classical.choice inferInstance
  let : m.asIdeal.IsMaximal := m.isMaximal
  let L := E ⧸ m.asIdeal
  let q : E →ₐ[F] L := Ideal.Quotient.mkₐ F m.asIdeal
  have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective F _
  let : Fintype (MaximalSpectrum E) := Fintype.ofFinite _
  let p := pullback σ
  let r := Fintype.card (MaximalSpectrum E)
  have hr : 0 < r := Fintype.card_pos
  have hc : p.IsCycleOn (↑(Finset.univ : Finset (MaximalSpectrum E))) := by
    simpa only [Finset.coe_univ] using pullback_isCycleOn σ h.2.2.2.2
  have hm : m ∈ (Finset.univ : Finset (MaximalSpectrum E)) := Finset.mem_univ m
  have hperiod (k : ℕ) : (p ^ k) m = m ↔ r ∣ k := by
    simpa only [Finset.card_univ] using hc.pow_apply_eq hm (n := k)
  have hrdvd : r ∣ l := (hperiod l).1 (by
    apply MaximalSpectrum.ext
    rw [pullback_pow, h.pow_eq_one]
    exact Ideal.comap_id _)
  have hrdvd_order : r ∣ orderOf σ := h.2.2.2.1.symm ▸ hrdvd
  obtain ⟨d, hd⟩ := hrdvd
  let orbit : Fin r ≃ MaximalSpectrum E :=
    Equiv.ofBijective (fun i => (p ^ i.val) m) ⟨by
      intro i j hij
      apply Fin.ext
      have heq := (hc.pow_apply_eq_pow_apply hm).mp hij
      change i.val % r = j.val % r at heq
      simpa only [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using heq,
      by
        intro j
        obtain ⟨k, hk, heq⟩ := hc.exists_pow_eq hm (Finset.mem_univ j)
        exact ⟨⟨k, hk⟩, heq⟩⟩
  have hmap (i : ℕ) :
      m.asIdeal = ((p ^ i) m).asIdeal.map (σ ^ i).toRingHom := by
    rw [pullback_pow]
    exact (Ideal.map_comap_of_surjective _ (σ ^ i).surjective _).symm
  let e := ((IsArtinianRing.equivPi E).restrictScalars F).trans
    ((AlgEquiv.piCongrLeft F (fun j : MaximalSpectrum E => E ⧸ j.asIdeal) orbit).symm.trans
      (AlgEquiv.piCongrRight (fun i : Fin r =>
        Ideal.quotientEquivAlg (orbit i).asIdeal m.asIdeal (σ ^ i.val) (hmap i.val))))
  have he (i : Fin r) (x : E) : e x i = q ((σ ^ i.val) x) := rfl
  let τ : L ≃ₐ[F] L := Ideal.quotientEquivAlg m.asIdeal m.asIdeal (σ ^ r)
    (by
      change m.asIdeal = m.asIdeal.map (σ ^ r).toRingHom
      have ht := hmap r
      rwa [(hperiod r).2 dvd_rfl] at ht)
  have hτ (x : E) : q ((σ ^ r) x) = τ (q x) := rfl
  have hτpow (k : ℕ) (x : E) : q (((σ ^ r) ^ k) x) = (τ ^ k) (q x) := by
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτ, ih]
  have hpow (k : ℕ) : τ ^ k = 1 ↔ (σ ^ r) ^ k = 1 := by
    constructor
    · intro hk
      ext x
      apply e.injective
      funext i
      rw [he, he]
      change q ((σ ^ i.val) (((σ ^ r) ^ k) x)) = q ((σ ^ i.val) x)
      rw [← AlgEquiv.mul_apply, ← pow_mul, ← pow_add, add_comm i.val, pow_add,
        AlgEquiv.mul_apply, pow_mul, hτpow, hk]
      rfl
    · intro hk
      ext y
      obtain ⟨x, rfl⟩ := hq y
      rw [← hτpow, hk]
      rfl
  have hord : orderOf τ = d := by
    have hs : orderOf (σ ^ r) = d := by
      rw [orderOf_pow_of_dvd hr.ne' hrdvd_order, h.2.2.2.1, hd,
        Nat.mul_div_cancel_left _ hr]
    apply Nat.dvd_antisymm
    · exact orderOf_dvd_of_pow_eq_one ((hpow d).2 (hs ▸ pow_orderOf_eq_one (σ ^ r)))
    · rw [← hs]
      exact orderOf_dvd_of_pow_eq_one ((hpow _).1 (pow_orderOf_eq_one τ))
  have hfin : Module.Finite F L := Module.Finite.of_surjective q.toLinearMap hq
  have hrank : Module.finrank F L = d := by
    have heq := e.toLinearEquiv.finrank_eq
    rw [h.2.1, hd, Module.finrank_pi_fintype] at heq
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at heq
    exact (Nat.eq_of_mul_eq_mul_left hr heq).symm
  have hfix (z : L) (hz : τ z = z) : z ∈ (algebraMap F L).range := by
    obtain ⟨x, hx⟩ := e.surjective (fun _ => z)
    have hcoord (i : Fin r) : q ((σ ^ i.val) x) = z := (he i x).symm.trans (congrFun hx i)
    let start : Fin r := ⟨0, hr⟩
    have hzero : q x = z := hcoord start
    have hσx : σ x = x := by
      apply e.injective
      funext i
      rw [he, he, hcoord, ← AlgEquiv.mul_apply, ← pow_succ]
      by_cases hi : i.val + 1 < r
      · exact hcoord ⟨i.val + 1, hi⟩
      · have hi' : i.val + 1 = r := by omega
        rw [hi', hτ, hzero, hz]
    obtain ⟨a, ha⟩ := h.2.2.2.2 x hσx
    exact ⟨a, (q.commutes a).symm.trans ((congrArg q ha).trans hzero)⟩
  exact ⟨⟨m, r, d, hr, hd, τ, ⟨hfin, hrank, inferInstance, hord, hfix⟩, e, he, hτ⟩⟩

end CyclicAlgebraStructure
end
end Langlands.BaseChange

import Langlands.GroupScheme.Dilatation.Algebra
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Polynomial.Quotient

/-! # Regularity of the denominator in polynomial dilatation charts -/

noncomputable section

open RingTheory.Sequence

namespace Langlands.GroupScheme.Dilatation

variable {A : Type*} [CommRing A]

private def quotSmulEquiv (I : Ideal A) :
    (A ⧸ (I • (⊤ : Submodule A A) : Submodule A A)) ≃ₗ[A] (A ⧸ I) :=
  Submodule.quotEquivOfEq _ _ (by
    change I • (⊤ : Ideal A) = I
    rw [Ideal.smul_eq_mul, Ideal.mul_top])

private def quotPrincipalEquiv (a : A) :
    QuotSMulTop a A ≃ₗ[A] (A ⧸ Ideal.span {a}) :=
  (Submodule.quotEquivOfEq _ _ (Submodule.ideal_span_singleton_smul a _).symm).trans
    (quotSmulEquiv (Ideal.span {a}))

/-- Regular sequences on a ring, expressed using actual ring quotients. -/
private theorem weaklyRegular_cons_quot (a : A) (xs : List A) :
    IsWeaklyRegular A (a :: xs) ↔ IsSMulRegular A a ∧
      IsWeaklyRegular (A ⧸ Ideal.span {a}) (xs.map (Ideal.Quotient.mk (Ideal.span {a}))) := by
  rw [isWeaklyRegular_cons_iff, (quotPrincipalEquiv a).isWeaklyRegular_congr]
  exact and_congr_right' (isWeaklyRegular_map_algebraMap_iff (A ⧸ Ideal.span {a}) _ xs).symm

private theorem weaklyRegular_map_ringEquiv {B : Type*} [CommRing B] (e : A ≃+* B)
    (xs : List A) : IsWeaklyRegular A xs ↔ IsWeaklyRegular B (xs.map e) :=
  e.toAddEquiv.isWeaklyRegular_congr <| List.forall₂_map_right_iff.mpr <|
    List.forall₂_same.mpr fun r _ x => e.map_mul r x

private theorem quotient_eq_iff (I : Ideal A) (x y : A) :
    Ideal.Quotient.mk I x = Ideal.Quotient.mk I y ↔ x - y ∈ I := by
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]

/-- If `t` is regular and `x` is regular modulo `t`, then `t` remains regular modulo `x`. -/
private theorem regular_quotient_of_regular_mod {t x : A} (ht : IsSMulRegular A t)
    (hx : IsSMulRegular (A ⧸ Ideal.span {t}) (Ideal.Quotient.mk (Ideal.span {t}) x)) :
    IsSMulRegular (A ⧸ Ideal.span {x}) (Ideal.Quotient.mk (Ideal.span {x}) t) := by
  intro a b h
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  change Ideal.Quotient.mk (Ideal.span {x}) t * Ideal.Quotient.mk _ a =
    Ideal.Quotient.mk _ t * Ideal.Quotient.mk _ b at h
  rw [← map_mul, ← map_mul] at h
  have hsub := (quotient_eq_iff (Ideal.span {x}) _ _).mp h
  rw [← mul_sub] at hsub
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hsub
  have hc0 : Ideal.Quotient.mk (Ideal.span {t}) c = 0 := by
    apply hx
    change Ideal.Quotient.mk (Ideal.span {t}) x * Ideal.Quotient.mk _ c = _ * 0
    rw [← map_mul, ← hc, map_mul, mul_zero,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton t)), zero_mul]
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hc0)
  apply (quotient_eq_iff _ _ _).mpr
  refine Ideal.mem_span_singleton.mpr ⟨d, ht ?_⟩
  change t * (a - b) = t * (x * d)
  rw [hc, hd]
  ring

/-- The two orders of quotienting by principal ideals agree on every old element. -/
private def principalQuotientComm (x t : A) :
    ((A ⧸ Ideal.span {t}) ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {t}) x}) ≃+*
      ((A ⧸ Ideal.span {x}) ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {x}) t}) :=
  (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
    ((DoubleQuot.quotQuotEquivComm (Ideal.span {t}) (Ideal.span {x})).trans
      (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])))

/-- A scalar stays regular after quotient by a list of equations whose reductions
form a weakly regular sequence modulo the scalar. -/
theorem regular_quotient_ofList_of_regular_mod (t : A) (xs : List A) (ht : IsSMulRegular A t)
    (h : IsWeaklyRegular (A ⧸ Ideal.span {t}) (xs.map (Ideal.Quotient.mk (Ideal.span {t})))) :
    IsSMulRegular (A ⧸ Ideal.ofList xs) (Ideal.Quotient.mk (Ideal.ofList xs) t) := by
  generalize hn : xs.length = n
  induction n generalizing A with
  | zero =>
    have hnil : xs = [] := List.length_eq_zero_iff.mp hn
    subst xs
    let e : (A ⧸ Ideal.ofList ([] : List A)) ≃+* A :=
      (Ideal.quotEquivOfEq Ideal.ofList_nil).trans (RingEquiv.quotientBot A)
    apply (e.toEquiv.isSMulRegular_congr (r := Ideal.Quotient.mk _ t) (s := t) ?_).mpr ht
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    change e (Ideal.Quotient.mk _ t * Ideal.Quotient.mk _ z) = t * e (Ideal.Quotient.mk _ z)
    simp only [map_mul, e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, RingEquiv.quotientBot_mk]
  | succ n ih =>
    have hne : xs ≠ [] := by intro he; simp [he] at hn
    obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hn' : xs.length = n := Nat.succ.inj hn
    let J : Ideal A := Ideal.span {x}
    let A' := A ⧸ J
    let q := Ideal.Quotient.mk J
    have ht' : IsSMulRegular A' (q t) :=
      regular_quotient_of_regular_mod ht ((weaklyRegular_cons_quot _ _).mp h).1
    have hx := ((weaklyRegular_cons_quot _ _).mp h).2
    have hx' : IsWeaklyRegular (A' ⧸ Ideal.span {q t})
        ((xs.map q).map (Ideal.Quotient.mk (Ideal.span {q t}))) := by
      have hc := (weaklyRegular_map_ringEquiv (principalQuotientComm x t) _).mp hx
      convert hc using 1
      simp only [List.map_map]
      congr 1
    have hh := ih (q t) (xs.map q) ht' hx' (by simpa only [List.length_map] using hn')
    let e : (A' ⧸ Ideal.ofList (xs.map q)) ≃+* (A ⧸ Ideal.ofList (x :: xs)) :=
      (Ideal.quotEquivOfEq (by rw [Ideal.map_ofList])).trans
        ((DoubleQuot.quotQuotEquivQuotSup J (Ideal.ofList xs)).trans
          (Ideal.quotEquivOfEq (by rw [Ideal.ofList_cons])))
    refine (e.toEquiv.isSMulRegular_congr ?_).mp hh
    intro z
    have e_t : e (Ideal.Quotient.mk (Ideal.ofList (xs.map q)) (q t)) =
        Ideal.Quotient.mk (Ideal.ofList (x :: xs)) t := by
      simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
      change Ideal.quotEquivOfEq _ (DoubleQuot.quotQuotEquivQuotSup J (Ideal.ofList xs)
        (DoubleQuot.quotQuotMk J (Ideal.ofList xs) t)) = _
      rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotEquivOfEq_mk]
    change e (_ * z) = _ * e z
    rw [map_mul, e_t]

end Langlands.GroupScheme.Dilatation

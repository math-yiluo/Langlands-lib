import Mathlib

/-!
# Root multiplicities of resultants along power-series branches

Let `fh, A ∈ F[X][Y]` and `x ∈ F`. Substituting `X = x + T` gives polynomials in `Y` over
`L⟦T⟧` for any field extension `L / F`. If `S` is a finite set of roots of `fh(x + T, Y)` in
`L⟦T⟧` and `A(x + T, Φ)` is divisible by `T^M` for every `Φ ∈ S`, then the resultant
`Res_Y(fh, A)` vanishes at `x` to order at least `M · #S`.
-/

noncomputable section

open Polynomial

namespace Langlands.AlgebraicGeometry.LangWeil.Stepanov

variable {F : Type*} [Field F]

/-- The substitution `p(X) ↦ p(x + T)`, valued in `L⟦T⟧`. -/
def iota (L : Type*) [Field L] [Algebra F L] (x : F) : Polynomial F →+* PowerSeries L :=
  Polynomial.eval₂RingHom ((PowerSeries.C (R := L)).comp (algebraMap F L))
    (PowerSeries.C (algebraMap F L x) + PowerSeries.X)

variable {L : Type*} [Field L] [Algebra F L]

theorem iota_C (x a : F) : iota L x (C a) = PowerSeries.C (algebraMap F L a) := by
  simp [iota]

theorem iota_X (x : F) : iota L x X = PowerSeries.C (algebraMap F L x) + PowerSeries.X := by
  simp [iota]

theorem iota_eq (x : F) (p : Polynomial F) :
    iota L x p =
      PowerSeries.map (algebraMap F L) ((taylor x p : Polynomial F) : PowerSeries F) := by
  have h : iota L x = (PowerSeries.map (algebraMap F L)).comp
      ((Polynomial.coeToPowerSeries.ringHom (R := F)).comp (taylorAlgHom x).toRingHom) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [iota, Polynomial.coeToPowerSeries.ringHom]
    · simp [iota, Polynomial.coeToPowerSeries.ringHom, add_comm]
  rw [h]
  rfl

theorem iota_injective (x : F) : Function.Injective (iota L x) := by
  intro p p' h
  rw [iota_eq, iota_eq] at h
  have h2 := PowerSeries.map_injective (algebraMap F L) (algebraMap F L).injective h
  have h3 : taylor x p = taylor x p' := Polynomial.coe_inj.mp h2
  exact taylor_injective x h3

theorem le_rootMultiplicity_of_X_pow_dvd_iota (x : F) {p : Polynomial F} (hp : p ≠ 0) {k : ℕ}
    (h : PowerSeries.X ^ k ∣ iota L x p) : k ≤ p.rootMultiplicity x := by
  rw [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply]
  have ht : taylor x p ≠ 0 := fun h0 => hp (taylor_injective x (h0.trans (map_zero _).symm))
  apply le_natTrailingDegree ht
  intro i hi
  rw [iota_eq, PowerSeries.X_pow_dvd_iff] at h
  have := h i hi
  rw [PowerSeries.coeff_map, Polynomial.coeff_coe] at this
  exact (algebraMap F L).injective (by rw [this, map_zero])

/-- **Multiplicity of a resultant along branches.** If every `Φ ∈ S` is a root of
`fh(x + T, Y)` and `T^M` divides `A(x + T, Φ)`, then `Res_Y(fh, A)` (Sylvester sizes
`natDegree fh` and `D ≥ natDegree A`) has a root of multiplicity at least `M · #S` at `x`,
provided it is nonzero. -/
theorem mul_card_le_rootMultiplicity_resultant (x : F) (fh A : Polynomial (Polynomial F))
    (D M : ℕ) (S : Finset (PowerSeries L)) (hfh : fh ≠ 0) (hA : A.natDegree ≤ D)
    (hres : resultant fh A fh.natDegree D ≠ 0)
    (hroot : ∀ Φ ∈ S, (fh.map (iota L x)).eval Φ = 0)
    (hvan : ∀ Φ ∈ S, PowerSeries.X ^ M ∣ (A.map (iota L x)).eval Φ) :
    M * S.card ≤ (resultant fh A fh.natDegree D).rootMultiplicity x := by
  classical
  apply le_rootMultiplicity_of_X_pow_dvd_iota (L := L) x hres
  have hinj := iota_injective (L := L) x
  set P := fh.map (iota L x) with hPdef
  set A' := A.map (iota L x) with hA'def
  have hA' : A'.natDegree ≤ D := (natDegree_map_le).trans hA
  have hPdeg : P.natDegree = fh.natDegree := natDegree_map_eq_of_injective hinj _
  have hP0 : P ≠ 0 := (Polynomial.map_ne_zero_iff hinj).2 hfh
  set Q : Polynomial (PowerSeries L) := ∏ Φ ∈ S, (X - C Φ) with hQdef
  have hQdvd : Q ∣ P := by
    have hle : S.val ≤ P.roots :=
      (Multiset.le_iff_subset S.nodup).2 fun Φ hΦ => (mem_roots hP0).2 (hroot Φ hΦ)
    calc Q = (S.val.map fun Φ => X - C Φ).prod := rfl
      _ ∣ (P.roots.map fun Φ => X - C Φ).prod :=
        Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hle)
      _ ∣ P := prod_multiset_X_sub_C_dvd P
  obtain ⟨R, hR⟩ := hQdvd
  have hQmonic : Q.Monic := monic_prod_of_monic _ _ fun Φ _ => monic_X_sub_C Φ
  have hQdeg : Q.natDegree = S.card := by
    rw [hQdef, natDegree_prod_of_monic _ _ fun Φ _ => monic_X_sub_C Φ]
    simp
  have hR0 : R ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hR
    exact hP0 hR
  have hdeg : fh.natDegree = Q.natDegree + R.natDegree := by
    rw [← hPdeg, hR, hQmonic.natDegree_mul' hR0]
  have hprod : resultant Q A' Q.natDegree D = ∏ Φ ∈ S, A'.eval Φ := by
    rw [hQdef, resultant_prod_left S (fun Φ => X - C Φ) A' D (by simp) hA']
    refine Finset.prod_congr rfl fun Φ _ => ?_
    rw [natDegree_X_sub_C, resultant_X_sub_C_left A' D Φ hA']
  have key : iota L x (resultant fh A fh.natDegree D) =
      (∏ Φ ∈ S, A'.eval Φ) * resultant R A' R.natDegree D := by
    rw [← resultant_map_map, ← hPdef, ← hA'def, hdeg, hR, resultant_mul_left _ _ _ _ hA', hprod]
  rw [key]
  apply Dvd.dvd.mul_right
  rw [pow_mul, ← Finset.prod_const]
  exact Finset.prod_dvd_prod_of_dvd _ _ hvan

end Langlands.AlgebraicGeometry.LangWeil.Stepanov

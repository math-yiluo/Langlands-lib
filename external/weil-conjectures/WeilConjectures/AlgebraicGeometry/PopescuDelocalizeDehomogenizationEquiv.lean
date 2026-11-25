/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Dehomogenization equivalence for weak Popescu delocalization

Source: Stacks Project, proof of Tag 07F9, the final displayed isomorphism.
(blueprint: lem-weil-pbc-popescu-delocalize-dehomogenization-equiv)
-/

@[expose] public section

universe u
open scoped BigOperators
open MvPolynomial
namespace Algebra

private theorem homogenization_eval
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (n m : ℕ) (f : MvPolynomial (Fin (n + m)) R) (d : ℕ)
    (hd : ∀ e ∈ f.support,
      (∑ i : Fin (n + m), if n ≤ i.val then e i else 0) ≤ d)
    (v : Fin (n + m) → A) (w : A) :
    (∑ e ∈ f.support, algebraMap R A (f.coeff e) *
      (∏ i : Fin (n + m), (if n ≤ i.val then v i * w else v i) ^ e i) *
      w ^ (d - ∑ i : Fin (n + m), if n ≤ i.val then e i else 0)) =
      w ^ d * aeval v f := by
  classical
  rw [aeval_eq_eval₂Hom, coe_eval₂Hom, eval₂_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hp : (∏ i : Fin (n + m),
      (if n ≤ i.val then v i * w else v i) ^ e i) =
      (∏ i : Fin (n + m), v i ^ e i) *
        w ^ (∑ i : Fin (n + m), if n ≤ i.val then e i else 0) := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    split_ifs <;> simp [mul_pow]
  rw [hp]
  rw [mul_assoc, mul_assoc, ← pow_add, Nat.add_sub_of_le (hd e he)]
  ring

private noncomputable def quotientAwayLift
    {R P A : Type u} [CommRing R] [CommRing P] [CommRing A]
    [Algebra R P] [Algebra R A]
    (I : Ideal P) (b : P) (f : P →ₐ[R] A)
    (hf : ∀ p ∈ I, f p = 0) (hb : IsUnit (f b)) :
    Localization.Away (Ideal.Quotient.mk I b) →ₐ[R] A :=
  IsLocalization.Away.liftAlgHom (Ideal.Quotient.mk I b)
    (f := Ideal.Quotient.liftₐ I f hf) (by simpa using hb)

private theorem quotientAwayLift_mk
    {R P A : Type u} [CommRing R] [CommRing P] [CommRing A]
    [Algebra R P] [Algebra R A]
    (I : Ideal P) (b : P) (f : P →ₐ[R] A)
    (hf : ∀ p ∈ I, f p = 0) (hb : IsUnit (f b)) (p : P) :
    quotientAwayLift I b f hf hb
      (algebraMap (P ⧸ I) (Localization.Away (Ideal.Quotient.mk I b))
        (Ideal.Quotient.mk I p)) = f p := by
  simp [quotientAwayLift, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]

private theorem quotientAway_ext
    {R P A : Type u} [CommRing R] [CommRing P] [CommRing A]
    [Algebra R P] [Algebra R A] (I : Ideal P) (b : P)
    (f g : Localization.Away (Ideal.Quotient.mk I b) →ₐ[R] A)
    (h : ∀ p : P, f (algebraMap (P ⧸ I) _ (Ideal.Quotient.mk I p)) =
      g (algebraMap (P ⧸ I) _ (Ideal.Quotient.mk I p))) : f = g := by
  apply IsLocalization.algHom_ext (Submonoid.powers (Ideal.Quotient.mk I b))
  apply Ideal.Quotient.algHom_ext
  exact AlgHom.ext h

/-- Source: Stacks Project, proof of Tag 07F9, the isomorphism following the
construction of B and b.
(blueprint: lem-weil-pbc-popescu-delocalize-dehomogenization-equiv)

Proof: Denote the right-hand quotient by D and its localization by C. Both
localizations invert the class of x₀*w*∏sⱼ, hence x₀, w and all sⱼ are units.
Define the polynomial map to C fixing x₀, the first n original variables and w,
and sending each of the last m original variables Xᵢ to xᵢ*w. Expanding the
support sum in hF gives Fⱼ(u,v*w,w) = w^(dⱼ)*fⱼ(u,v): in each monomial the
w-exponent is the sum of the last m exponents plus its complementary exponent;
hdegree ensures this sum is dⱼ. Thus x₀*Fⱼ maps to zero. The membership hg gives
sⱼ₊₁*gⱼ = 0 in D and hence gⱼ = 0 in C by the unit sⱼ₊₁. This map factors
through B and extends to B_b, since b maps to a unit.

Conversely map D to B_b by fixing x₀, the first n original variables and w, and
sending each remaining xᵢ to Xᵢ/w. The same identity gives fⱼ = w^(-dⱼ)*Fⱼ
under this substitution. In B_b, x₀*Fⱼ = 0 and x₀ is a unit, so Fⱼ = 0.
The map therefore descends to D and extends to C because x₀*w*∏sⱼ is a unit.
The composites fix the coefficients and every variable: the only nontrivial
identities are (xᵢ*w)/w = xᵢ and (Xᵢ/w)*w = Xᵢ. Polynomial and quotient
extensionality, followed by uniqueness of maps out of each localization, show
that these maps are inverse R-algebra maps. This also covers m=0, c=0, t=0,
and zero localizations. No Jacobian hypothesis is needed for this isomorphism. -/
theorem popescu_delocalize_dehomogenization_equiv_exists
    (R : Type u) [CommRing R]
    (n m c t : ℕ)
    (f : Fin c → MvPolynomial (Fin (n + m)) R)
    (g : Fin t → MvPolynomial (Fin n) R)
    (s : Fin (t + 1) → R)
    (hg : ∀ j : Fin t,
      C (s j.succ) * rename (Fin.castLE (Nat.le_add_right n m)) (g j) ∈
        Ideal.span (Set.range f))
    (d : Fin c → ℕ)
    (hdegree : ∀ j : Fin c, ∀ e ∈ (f j).support,
      (∑ i : Fin (n + m), if n ≤ i.val then e i else 0) ≤ d j)
    (F : Fin c → MvPolynomial (Fin (n + m + 2)) R)
    (hF : ∀ j : Fin c, F j =
      ∑ e ∈ (f j).support,
        C ((f j).coeff e) *
          (∏ i : Fin (n + m), X i.castSucc.succ ^ e i) *
          X (Fin.last (n + m + 1)) ^
            (d j - ∑ i : Fin (n + m), if n ≤ i.val then e i else 0)) :
    Nonempty (Localization.Away
      (Ideal.Quotient.mk
        (Ideal.span
          (Set.range (fun j : Fin t =>
            rename (fun i : Fin n =>
              (Fin.castLE (Nat.le_add_right n m) i).castSucc.succ) (g j)) ∪
            Set.range (fun j : Fin c => X (0 : Fin (n + m + 2)) * F j)))
        (X (0 : Fin (n + m + 2)) * X (Fin.last (n + m + 1)) *
          C (∏ j : Fin (t + 1), s j))) ≃ₐ[R]
      Localization.Away (Ideal.Quotient.mk
        (Ideal.span (Set.range (fun j : Fin c =>
          rename (fun i : Fin (n + m) => i.castSucc.succ) (f j))))
        (X (0 : Fin (n + m + 2)) * X (Fin.last (n + m + 1))
          * C (∏ j : Fin (t + 1), s j)))) := by
  classical
  let P := MvPolynomial (Fin (n + m + 2)) R
  let I : Ideal P := Ideal.span
    (Set.range (fun j : Fin t ↦
      rename (fun i : Fin n ↦
        (Fin.castLE (Nat.le_add_right n m) i).castSucc.succ) (g j)) ∪
      Set.range (fun j : Fin c ↦ X (0 : Fin (n + m + 2)) * F j))
  let J : Ideal P := Ideal.span (Set.range (fun j : Fin c ↦
    rename (fun i : Fin (n + m) ↦ i.castSucc.succ) (f j)))
  let b : P := X (0 : Fin (n + m + 2)) * X (Fin.last (n + m + 1)) *
    C (∏ j : Fin (t + 1), s j)
  let BL := Localization.Away (Ideal.Quotient.mk I b)
  let DL := Localization.Away (Ideal.Quotient.mk J b)
  let qB : P →ₐ[R] BL := (Algebra.algHom R (P ⧸ I) BL).comp (Ideal.Quotient.mkₐ R I)
  let qD : P →ₐ[R] DL := (Algebra.algHom R (P ⧸ J) DL).comp (Ideal.Quotient.mkₐ R J)
  have huB : IsUnit (qB b) := by
    change IsUnit (algebraMap (P ⧸ I) BL (Ideal.Quotient.mk I b))
    exact IsLocalization.Away.algebraMap_isUnit _
  have huD : IsUnit (qD b) := by
    change IsUnit (algebraMap (P ⧸ J) DL (Ideal.Quotient.mk J b))
    exact IsLocalization.Away.algebraMap_isUnit _
  have hBw : IsUnit (qB (X (Fin.last (n + m + 1)))) := by
    exact isUnit_of_mul_isUnit_right
      (isUnit_of_mul_isUnit_left (by simpa only [b, map_mul] using huB))
  have hDw : IsUnit (qD (X (Fin.last (n + m + 1)))) := by
    exact isUnit_of_mul_isUnit_right
      (isUnit_of_mul_isUnit_left (by simpa only [b, map_mul] using huD))
  have hBx : IsUnit (qB (X (0 : Fin (n + m + 2)))) := by
    exact isUnit_of_mul_isUnit_left
      (isUnit_of_mul_isUnit_left (by simpa only [b, map_mul] using huB))
  let wB : BLˣ := hBw.unit
  let wD : DLˣ := hDw.unit
  have hwB : (wB : BL) = qB (X (Fin.last (n + m + 1))) := hBw.unit_spec
  have hwD : (wD : DL) = qD (X (Fin.last (n + m + 1))) := hDw.unit_spec
  let scaled : Fin (n + m + 2) → Prop := fun i ↦ n + 1 ≤ i.val ∧ i.val < n + m + 1
  let aD : Fin (n + m + 2) → DL := fun i ↦
    if scaled i then qD (X i) * (wD : DL) else qD (X i)
  let aB : Fin (n + m + 2) → BL := fun i ↦
    if scaled i then qB (X i) * (↑wB⁻¹ : BL) else qB (X i)
  let φ : P →ₐ[R] DL := aeval aD
  let ψ : P →ₐ[R] BL := aeval aB
  have haDw : aD (Fin.last (n + m + 1)) = (wD : DL) := by
    simp [aD, scaled, ← hwD]
  have haBw : aB (Fin.last (n + m + 1)) = (wB : BL) := by
    simp [aB, scaled, ← hwB]
  have haDx : aD (0 : Fin (n + m + 2)) = qD (X 0) := by
    simp [aD, scaled]
  have haBx : aB (0 : Fin (n + m + 2)) = qB (X 0) := by
    simp [aB, scaled]
  have haDi (i : Fin (n + m)) :
      aD i.castSucc.succ =
        if n ≤ i.val then qD (X i.castSucc.succ) * (wD : DL)
        else qD (X i.castSucc.succ) := by
    simp only [aD, scaled, Fin.val_succ, Fin.val_castSucc]
    have hi := i.isLt
    split_ifs <;> simp_all
  have haBi (i : Fin (n + m)) :
      aB i.castSucc.succ =
        if n ≤ i.val then qB (X i.castSucc.succ) * (↑wB⁻¹ : BL)
        else qB (X i.castSucc.succ) := by
    simp only [aB, scaled, Fin.val_succ, Fin.val_castSucc]
    have hi := i.isLt
    split_ifs <;> simp_all
  have hqDf (j : Fin c) :
      aeval (fun i : Fin (n + m) ↦ qD (X i.castSucc.succ)) (f j) = 0 := by
    have he : (aeval (fun i : Fin (n + m) ↦ qD (X i.castSucc.succ))) =
        qD.comp (rename (fun i : Fin (n + m) ↦ i.castSucc.succ)) := by
      ext i
      dsimp only [P]
      simp [MvPolynomial.rename_X, MvPolynomial.aeval_X]
    rw [he, AlgHom.comp_apply]
    change algebraMap (P ⧸ J) DL (Ideal.Quotient.mk J _) = 0
    have hm : rename (fun i : Fin (n + m) ↦ i.castSucc.succ) (f j) ∈ J :=
      Ideal.subset_span ⟨j, rfl⟩
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm, map_zero]
  have hφF (j : Fin c) : φ (F j) = 0 := by
    rw [show φ (F j) = aeval aD (F j) from rfl, hF j]
    simp only [map_sum, map_mul, map_prod, map_pow, MvPolynomial.aeval_C,
      MvPolynomial.aeval_X, haDw, haDi]
    rw [homogenization_eval n m (f j) (d j) (hdegree j)]
    rw [hqDf, mul_zero]
  have hφg (j : Fin t) :
      φ (rename (fun i : Fin n ↦
        (Fin.castLE (Nat.le_add_right n m) i).castSucc.succ) (g j)) = 0 := by
    let E : MvPolynomial (Fin (n + m)) R →ₐ[R] DL :=
      aeval (fun i : Fin (n + m) ↦ qD (X i.castSucc.succ))
    have hE : ∀ p ∈ Ideal.span (Set.range f), E p = 0 := by
      suffices Ideal.span (Set.range f) ≤ RingHom.ker E.toRingHom from
        fun p hp ↦ this hp
      exact Ideal.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact hqDf k)
    have hs : ∀ k : Fin (t + 1), IsUnit (qD (C (s k))) := by
      have hparts : (IsUnit (qD (X (0 : Fin (n + m + 2)))) ∧
          IsUnit (qD (X (Fin.last (n + m + 1))))) ∧
          ∀ k : Fin (t + 1), IsUnit (qD (C (s k))) := by
        simpa [b] using huD
      exact hparts.2
    have hEC (r : R) : E (C r) = qD (C r) := by
      dsimp only [E, P]
      rw [MvPolynomial.aeval_C]
      exact (qD.commutes r).symm
    have hz := hE _ (hg j)
    rw [map_mul, hEC] at hz
    have hz' : E (rename (Fin.castLE (Nat.le_add_right n m)) (g j)) = 0 :=
      (hs j.succ).mul_left_cancel (by simpa only [mul_zero] using hz)
    have he : φ.comp (rename (fun i : Fin n ↦
        (Fin.castLE (Nat.le_add_right n m) i).castSucc.succ)) =
        E.comp (rename (Fin.castLE (Nat.le_add_right n m))) := by
      apply MvPolynomial.algHom_ext
      intro i
      dsimp only [φ, E, P]
      simp only [AlgHom.comp_apply, MvPolynomial.rename_X, MvPolynomial.aeval_X]
      have hi : ¬scaled (Fin.castLE (Nat.le_add_right n m) i).castSucc.succ := by
        dsimp only [scaled]
        simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_castLE]
        have hi := i.isLt
        omega
      simp only [aD, ite_eq_right hi]
      rfl
    exact (AlgHom.congr_fun he (g j)).trans hz'
  have hφI : ∀ p ∈ I, φ p = 0 := by
    suffices I ≤ RingHom.ker φ.toRingHom from fun p hp ↦ this hp
    apply Ideal.span_le.mpr
    rintro p (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact hφg j
    · change φ (X (0 : Fin (n + m + 2)) * F j) = 0
      simp [hφF]
  have hψf (j : Fin c) :
      ψ (rename (fun i : Fin (n + m) ↦ i.castSucc.succ) (f j)) = 0 := by
    have hqBF : qB (F j) = 0 := by
      have hm : X (0 : Fin (n + m + 2)) * F j ∈ I :=
        Ideal.subset_span (Or.inr ⟨j, rfl⟩)
      have hz : qB (X (0 : Fin (n + m + 2)) * F j) = 0 := by
        change algebraMap (P ⧸ I) BL (Ideal.Quotient.mk I _) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm, map_zero]
      rw [map_mul] at hz
      exact hBx.mul_left_cancel (by simpa only [mul_zero] using hz)
    have hvar (i : Fin (n + m)) :
        (if n ≤ i.val then aB i.castSucc.succ * (wB : BL)
          else aB i.castSucc.succ) = qB (X i.castSucc.succ) := by
      rw [haBi]
      split_ifs <;> simp [mul_assoc]
    have hBC (r : R) : qB (C r) = algebraMap R BL r := qB.commutes r
    have he : qB (F j) = (wB : BL) ^ d j *
        aeval (fun i : Fin (n + m) ↦ aB i.castSucc.succ) (f j) := by
      rw [hF j]
      dsimp only [P]
      simp only [map_sum, map_mul, map_prod, map_pow]
      rw [← homogenization_eval n m (f j) (d j) (hdegree j)]
      simp only [hvar]
      apply Finset.sum_congr rfl
      intro e he
      rw [hBC, ← hwB]
    rw [he] at hqBF
    have hz : aeval (fun i : Fin (n + m) ↦ aB i.castSucc.succ) (f j) = 0 :=
      (wB.isUnit.pow (d j)).mul_left_cancel (by simpa only [mul_zero] using hqBF)
    dsimp only [ψ, P]
    rw [MvPolynomial.aeval_rename]
    exact hz
  have hψJ : ∀ p ∈ J, ψ p = 0 := by
    suffices J ≤ RingHom.ker ψ.toRingHom from fun p hp ↦ this hp
    exact Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hψf j)
  have hφb : φ b = qD b := by
    dsimp only [P]
    simp only [φ, b, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      haDx, haDw]
    congr 1
  have hψb : ψ b = qB b := by
    dsimp only [P]
    simp only [ψ, b, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      haBx, haBw]
    congr 1
  let α : BL →ₐ[R] DL := quotientAwayLift I b φ hφI (hφb.symm ▸ huD)
  let β : DL →ₐ[R] BL := quotientAwayLift J b ψ hψJ (hψb.symm ▸ huB)
  have hα (p : P) : α (qB p) = φ p := quotientAwayLift_mk _ _ _ _ _ p
  have hβ (p : P) : β (qD p) = ψ p := quotientAwayLift_mk _ _ _ _ _ p
  have hαw : α (wB : BL) = (wD : DL) := by
    rw [hwB, hα]
    dsimp only [φ, P]
    rw [MvPolynomial.aeval_X]
    exact haDw
  have hβw : β (wD : DL) = (wB : BL) := by
    rw [hwD, hβ]
    dsimp only [ψ, P]
    rw [MvPolynomial.aeval_X]
    exact haBw
  have hαwi : α (↑wB⁻¹ : BL) = (↑wD⁻¹ : DL) := by
    have he : Units.map α.toMonoidHom wB = wD := Units.ext hαw
    simpa using congrArg (fun w : DLˣ ↦ (↑w⁻¹ : DL)) he
  have hβα : β.comp α = AlgHom.id R BL := by
    apply quotientAway_ext I b
    apply AlgHom.congr_fun (show (β.comp α).comp qB = (AlgHom.id R BL).comp qB from ?_)
    apply MvPolynomial.algHom_ext
    intro i
    change β (α (qB (X i))) = qB (X i)
    rw [hα]
    rw [show φ (X i) = aD i from MvPolynomial.aeval_X aD i]
    by_cases hi : scaled i
    · simp only [aD, ite_eq_left hi, map_mul, hβw, hβ]
      rw [show ψ (X i) = aB i from MvPolynomial.aeval_X aB i]
      simp [aB, hi, mul_assoc]
    · simp only [aD, ite_eq_right hi, hβ]
      rw [show ψ (X i) = aB i from MvPolynomial.aeval_X aB i]
      simp [aB, hi]
  have hαβ : α.comp β = AlgHom.id R DL := by
    apply quotientAway_ext J b
    apply AlgHom.congr_fun (show (α.comp β).comp qD = (AlgHom.id R DL).comp qD from ?_)
    apply MvPolynomial.algHom_ext
    intro i
    change α (β (qD (X i))) = qD (X i)
    rw [hβ]
    rw [show ψ (X i) = aB i from MvPolynomial.aeval_X aB i]
    by_cases hi : scaled i
    · simp only [aB, ite_eq_left hi, map_mul, hαwi, hα]
      rw [show φ (X i) = aD i from MvPolynomial.aeval_X aD i]
      simp [aD, hi, mul_assoc]
    · simp only [aB, ite_eq_right hi, hα]
      rw [show φ (X i) = aD i from MvPolynomial.aeval_X aD i]
      simp only [aD, ite_eq_right hi]
  exact ⟨AlgEquiv.ofAlgHom α β hαβ hβα⟩

end Algebra

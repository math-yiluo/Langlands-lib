/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulCechLocalizedEvaluation
import WeilConjectures.AlgebraicGeometry.KoszulCechBoundaryEvaluation
import Mathlib.Data.Nat.Choose.Basic

/-! # The horizontal localized Koszul boundary calculation

Source: Stacks Project, Tags 08D0 and 08D1.
(blueprint: lem-sc-koszul-cech-localized-boundary).
-/

@[expose] public section

universe uK

open CategoryTheory

namespace AlgebraicGeometry

private theorem triangle_step (p : ℕ) (hp : 0 < p) :
    p * (p - 1) / 2 = (p - 1) * (p - 2) / 2 + (p - 1) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  rw [← Nat.choose_two_right]
  have ht : t + 1 - 2 = t - 1 := by omega
  simp only [Nat.succ_sub_one, ht]
  rw [← Nat.choose_two_right, Nat.choose_succ_succ t 1, Nat.choose_one_right]
  change t + t.choose 2 = t.choose 2 + t
  omega

private theorem boundary_sign (c : ℕ) (hc : 1 < c) (n : ℤ) :
    (Int.negOnePow ((c - 1 : ℕ) * (n + 2 - (c : ℤ)) +
      ((c - 1) * (c - 2) / 2 : ℕ))) * n.negOnePow =
    Int.negOnePow ((c - 2 : ℕ) * (n + 2 - (c : ℤ)) +
      ((c - 2) * (c - 3) / 2 : ℕ)) := by
  have htri := triangle_step (c - 1) (by omega)
  have h1 : c - 1 - 1 = c - 2 := by omega
  have h2 : c - 1 - 2 = c - 3 := by omega
  rw [h1, h2] at htri
  have ht : (((c - 1) * (c - 2) / 2 : ℕ) : ℤ) =
      (((c - 2) * (c - 3) / 2 : ℕ) : ℤ) + (c - 2 : ℕ) := by
    exact_mod_cast htri
  have hd : ((c - 1 : ℕ) : ℤ) = (c - 2 : ℕ) + 1 := by omega
  have hdc : ((c - 2 : ℕ) : ℤ) = (c : ℤ) - 2 := by omega
  rw [← Int.negOnePow_add, ht, hd]
  have hh : (((c - 2 : ℕ) : ℤ) + 1) * (n + 2 - (c : ℤ)) +
      ((((c - 2) * (c - 3) / 2 : ℕ) : ℤ) + (c - 2 : ℕ)) + n =
      (c - 2 : ℕ) * (n + 2 - (c : ℤ)) +
        (((c - 2) * (c - 3) / 2 : ℕ) : ℤ) + 2 * n := by
    rw [hdc]
    ring
  rw [hh, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

private theorem division_factor {A : Type*} [CommRing A]
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (s a t : A) (h : s = a * t) (e : ℕ)
    (D : N ≃ₗ[A] N) (E : M ≃ₗ[A] M)
    (hD : ∀ y, D.symm y = s ^ e • y) (hE : ∀ x, t ^ e • E x = x)
    (R : M →ₗ[A] N) (x : M) : D (a ^ e • R x) = R (E x) := by
  apply D.symm.injective
  rw [D.symm_apply_apply, hD, h, mul_pow, mul_smul]
  rw [← R.map_smul (t ^ e) (E x), hE]


variable (A : Type uK) [CommRing A] (r : ℕ) (f : Fin r → A)
variable (F : CochainComplex
  (SheafOfModules.{uK} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)

private theorem localized_fraction_restriction
    (S T : SheafOfModules.{uK} (moduleRings (Spec (.of A)).toRingedSpace))
    (g : S ⟶ T) (s a t : A) (hst : s = a * t) (e : ℕ)
    (hle : PrimeSpectrum.basicOpen s ≤ PrimeSpectrum.basicOpen t)
    (x : (affineOpenSections A ⊤).obj S) :
    koszulCechScalarDivision A T s e
      (a ^ e • (modulesSpecToSheaf.obj T).obj.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen s ≤ ⊤)).op
        ((affineOpenSections A ⊤).map g x)) =
    (modulesSpecToSheaf.obj T).obj.map (homOfLE hle).op
      ((affineOpenSections A (PrimeSpectrum.basicOpen t)).map g
        (koszulCechScalarDivision A S t e
          ((modulesSpecToSheaf.obj S).obj.map
            (homOfLE (le_top : PrimeSpectrum.basicOpen t ≤ ⊤)).op x))) := by
  let R : (affineOpenSections A (PrimeSpectrum.basicOpen t)).obj S ⟶
      (affineOpenSections A (PrimeSpectrum.basicOpen s)).obj T :=
    (affineOpenSections A (PrimeSpectrum.basicOpen t)).map g ≫
      (modulesSpecToSheaf.obj T).obj.map (homOfLE hle).op
  have hnum : (modulesSpecToSheaf.obj T).obj.map
      (homOfLE (le_top : PrimeSpectrum.basicOpen s ≤ ⊤)).op
      ((affineOpenSections A ⊤).map g x) =
      R ((modulesSpecToSheaf.obj S).obj.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen t ≤ ⊤)).op x) := by
    have hres := ConcreteCategory.congr_hom
      ((modulesSpecToSheaf.map g).hom.naturality
        (homOfLE (le_top : PrimeSpectrum.basicOpen t ≤ ⊤)).op) x
    simp only [ModuleCat.comp_apply] at hres
    dsimp only [affineOpenSections] at hres ⊢
    have hcomp :
        (homOfLE (le_top : PrimeSpectrum.basicOpen t ≤ ⊤)).op ≫ (homOfLE hle).op =
          (homOfLE (le_top : PrimeSpectrum.basicOpen s ≤ ⊤)).op := Subsingleton.elim _ _
    rw [← hcomp, Functor.map_comp, ModuleCat.comp_apply, ← hres]
    rfl
  rw [hnum]
  exact division_factor s a t hst e
    (koszulCechScalarDivision A T s e) (koszulCechScalarDivision A S t e)
    (fun _ ↦ rfl)
    (fun y ↦ (koszulCechScalarDivision A S t e).symm_apply_apply y) R.hom _

/-- The precomposition term alone becomes the alternating Cech deletion sum.
Source: Stacks Project, Tag 08D0, the two displayed differential calculations,
and Tag 08D1, the correction of totalization signs.
(blueprint: lem-sc-koszul-cech-localized-boundary)
Proof: put p=card(J)-1. The hypothesis card(J)>1 makes every erased subset
nonempty and places both tail degrees in the supported range. Transport the tail
differential to the negative Koszul contraction. On the
increasing wedge it is minus the sum over j in J of (-1)^position times
f(j)^(e+1) times the increasing wedge for J.erase j. Here position is the
number of elements of J smaller than j. Apply z and restriction and use their
A-linearity to distribute the sum. The product identity
prod(J)=f(j)*prod(J.erase j) and the invertibility of these products on D(prod(J))
identify division of f(j)^(e+1) times the restricted numerator by prod(J)^(e+1)
with restriction of division by prod(J.erase j)^(e+1). Naturality composes the
two restrictions. The equality of vertical degrees is principalCech_erase_degree;
its eqToHom is exactly the transport in the right side. The negative boundary
and the Hom sign (n+1).negOnePow leave n.negOnePow. Finally the difference
S(p,n+1)+n-S(p-1,n) equals 2*n, hence is even, where S(p,n)=p*(n-p)+p*(p-1)/2.
This matches the displayed signs term by term. No coefficient differential is
involved. The singleton case is proved directly in the original theorem and is excluded here.
The empty cover has no J; zero or nilpotent products give empty opens
and zero section modules, so the argument also applies there. -/
theorem koszulCechLocalized_boundary (e : ℕ)
    (B : ∀ J : {J : Finset (Fin r) // J.Nonempty},
      ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat).X
        (1 - (J.val.card : ℤ)))
    (hB : ∀ J, B J =
      ((koszulOpenTail A r f e).extendXIso ComplexShape.embeddingDownNat
        (show ComplexShape.embeddingDownNat.f (J.val.card - 1) =
          1 - (J.val.card : ℤ) by
          simp only [ComplexShape.embeddingDownNat_f]
          have h : 0 < J.val.card := Finset.card_pos.mpr J.property
          omega)).inv
        (exteriorPower.ιMulti A (J.val.card - 1 + 1)
          (fun i ↦ Finsupp.single (J.val.orderEmbOfFin
            (show J.val.card = J.val.card - 1 + 1 by
              have h : 0 < J.val.card := Finset.card_pos.mpr J.property
              omega) i) (1 : A)))) (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain
      ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat)
      (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) n)
    (J : {J : Finset (Fin r) // J.Nonempty}) (hJ : 1 < J.val.card) :
    (Int.negOnePow
      ((J.val.card - 1 : ℕ) * ((n + 1) + 1 - (J.val.card : ℤ)) +
        ((J.val.card - 1) * (J.val.card - 2) / 2 : ℕ))) •
      koszulCechScalarDivision A (F.X ((n + 1) + 1 - (J.val.card : ℤ)))
        (∏ j ∈ J.val, f j) (e + 1)
        ((modulesSpecToSheaf.obj (F.X ((n + 1) + 1 - (J.val.card : ℤ)))).obj.map
          (homOfLE (le_top : principalCechIntersection r f J.val ≤ ⊤)).op
          (((n + 1).negOnePow •
            ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat).d
              (1 - (J.val.card : ℤ)) (2 - (J.val.card : ℤ)) ≫
            z.v (2 - (J.val.card : ℤ)) ((n + 1) + 1 - (J.val.card : ℤ)) (by ring))
              (B J))) =
      ∑ j : J.val, if h : (J.val.erase j.val).Nonempty then
        (-1 : A) ^ ((J.val.filter (fun i ↦ i < j.val)).card) •
          (modulesSpecToSheaf.obj (F.X ((n + 1) + 1 - (J.val.card : ℤ)))).obj.map
            (homOfLE (principalCechIntersection_erase_le r f J.val j.val)).op
            ((affineOpenSections A (principalCechIntersection r f (J.val.erase j.val))).map
              (eqToHom (congrArg F.X
                (principalCech_erase_degree r J.val j.val j.property n)))
              (koszulCechLocalizedDegreeMap A r f F e n B z ⟨J.val.erase j.val, h⟩))
      else 0 := by
  classical
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply]
  erw [koszulCechBoundary_evaluation A r f F e B hB n z J hJ]
  simp only [Int.negOnePow_succ, Units.smul_def, Units.val_neg,
    ← Int.cast_smul_eq_zsmul (R := A), Int.cast_neg, neg_smul, smul_neg, neg_neg,
    map_smul, map_sum, Finset.smul_sum, Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : (J.val.erase j.val).Nonempty
  · simp only [dite_eq_left h]
    have hcard := Finset.card_erase_add_one j.property
    have hsign := boundary_sign J.val.card hJ n
    have hc1 : (J.val.erase j.val).card - 1 = J.val.card - 2 := by omega
    have hc2 : (J.val.erase j.val).card - 2 = J.val.card - 3 := by omega
    have hdeg := principalCech_erase_degree r J.val j.val j.property n
    have hsign' :
        Int.negOnePow
          ((J.val.card - 1 : ℕ) * ((n + 1) + 1 - (J.val.card : ℤ)) +
            ((J.val.card - 1) * (J.val.card - 2) / 2 : ℕ)) * n.negOnePow =
        Int.negOnePow
          (((J.val.erase j.val).card - 1 : ℕ) *
            (n + 1 - ((J.val.erase j.val).card : ℤ)) +
            (((J.val.erase j.val).card - 1) *
              ((J.val.erase j.val).card - 2) / 2 : ℕ)) := by
      simpa only [hc1, hc2, hdeg, show (n + 1) + 1 = n + 2 by ring] using hsign
    simp only [map_smul, mul_smul]
    rw [smul_smul, ← Int.cast_mul, ← Units.val_mul, hsign']
    rw [smul_comm]
    change _ =
      (-1 : A) ^ ((J.val.filter (fun i ↦ i < j.val)).card) •
        (modulesSpecToSheaf.obj (F.X ((n + 1) + 1 - (J.val.card : ℤ)))).obj.map
          (homOfLE (principalCechIntersection_erase_le r f J.val j.val)).op
          ((affineOpenSections A (principalCechIntersection r f (J.val.erase j.val))).map
            (eqToHom (congrArg F.X hdeg))
            ((Int.negOnePow
              (((J.val.erase j.val).card - 1 : ℕ) *
                (n + 1 - ((J.val.erase j.val).card : ℤ)) +
                (((J.val.erase j.val).card - 1) *
                  ((J.val.erase j.val).card - 2) / 2 : ℕ))) •
              koszulCechScalarDivision A (F.X (n + 1 - ((J.val.erase j.val).card : ℤ)))
                (∏ i ∈ J.val.erase j.val, f i) (e + 1)
                ((modulesSpecToSheaf.obj
                  (F.X (n + 1 - ((J.val.erase j.val).card : ℤ)))).obj.map
                  (homOfLE (le_top :
                    principalCechIntersection r f (J.val.erase j.val) ≤ ⊤)).op
                  ((z.v (1 - ((J.val.erase j.val).card : ℤ))
                    (n + 1 - ((J.val.erase j.val).card : ℤ)) (by ring))
                    (B ⟨J.val.erase j.val, h⟩)))))
    simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul (R := A), map_smul]
    apply congrArg (fun x ↦ (-1 : A) ^ ((J.val.filter (fun i ↦ i < j.val)).card) • x)
    apply congrArg (fun x ↦
      ((Int.negOnePow
        (((J.val.erase j.val).card - 1 : ℕ) *
          (n + 1 - ((J.val.erase j.val).card : ℤ)) +
          (((J.val.erase j.val).card - 1) *
            ((J.val.erase j.val).card - 2) / 2 : ℕ)) : ℤ) : A) • x)
    simpa only [principalCechIntersection, map_smul] using
      (localized_fraction_restriction A
      (F.X (n + 1 - ((J.val.erase j.val).card : ℤ)))
      (F.X ((n + 1) + 1 - (J.val.card : ℤ)))
      (eqToHom (congrArg F.X hdeg))
      (∏ i ∈ J.val, f i) (f j.val) (∏ i ∈ J.val.erase j.val, f i)
      (Finset.mul_prod_erase J.val f j.property).symm (e + 1)
      (principalCechIntersection_erase_le r f J.val j.val)
      ((z.v (1 - ((J.val.erase j.val).card : ℤ))
        (n + 1 - ((J.val.erase j.val).card : ℤ)) (by ring))
        (B ⟨J.val.erase j.val, h⟩)))
  · simp only [dite_eq_right h, map_zero, smul_zero]

end AlgebraicGeometry

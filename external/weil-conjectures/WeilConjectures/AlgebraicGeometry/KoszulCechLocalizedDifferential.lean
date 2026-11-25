/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulCechLocalizedEvaluation
import WeilConjectures.AlgebraicGeometry.KoszulCechLocalizedBoundary

/-! # The differential identity for signed localized Koszul evaluation

Source: Stacks Project, Tags 08D0 and 08D1
(blueprint: lem-sc-koszul-cech-localized-differential).
The degree maps are constructed using the inverse of scalar multiplication on principal
opens. Only their compatibility with adjacent differentials remains to be proved.
-/

@[expose] public section

universe uK

open CategoryTheory

namespace AlgebraicGeometry

variable (A : Type uK) [CommRing A]
variable (S : SheafOfModules.{uK} (moduleRings (Spec (.of A)).toRingedSpace)) (s : A)

variable (r : ℕ) (f : Fin r → A)
variable (F : CochainComplex
  (SheafOfModules.{uK} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)

/-- The explicit localized degree maps commute with adjacent differentials when B
is the ordered exterior basis transported into the extended Koszul tail.
Source: Stacks Project, Tags 08D0 and 08D1
(blueprint: lem-sc-koszul-cech-localized-differential).
Proof: In degree n and at a nonempty subset J, put p=card(J)-1 and q=n-p.
The Hom differential is postcomposition by d_F plus (-1)^n precomposition by the
positive Koszul boundary, since the tail uses the negative boundary. On the ordered
wedge, that boundary is the sum over deleting a generator, with coefficient
(-1)^position f_j^(e+1). After restriction to D(product f_j), division by the full
product to power e+1 cancels f_j^(e+1) and leaves the denominator of J.erase j.
Restrictions compose and commute with d_F; inverses to scalar multiplication
commute with these A-linear maps. The singleton case has no incoming horizontal
term, since the tail has no augmentation term in positive cohomological degree.
For S(p,n)=p*(n-p)+p*(p-1)/2, one has S(p,n+1)=S(p,n)+p, and
S(p,n+1)+n-S(p-1,n) is even. These identities give the vertical sign (-1)^p and
the horizontal alternating signs of principalCechDifferentialValue, respectively.
Use the increasing enumeration of J to match the deletion positions with the
number of elements less than j, and use the increasing enumeration of J.erase j
for the remaining ordered wedge. Equality of all subset components proves the
linear-map identity. No quasi-coherence is used. For r=0 there are no components;
if a product is zero or nilpotent, its principal open is empty and sections are zero. -/
theorem koszulCechLocalizedDegreeMap_comm (e : ℕ)
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
              omega) i) (1 : A)))) (n : ℤ) :
    (CochainComplex.moduleHomComplex
      ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat)
      (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)).d
        n (n + 1) ≫ koszulCechLocalizedDegreeMap A r f F e (n + 1) B =
      koszulCechLocalizedDegreeMap A r f F e n B ≫ (principalCechTotal r f F).d
        n (n + 1) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext J
  simp only [principalCechTotal, CochainComplex.of_d, ModuleCat.comp_apply]
  change koszulCechLocalizedDegreeMap A r f F e (n + 1) B
    (CochainComplex.HomComplex.δ n (n + 1) z) J =
    (principalCechDifferential_exists r f F n).choose
      (koszulCechLocalizedDegreeMap A r f F e n B z) J
  rw [(principalCechDifferential_exists r f F n).choose_spec]
  change
    (Int.negOnePow
      ((J.val.card - 1 : ℕ) * ((n + 1) + 1 - (J.val.card : ℤ)) +
        ((J.val.card - 1) * (J.val.card - 2) / 2 : ℕ))) •
      koszulCechScalarDivision A (F.X ((n + 1) + 1 - (J.val.card : ℤ)))
        (∏ j ∈ J.val, f j) (e + 1)
        ((modulesSpecToSheaf.obj (F.X ((n + 1) + 1 - (J.val.card : ℤ)))).obj.map
          (homOfLE (le_top : principalCechIntersection r f J.val ≤ ⊤)).op
          (((CochainComplex.HomComplex.δ n (n + 1) z).v
            (1 - (J.val.card : ℤ)) ((n + 1) + 1 - (J.val.card : ℤ)) (by ring)) (B J))) = _
  rw [CochainComplex.HomComplex.δ_v n (n + 1) rfl z
    (1 - (J.val.card : ℤ)) ((n + 1) + 1 - (J.val.card : ℤ)) (by ring)
    (n + 1 - (J.val.card : ℤ)) (2 - (J.val.card : ℤ)) (by ring) (by ring)]
  simp only [ModuleCat.hom_add, LinearMap.add_apply, map_add, smul_add]
  change _ = _ + _
  apply congrArg₂ (· + ·)
  · change _ = (-1 : A) ^ (J.val.card - 1) •
      (affineOpenSections A (principalCechIntersection r f J.val)).map
        (F.d (n + 1 - (J.val.card : ℤ)) ((n + 1) + 1 - (J.val.card : ℤ)))
        (koszulCechLocalizedDegreeMap A r f F e n B z J)
    exact koszulCechLocalized_vertical A r f F e n J
      ((z.v (1 - (J.val.card : ℤ)) (n + 1 - (J.val.card : ℤ)) (by ring)) (B J))
  · by_cases hcard : J.val.card = 1
    · have hd :
          ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat).d
            (1 - (J.val.card : ℤ)) (2 - (J.val.card : ℤ)) = 0 := by
        have h0 : 1 - (J.val.card : ℤ) = 0 := by omega
        have h1 : 2 - (J.val.card : ℤ) = 1 := by omega
        rw [h0, h1]
        exact
          (koszulOpenTail A r f e).extend_d_from_eq_zero
            ComplexShape.embeddingDownNat 0 1 0
            (by simp [ComplexShape.embeddingDownNat_f])
            (by simp [ComplexShape.down_Rel])
      have he : ∀ j : J.val, ¬ (J.val.erase j.val).Nonempty := by
        intro j h
        have hc := Finset.card_erase_add_one j.property
        have hp := Finset.card_pos.mpr h
        omega
      simp only [hd, smul_zero, Limits.zero_comp, ModuleCat.hom_zero,
        LinearMap.zero_apply, map_zero, he, dite_false, Finset.sum_const_zero, id_eq]
    · have hp := Finset.card_pos.mpr J.property
      exact koszulCechLocalized_boundary A r f F e B hB n z J (by omega)

end AlgebraicGeometry

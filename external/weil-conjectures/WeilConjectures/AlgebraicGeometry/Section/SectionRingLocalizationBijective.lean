/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import WeilConjectures.AlgebraicGeometry.InvertibleSectionLocalization
import WeilConjectures.AlgebraicGeometry.SectionRingVeroneseFractions
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes

/-! # The section-ring localization comparison

## References

* Stacks Project, Properties, Lemmas 01PW and 01Q1
* Stacks Project, Cohomology of Schemes, Lemma 09MR (in degree zero)

## Implementation details

Bijectivity is obtained by transporting the additive equivalence of `invertS_cohomology` in
degree zero (for the invertible module `L.tensorPow d`) to the homogeneous localization.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

private theorem eqToHom_app_heq {X : Scheme.{u}} {M N : X.Modules}
    {U : X.Opens} (h : M = N) (a : Γ(M, U)) :
    HEq ((eqToHom h).app U a) a := by
  subst N
  rfl

private theorem ring_power_of {X : Scheme.{u}} (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (t : Γ(L.tensorPow d, ⊤)) (n : ℕ) :
    (DirectSum.of (SectionRingComponent L) d t) ^ n =
      DirectSum.of (SectionRingComponent L) (d * n)
        ((L.tensorPowMulIso d n).inv.app ⊤
          (tensorPowSectionOne (homOfGlobalSection (L.tensorPow d) t) n ⊤)) := by
  induction n with
  | zero =>
    simp only [pow_zero, tensorPowMulIso, eqToIso.inv, tensorPowSectionOne_zero]
    rfl
  | succ n ih =>
    rw [pow_succ', ih, DirectSum.of_mul_of]
    simp only [tensorPowMulIso, Iso.trans_inv, MonoidalCategory.tensorIso_inv, Iso.refl_inv,
      tensorPowSectionOne_succ, Hom.comp_app, ConcreteCategory.comp_apply,
      eqToIso.inv]
    simp only [tensorPow_succ]
    have ht : (homOfGlobalSection (L.tensorPow d) t).app ⊤
        (unitSectionsEquiv ⊤ 1) = t := by
      change (homOfGlobalSection (L.tensorPow d) t).app ⊤ (1 : Γ(X, ⊤)) = t
      rw [homOfGlobalSection_app_one, presheaf_map_id_apply]
    rw [tensorHom_app_tmulSection, Hom.id_app, ConcreteCategory.id_apply]
    erw [ht]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    apply Sigma.ext (by change d + d * n = d * (n + 1); ring)
    exact (eqToHom_app_heq _ _).symm

private noncomputable def veroneseIso {X : Scheme.{u}} (L : X.Modules) (d n : ℕ) :
    L.tensorPow (n • d) ≅ (L.tensorPow d).tensorPow n :=
  eqToIso (congrArg L.tensorPow (by simp [Nat.mul_comm])) ≪≫ L.tensorPowMulIso d n

private theorem veroneseIso_power {X : Scheme.{u}} (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) (n : ℕ) :
    (veroneseIso L d n).hom.app ⊤ ((s.val ^ n) (n • d)) =
      tensorPowSectionOne (homOfGlobalSection (L.tensorPow d) (s.val d)) n ⊤ := by
  have h (k : ℕ) (hk : k = d * n) :
      (eqToIso (congrArg L.tensorPow hk) ≪≫ L.tensorPowMulIso d n).hom.app ⊤
        ((s.val ^ n) k) =
      tensorPowSectionOne (homOfGlobalSection (L.tensorPow d) (s.val d)) n ⊤ := by
    subst k
    simp only [eqToIso_refl, Iso.refl_trans]
    rcases s with ⟨s, hs⟩
    obtain ⟨t, rfl⟩ := hs
    simp only [DirectSum.of_eq_same]
    rw [ring_power_of, DirectSum.of_eq_same]
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.inv_hom_id, Hom.id_app]
    rfl
  exact h _ (by simp [Nat.mul_comm])

/-- A ring map satisfying the restriction-and-division formula on a nonvanishing open
is bijective. No affineness or ampleness hypothesis is needed. -/
theorem sectionRing_localization_bijective
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    [CompactSpace X] [QuasiSeparatedSpace X]
    (d : ℕ) (hd : 0 < d) (s : sectionRingGrade L d)
    (U : X.Opens) (hU : (U : Set X) = nonvanishingLocus (L.tensorPow d) (s.val d))
    (φ : CommRingCat.of (HomogeneousLocalization.Away (sectionRingGrade L) s.val) ⟶
      Γ(X, U))
    (hφ : ∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
      (φ (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
          ξ.val ξ.property)) •
        (L.tensorPow (n • d)).presheaf.map
          (homOfLE (le_top : U ≤ ⊤)).op ((s.val ^ n) (n • d)) =
        (L.tensorPow (n • d)).presheaf.map
          (homOfLE (le_top : U ≤ ⊤)).op (ξ.val (n • d))) :
    Function.Bijective φ := by
  have _ := hd
  obtain ⟨V, hV, eF, _, hF⟩ := exists_sectionFraction_nonvanishing_equiv
    X (L.tensorPow d) (s.val d) (MonoidalCategory.tensorUnit X.Modules)
  have hVU : V = U := SetLike.coe_injective (hV.trans hU.symm)
  subst V
  obtain ⟨eA, hA⟩ := exists_sectionRing_veronese_fraction_equiv X L d s
  let e : HomogeneousLocalization.Away (sectionRingGrade L) s.val ≃+ Γ(X, U) :=
    eA.trans (eF.trans (unitSectionsEquiv U).toAddEquiv.symm)
  obtain ⟨V, hV, _, hgen⟩ := nonvanishing_section_trivializes X (L.tensorPow d) (s.val d)
  have hVU : V = U := SetLike.coe_injective (hV.trans hU.symm)
  subst V
  have hs : IsFreeGenerator
      ((homOfGlobalSection (L.tensorPow d) (s.val d)).app U (unitSectionsEquiv U 1)) := by
    intro W hW
    change Function.Bijective (fun r : Γ(X, W) ↦
      r • (L.tensorPow d).presheaf.map (homOfLE hW).op
        ((homOfGlobalSection (L.tensorPow d) (s.val d)).app U (1 : Γ(X, U))))
    rw [homOfGlobalSection_app_one, presheaf_map_map_apply]
    constructor
    · intro a b hab
      obtain ⟨c, _, huniq⟩ := hgen W hW
        (a • (L.tensorPow d).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s.val d))
      exact (huniq a rfl).trans (huniq b hab).symm
    · intro t
      obtain ⟨a, ha, _⟩ := hgen W hW t
      exact ⟨a, ha.symm⟩
  have heq : ∀ z, φ z = e z := by
    intro z
    obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
      (sectionRingGrade L) s.property z
    let ξ : sectionRingGrade L (n • d) := ⟨a, ha⟩
    let q := HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n a ha
    let ν := tensorPowSectionOne (homOfGlobalSection (L.tensorPow d) (s.val d)) n U
    have hp : (veroneseIso L d n).hom.app U
        ((L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          ((s.val ^ n) (n • d))) = ν := by
      rw [Hom.app_presheaf_map, veroneseIso_power, presheaf_map_tensorPowSectionOne]
    apply (isFreeGenerator_tensorPowSectionOne
      (homOfGlobalSection (L.tensorPow d) (s.val d)) hs n).smul_left_injective
    have hgiven := congrArg ((veroneseIso L d n).hom.app U) (hφ n ξ)
    rw [Hom.app_smul, hp] at hgiven
    have hfrac := hF n
      ((veroneseIso L d n ≪≫ (MonoidalCategory.leftUnitor _).symm).hom.app ⊤ (ξ.val (n • d)))
    have hA' : eA q = sectionFraction (L.tensorPow d)
        (MonoidalCategory.tensorUnit X.Modules) (s.val d) n
        ((veroneseIso L d n ≪≫ (MonoidalCategory.leftUnitor _).symm).hom.app ⊤
          (ξ.val (n • d))) := by
      simpa only [veroneseIso, Iso.trans_assoc] using hA n ξ
    rw [← hA'] at hfrac
    have hfrac' := congrArg
      ((MonoidalCategory.leftUnitor ((L.tensorPow d).tensorPow n)).hom.app U) hfrac
    have he : eF (eA q) = unitSectionsEquiv U (e q) :=
      ((unitSectionsEquiv U).apply_symm_apply _).symm
    change (MonoidalCategory.leftUnitor ((L.tensorPow d).tensorPow n)).hom.app U
        (tmulSection (eF (eA q)) ν) = _ at hfrac'
    rw [he, leftUnitor_hom_app_tmulSection] at hfrac'
    simp only [← Hom.app_presheaf_map, Iso.trans_hom, Iso.symm_hom, Hom.comp_app,
      ConcreteCategory.comp_apply] at hfrac'
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.inv_hom_id, Hom.id_app] at hfrac'
    exact hgiven.trans hfrac'.symm
  have hfun : (fun z ↦ φ z) = e := funext heq
  change Function.Bijective (fun z ↦ φ z)
  rw [hfun]
  exact e.bijective

end AlgebraicGeometry.Scheme.Modules

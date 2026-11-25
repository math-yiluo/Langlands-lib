/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import WeilConjectures.AlgebraicGeometry.SectionRingVeroneseFractions
import WeilConjectures.AlgebraicGeometry.SectionFractionRestrictionMap
@[expose] public section
universe v
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

-- Tensor-power comparison, as in SectionRingLocalizationBijective.
private theorem eqToHom_app_heq {X : Scheme.{v}} {M N : X.Modules}
    {U : X.Opens} (h : M = N) (a : Γ(M, U)) :
    HEq ((eqToHom h).app U a) a := by
  subst N
  rfl

private theorem ring_power_of {X : Scheme.{v}} (L : X.Modules) [L.IsInvertible]
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

private noncomputable def veroneseIso {X : Scheme.{v}} (L : X.Modules) (d n : ℕ) :
    L.tensorPow (n • d) ≅ (L.tensorPow d).tensorPow n :=
  eqToIso (congrArg L.tensorPow (by simp [Nat.mul_comm])) ≪≫ L.tensorPowMulIso d n

private theorem veroneseIso_power {X : Scheme.{v}} (L : X.Modules) [L.IsInvertible]
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

/-- Existence of a coefficient function satisfying the numerator equation.
The function is obtained by the local quotient construction of Stacks Tags 01N8 and 01NK.
(blueprint: lem-sc-section-ring-coefficient-data-numerator)

Write e_n for the restriction of the degree-n*d component of s^n. The section-ring
product is the tensor product transported by tensorPowAddIso. Restriction preserves
this product, so induction from hs, the unit generator, and IsFreeGenerator.tmulSection
shows that each e_n is a free generator. For a numerator a of degree n*d, let r_n(a)
be the unique scalar with r_n(a) • e_n equal to its restriction to U.
If a/s^n = b/s^m, localization equality supplies k with
s^k * (a*s^m - b*s^n) = 0. Restrict and use bilinearity to get
(r_n(a) - r_m(b)) • e_(k+n+m) = 0. Injectivity of scalar multiplication
by that free generator gives r_n(a) = r_m(b). Every fraction has such a
representative by Away.mk_surjective, so these coefficients descend to a function.
Its numerator equation is the defining equation of r_n(a). This also works on the
empty open: the scalar ring and section modules there are trivial. -/
theorem exists_sectionRing_coefficient_numerator
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) (hd : 0 < d) (U : X.Opens)
    (hs : IsFreeGenerator ((L.tensorPow d).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op (s.val d))) :
    ∃ c : HomogeneousLocalization.Away (sectionRingGrade L) s.val → Γ(X, U),
      ∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
        c (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
            ξ.val ξ.property) •
          (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
            ((s.val ^ n) (n • d)) =
        (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          (ξ.val (n • d)) := by
  classical
  have _ := hd
  have hs' : IsFreeGenerator
      ((homOfGlobalSection (L.tensorPow d) (s.val d)).app U (unitSectionsEquiv U 1)) := by
    change IsFreeGenerator
      ((homOfGlobalSection (L.tensorPow d) (s.val d)).app U (1 : Γ(X, U)))
    rw [homOfGlobalSection_app_one]
    exact hs
  -- Reuse the fraction quotient and its canonical restriction map.
  obtain ⟨eA, hA⟩ := exists_sectionRing_veronese_fraction_equiv X L d s
  obtain ⟨f, _, hf⟩ := exists_sectionFraction_restriction_map
    (L.tensorPow d) (MonoidalCategory.tensorUnit X.Modules) (s.val d) U hs'
  let c : HomogeneousLocalization.Away (sectionRingGrade L) s.val → Γ(X, U) :=
    fun z ↦ (unitSectionsEquiv U).symm (f (eA z))
  refine ⟨c, ?_⟩
  intro n ξ
  let q := HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n ξ.val ξ.property
  let ν := tensorPowSectionOne (homOfGlobalSection (L.tensorPow d) (s.val d)) n U
  have hp : (veroneseIso L d n).hom.app U
      ((L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        ((s.val ^ n) (n • d))) = ν := by
    rw [Hom.app_presheaf_map, veroneseIso_power, presheaf_map_tensorPowSectionOne]
  have hfrac := hf n
    ((veroneseIso L d n ≪≫ (MonoidalCategory.leftUnitor _).symm).hom.app ⊤ (ξ.val (n • d)))
  have hA' : eA q = sectionFraction (L.tensorPow d)
      (MonoidalCategory.tensorUnit X.Modules) (s.val d) n
      ((veroneseIso L d n ≪≫ (MonoidalCategory.leftUnitor _).symm).hom.app ⊤
        (ξ.val (n • d))) := by
    simpa only [veroneseIso, Iso.trans_assoc] using hA n ξ
  rw [← hA'] at hfrac
  -- The left unitor turns tensoring a function with a section into scalar multiplication.
  have hfrac' := congrArg
    ((MonoidalCategory.leftUnitor ((L.tensorPow d).tensorPow n)).hom.app U) hfrac
  have hc : f (eA q) = unitSectionsEquiv U (c q) :=
    ((unitSectionsEquiv U).apply_symm_apply _).symm
  change (MonoidalCategory.leftUnitor ((L.tensorPow d).tensorPow n)).hom.app U
    (tmulSection (f (eA q)) ν) = _ at hfrac'
  rw [hc, leftUnitor_hom_app_tmulSection] at hfrac'
  simp only [← Hom.app_presheaf_map, Iso.trans_hom, Iso.symm_hom, Hom.comp_app,
    ConcreteCategory.comp_apply] at hfrac'
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.inv_hom_id, Hom.id_app] at hfrac'
  have hinj : Function.Injective ((veroneseIso L d n).hom.app U) :=
    ConcreteCategory.bijective_of_isIso ((veroneseIso L d n).hom.app U) |>.1
  apply hinj
  rw [Hom.app_smul, hp]
  exact hfrac'

end AlgebraicGeometry.Scheme.Modules

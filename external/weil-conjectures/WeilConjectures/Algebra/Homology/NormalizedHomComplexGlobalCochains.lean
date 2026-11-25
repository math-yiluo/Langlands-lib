/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexProjections

/-!
# Component-normalized global cochains of the sheaf Hom complex

Source: Stacks Project, Cohomology on Sites, Section 21.34, Equation (21.34.0.2)
(Tag 0A8Z), and Lemma 21.34.8 (Tag 0A96).
(blueprint: lem-pc-normalized-hom-complex-global-cochains)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}

set_option hygiene false in
local notation "𝓡" =>
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
set_option hygiene false in
local notation "Mod" => SheafOfModules.{u} 𝓡

/-- (blueprint: lem-pc-normalized-hom-complex-global-cochains) -/
noncomputable def normalizedHomFactorEquiv (M N : Mod) :
    (SheafOfModules.unit 𝓡 ⟶ SheafOfModules.homObj (R := R) M N) ≃+ (M ⟶ N) where
  toEquiv := (SheafOfModules.unitHomEquiv _).trans
    (SheafOfModules.homObjSectionsEquiv M N)
  map_add' f g := by rfl

/-- (blueprint: lem-pc-normalized-hom-complex-global-cochains) -/
lemma normalizedHomFactorEquiv_comp {M M' N N' : Mod}
    (s : SheafOfModules.unit 𝓡 ⟶ SheafOfModules.homObj (R := R) M N)
    (f : M' ⟶ M) (g : N ⟶ N') :
    normalizedHomFactorEquiv M' N' (s ≫ SheafOfModules.homObjMap (R := R) f g) =
      f ≫ normalizedHomFactorEquiv M N s ≫ g := by
  rfl

/-- Construct the global-cochain comparison from a specified product cone.
The inverse is the unique lift to that product. 
(blueprint: lem-pc-normalized-hom-complex-global-cochains)
-/
noncomputable def normalizedHomGlobalCochainsOfFan (A B : CochainComplex Mod ℤ) (n : ℤ)
    (Z : Mod) (π : ∀ p q : ℤ, p + n = q → (Z ⟶
      SheafOfModules.homObj (R := R) (A.X p) (B.X q)))
    (hπ : IsLimit (Fan.mk Z (fun p ↦ π p (p + n) rfl))) :
    (SheafOfModules.unit 𝓡 ⟶ Z) ≃+ CochainComplex.HomComplex.Cochain A B n :=
    { toFun s := CochainComplex.HomComplex.Cochain.mk fun p q hpq ↦
        normalizedHomFactorEquiv (A.X p) (B.X q) (s ≫ π p q hpq)
      invFun c := Fan.IsLimit.lift hπ fun p ↦
        (normalizedHomFactorEquiv (A.X p) (B.X (p + n))).symm (c.v p (p + n) rfl)
      left_inv s := by
        apply Fan.IsLimit.hom_ext hπ
        intro p
        simpa using Fan.IsLimit.fac hπ (fun p ↦
          s ≫ π p (p + n) rfl) p
      right_inv c := by
        apply CochainComplex.HomComplex.Cochain.ext
        intro p q hpq
        subst q
        change normalizedHomFactorEquiv (A.X p) (B.X (p + n))
          (Fan.IsLimit.lift hπ (fun p ↦
            (normalizedHomFactorEquiv (A.X p) (B.X (p + n))).symm (c.v p (p + n) rfl)) ≫
            π p (p + n) rfl) = c.v p (p + n) rfl
        have hf := Fan.IsLimit.fac hπ (fun p ↦
          (normalizedHomFactorEquiv (A.X p) (B.X (p + n))).symm (c.v p (p + n) rfl)) p
        simp only [fan_mk_proj] at hf
        rw [hf]
        exact AddEquiv.apply_symm_apply _ _
      map_add' s t := by
        apply CochainComplex.HomComplex.Cochain.ext
        intro p q hpq
        simp [add_comp] }

/-- The projections exposed by the Hom-complex product specification. 
(blueprint: lem-pc-normalized-hom-complex-global-cochains)
-/
noncomputable def normalizedHomProjection (A B : CochainComplex Mod ℤ)
    (n p q : ℤ) (h : p + n = q) :
    (homComplex (R := R) A B).X n ⟶ SheafOfModules.homObj (R := R) (A.X p) (B.X q) :=
  (Classical.choose
    (homComplex_projections_exists.{u, u, u, u} (J := J) (R := R))) A B n p q h

/-- The canonical product projections of the chosen Hom complex form a limit cone. 
(blueprint: lem-pc-normalized-hom-complex-global-cochains)
-/
theorem normalizedHomProjection_isLimit (A B : CochainComplex Mod ℤ) (n : ℤ) :
    Nonempty (IsLimit (Fan.mk ((homComplex (R := R) A B).X n)
      (fun p ↦ normalizedHomProjection (R := R) A B n p (p + n) rfl))) := by
  exact (Classical.choose_spec
    (homComplex_projections_exists.{u, u, u, u} (J := J) (R := R))).1 A B n

/-- The explicit product-projection comparison with ordinary cochains.
Source: Stacks Project, sites-cohomology.tex, Tag 0A8Z.
(blueprint: lem-pc-normalized-hom-complex-global-cochains). -/
noncomputable def normalizedHomGlobalCochains
    (R : Sheaf J CommRingCat.{u}) (A B : CochainComplex Mod ℤ) (n : ℤ) :
    (SheafOfModules.unit 𝓡 ⟶ (homComplex (R := R) A B).X n) ≃+
      CochainComplex.HomComplex.Cochain A B n :=
  normalizedHomGlobalCochainsOfFan A B n _ (normalizedHomProjection (R := R) A B n)
    (normalizedHomProjection_isLimit A B n).some

/-- The component formula retained by the explicit comparison.
Source: Stacks Project, sites-cohomology.tex, Tag 0A8Z.
(blueprint: lem-pc-normalized-hom-complex-global-cochains). -/
theorem normalizedHomGlobalCochains_v
    (R : Sheaf J CommRingCat.{u}) (A B : CochainComplex Mod ℤ) (n : ℤ)
    (s : SheafOfModules.unit 𝓡 ⟶ (homComplex (R := R) A B).X n)
    (p q : ℤ) (h : p + n = q) :
    (normalizedHomGlobalCochains R A B n s).v p q h =
      normalizedHomFactorEquiv (A.X p) (B.X q)
        (s ≫ normalizedHomProjection (R := R) A B n p q h) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Differential compatibility of the comparison built from two product cones. 
(blueprint: lem-pc-normalized-hom-complex-global-cochains)
-/
lemma normalizedHomGlobalCochainsOfFan_comm (A B : CochainComplex Mod ℤ)
    (i j : ℤ) (hij : i + 1 = j) (Zi Zj : Mod)
    (πi : ∀ p q : ℤ, p + i = q → (Zi ⟶
      SheafOfModules.homObj (R := R) (A.X p) (B.X q)))
    (πj : ∀ p q : ℤ, p + j = q → (Zj ⟶
      SheafOfModules.homObj (R := R) (A.X p) (B.X q)))
    (hi : IsLimit (Fan.mk Zi (fun p ↦ πi p (p + i) rfl)))
    (hj : IsLimit (Fan.mk Zj (fun p ↦ πj p (p + j) rfl))) (d : Zi ⟶ Zj)
    (hd : ∀ (p q q' p' : ℤ) (hpq : p + j = q) (hq' : p + i = q')
      (hp' : p' + i = q), d ≫ πj p q hpq =
        πi p q' hq' ≫ SheafOfModules.homObjMap (R := R) (𝟙 (A.X p)) (B.d q' q) -
          i.negOnePow • (πi p' q hp' ≫
            SheafOfModules.homObjMap (R := R) (A.d p p') (𝟙 (B.X q))))
    (s : SheafOfModules.unit 𝓡 ⟶ Zi) :
    normalizedHomGlobalCochainsOfFan A B j Zj πj hj (s ≫ d) =
      CochainComplex.HomComplex.δ i j
        (normalizedHomGlobalCochainsOfFan A B i Zi πi hi s) := by
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  rw [CochainComplex.HomComplex.δ_v i j hij _ p q hpq (p + i) (p + 1)
    (by omega) rfl]
  change normalizedHomFactorEquiv (A.X p) (B.X q) ((s ≫ d) ≫ πj p q hpq) = _
  rw [Category.assoc, hd p q (p + i) (p + 1) hpq rfl (by omega)]
  simp only [comp_sub, Units.smul_def, comp_zsmul, ← Category.assoc,
    map_sub, map_zsmul, normalizedHomFactorEquiv_comp, Category.id_comp, Category.comp_id]
  change normalizedHomFactorEquiv (A.X p) (B.X (p + i))
      (s ≫ πi p (p + i) rfl) ≫ B.d (p + i) q -
        (i.negOnePow : ℤˣ) • (A.d p (p + 1) ≫
          normalizedHomFactorEquiv (A.X (p + 1)) (B.X q)
            (s ≫ πi (p + 1) q (by omega))) =
    normalizedHomFactorEquiv (A.X p) (B.X (p + i))
      (s ≫ πi p (p + i) rfl) ≫ B.d (p + i) q +
        j.negOnePow • A.d p (p + 1) ≫
          normalizedHomFactorEquiv (A.X (p + 1)) (B.X q)
            (s ≫ πi (p + 1) q (by omega))
  subst j
  simp only [Int.negOnePow_succ, Units.smul_def, Units.val_neg,
    neg_smul, sub_eq_add_neg]

/-- The explicit normalized comparison commutes with the cochain differential.
Source: Stacks Project, sites-cohomology.tex, Tag 0A8Z.
(blueprint: lem-pc-normalized-hom-complex-global-cochains).
Proof: project onto each Hom factor, apply the differential projection formula,
and identify internal-Hom sections with morphisms. The resulting formula is
exactly the ordinary cochain differential. For nonconsecutive degrees both
sides vanish by the complex shape. -/
theorem normalizedHomGlobalCochains_comm
    (R : Sheaf J CommRingCat.{u}) (A B : CochainComplex Mod ℤ)
    (i j : ℤ) (s : SheafOfModules.unit 𝓡 ⟶ (homComplex (R := R) A B).X i) :
    normalizedHomGlobalCochains R A B j (s ≫ (homComplex (R := R) A B).d i j) =
      CochainComplex.HomComplex.δ i j (normalizedHomGlobalCochains R A B i s) := by
  classical
  by_cases hij : i + 1 = j
  · exact normalizedHomGlobalCochainsOfFan_comm A B i j hij
      ((homComplex (R := R) A B).X i) ((homComplex (R := R) A B).X j)
      (normalizedHomProjection (R := R) A B i) (normalizedHomProjection (R := R) A B j)
      (normalizedHomProjection_isLimit A B i).some
      (normalizedHomProjection_isLimit A B j).some
      ((homComplex (R := R) A B).d i j)
      (fun p q q' p' hpq hq' hp' ↦ (Classical.choose_spec
        (homComplex_projections_exists.{u, u, u, u} (J := J) (R := R))).2.1
            A B i j p q q' p' hij hpq hq' hp') s
  · rw [(homComplex (R := R) A B).shape i j
        (by simpa [ComplexShape.up_Rel] using hij), comp_zero, map_zero,
        CochainComplex.HomComplex.δ_shape i j hij]

end CategoryTheory

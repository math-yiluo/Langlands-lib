/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeBasic

/-! # Strict scalar cone augmentations

Source: Stacks Project, sites-cohomology.tex, principal quotient formulas, Tag 06YP.
(blueprint: lem-cbc-regular-quotient-cone-chain).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v r
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules.RegularQuotientCone

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  {R : Sheaf J CommRingCat.{r}}
  (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
  (T : CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ)
  (ρ : 𝟭 (CochainComplex (Modules R) ℤ) ⟶ T)
  (hz : ∀ P, (complexScalar R t).app P ≫ ρ.app P = 0)

/-- Extend a chain map annihilating the scalar to its cone, with zero shifted component.
Source: Stacks 06YP (blueprint: lem-cbc-regular-quotient-cone-chain). -/
noncomputable def chainAugmentation : cone R t ⟶ T where
  app P := CochainComplex.mappingCone.desc ((complexScalar R t).app P) 0 (ρ.app P)
    (by simp [hz P])
  naturality {P Q} h := by
    ext n : 1
    apply CochainComplex.mappingCone.ext_from _ (n + 1) n rfl
    · simp [cone, CochainComplex.mappingCone.map, Category.assoc]
    · simpa [cone, CochainComplex.mappingCone.map, Category.assoc] using
        congrArg (fun f ↦ f.f n) (ρ.naturality h)

/-- The augmentation is the second projection followed by the coefficient map.
Source: Stacks 06YP (blueprint: lem-cbc-regular-quotient-cone-chain). -/
theorem chainAugmentation_components (P : CochainComplex (Modules R) ℤ) (n : ℤ) :
    ((chainAugmentation t T ρ hz).app P).f n =
      (CochainComplex.mappingCone.snd ((complexScalar R t).app P)).v n n (add_zero n) ≫
        (ρ.app P).f n := by
  rw [chainAugmentation, CochainComplex.mappingCone.desc_f _ _ _ _ n (n + 1) rfl]
  simp

/-- The augmentation composed with the unshifted inclusion is the coefficient map.
Source: Stacks 06YP (blueprint: lem-cbc-regular-quotient-cone-chain). -/
theorem inclusion_chainAugmentation :
    inclusion R t ≫ chainAugmentation t T ρ hz = ρ := by
  apply NatTrans.ext
  funext P
  exact CochainComplex.mappingCone.inr_desc ((complexScalar R t).app P) 0 (ρ.app P)
    (by simp [hz P])

variable {S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
  (E : Modules R ⥤ Modules S) [E.Additive] (adj : E ⊣ restriction φ)

/-- The ordinary adjunction unit applied termwise.
Source: Stacks 03D7 (blueprint: lem-cbc-regular-quotient-cone-chain). -/
noncomputable def coefficientUnit : 𝟭 (CochainComplex (Modules R) ℤ) ⟶
    E.mapHomologicalComplex (.up ℤ) ⋙ (restriction φ).mapHomologicalComplex (.up ℤ) where
  app P := {
    f := fun n ↦ adj.unit.app (P.X n)
    comm' := fun i j _ ↦ (adj.unit.naturality (P.d i j)).symm }
  naturality {P Q} h := by
    ext n : 1
    exact adj.unit.naturality (h.f n)

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasSheafify J AddCommGrpCat] in
/-- The vanishing composite with the coefficient-ring map says the section maps to zero.
Source: Stacks 06YP (blueprint: lem-cbc-regular-quotient-cone-chain). -/
theorem section_image_zero
    (ht : (scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R)) ≫
      ringMap φ = 0) (U : Cᵒᵖ) : (φ.hom.app U).hom (t.val U) = 0 := by
  have h := congrArg (fun f ↦ f.val.app U (1 : R.obj.obj U)) ht
  change (φ.hom.app U).hom ((show R.obj.obj U from t.val U) * 1) * 1 = 0 at h
  simpa only [mul_one] using h

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasSheafify J AddCommGrpCat] in
/-- The scalar acts trivially on any module restricted from the quotient.
Source: Stacks 06YP (blueprint: lem-cbc-regular-quotient-cone-chain). -/
theorem scalar_restriction_zero
    (ht : (scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R)) ≫
      ringMap φ = 0) (M : Modules S) :
    (scalar R t).app ((restriction φ).obj M) = 0 := by
  ext U x
  change (φ.hom.app U).hom (t.val U) • (show M.val.obj U from x) = 0
  rw [section_image_zero t φ ht U, zero_smul]

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasSheafify J AddCommGrpCat] in
/-- The coefficient unit kills the scalar whenever the coefficient-ring map does.
Source: Stacks 06YP (blueprint: lem-cbc-regular-quotient-cone-chain). -/
theorem coefficientUnit_zero
    (ht : (scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R)) ≫
      ringMap φ = 0) (P : CochainComplex (Modules R) ℤ) :
    (complexScalar R t).app P ≫ (coefficientUnit φ E adj).app P = 0 := by
  ext n : 1
  change (scalar R t).app (P.X n) ≫ adj.unit.app (P.X n) = 0
  have hn : adj.unit.app (P.X n) ≫
      (scalar R t).app ((restriction φ).obj (E.obj (P.X n))) =
      (scalar R t).app (P.X n) ≫ adj.unit.app (P.X n) := by
    simpa only [Functor.id_map, Functor.id_obj, Functor.comp_obj] using
      (scalar R t).naturality (adj.unit.app (P.X n))
  rw [← hn, scalar_restriction_zero t φ ht, comp_zero]

/-- Scalar cone formation preserves every quasi-isomorphism, without a flatness condition.
Source: Stacks, derived.tex, Tag 014A
(blueprint: lem-cbc-regular-quotient-cone-chain). -/
theorem cone_quasiIso {P Q : CochainComplex (Modules R) ℤ} (h : P ⟶ Q)
    (hh : QuasiIso h) : QuasiIso ((cone R t).map h) := by
  let := HasDerivedCategory.standard (Modules R)
  let q := HomotopyCategory.quotient (Modules R) (.up ℤ)
  let f := (complexScalar R t).app P
  let g := (complexScalar R t).app Q
  let m := (DerivedCategory.Qh (C := Modules R)).mapTriangle.map
    (q.mapTriangle.map (CochainComplex.mappingCone.triangleMap f g h h
      ((complexScalar R t).naturality h).symm))
  have hi : IsIso (DerivedCategory.Qh.map (q.map h)) :=
    Localization.inverts DerivedCategory.Qh _ _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff h).2 hh)
  have hm : IsIso m.hom₃ := CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂ m
    (DerivedCategory.Qh.map_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished f))
    (DerivedCategory.Qh.map_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished g)) hi hi
  have hc : IsIso (DerivedCategory.Q.map ((cone R t).map h)) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso (Modules R)) _).1 hm
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso (Modules R) _).1 hc

end SheafOfModules.RegularQuotientCone

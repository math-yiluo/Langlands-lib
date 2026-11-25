/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices

/-! # Scalar transport through restricted section complexes

Source: Stacks Project, Tags 01E4 and 01E5.
(blueprint: lem-pc-resolution-sections-homology-scalar)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Scalar endomorphisms intertwined on short complexes remain intertwined on homology. -/
private theorem homology_scalar_transport
    {R : Type u} [Ring R] {C : Type*} [Category C] [Abelian C]
    (A : ShortComplex (ModuleCat.{u} R)) (B : ShortComplex C)
    (E : C ⥤ AddCommGrpCat.{u}) [E.PreservesZeroMorphisms] [E.PreservesHomology]
    (q : A.map (forget₂ _ AddCommGrpCat.{u}) ⟶ B.map E) (r : R) (τ : E ⟶ E)
    (hq : A.mapNatTrans (ModuleCat.smulNatTrans R r).asHom ≫ q = q ≫ B.mapNatTrans τ) :
    (A.homology.smul r).asHom ≫ (A.mapHomologyIso (forget₂ _ AddCommGrpCat.{u})).inv ≫
      ShortComplex.homologyMap q ≫ (B.mapHomologyIso E).hom =
    (A.mapHomologyIso (forget₂ _ AddCommGrpCat.{u})).inv ≫
      ShortComplex.homologyMap q ≫ (B.mapHomologyIso E).hom ≫ τ.app B.homology := by
  have hm := congrArg (fun g ↦ ShortComplex.homologyMap g) hq
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp,
    ShortComplex.homologyMap_mapNatTrans, ShortComplex.homologyMap_mapNatTrans] at hm
  have hm' := congrArg (fun g ↦
    (A.mapHomologyIso (forget₂ _ AddCommGrpCat.{u})).inv ≫ g ≫
      (B.mapHomologyIso E).hom) hm
  simpa [Category.assoc, ModuleCat.smulNatTrans] using hm'

namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The homology comparison of restricted section complexes is semilinear.
Source: Stacks Project, Tags 01E4 and 01E5.
(blueprint: lem-pc-resolution-sections-homology-scalar)

Proof: Put U = f inverse V. The ring map displayed here is pullback of sections
along f: the canonical chart V.toSpecΓ cancels ΓSpecIso, and restriction to the
whole of U is the identity. In every degree, R.components expresses R.sections
as a module morphism on U followed by the restriction comparison and restriction
along the equality U.ι_image_top. Each of these maps preserves multiplication
by the pulled-back section. Hence the section complex comparison is semilinear
for Γ(S,V) to Γ(U,O_U). Fix a and its pullback b. Multiplication by b is a
natural endomorphism of the forgetful functor from global-section modules;
multiplication by a is a natural endomorphism of evaluation at V. The degreewise
identity gives a commuting square on the three-term complexes. Apply homology
and use homologyMap_mapNatTrans to identify its scalar endomorphisms through
the two mapHomologyIso comparisons. Cancelling the comparison inverses gives
b acting before T equal to a acting after T. Evaluate this equality at y.
This uses neither the augmentation nor resolution naturality: it is a statement
about the pinned degreewise section comparison. It also holds for p=0, empty
opens, and zero modules, since the same module maps and homology comparisons
are used in those cases. -/
theorem resolutionSectionsHomology_scalar
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (I : InjectiveResolution F)
    (p : ℕ) (V : S.Opens) (R : RestrictedResolutionSections I (f ⁻¹ᵁ V)) :
    let h := f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let T := (((RingedSpace.globalSectionsComplex R.resolution).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{u})).inv ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
        R.sections.hom ≫
      (((((SheafOfModules.forget S.ringCatSheaf).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).sc p).mapHomologyIso
          (PresheafOfModules.toPresheaf S.ringCatSheaf.obj ⋙
            (CategoryTheory.evaluation S.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V))).hom
    ∀ (a : Γ(S, V)) (y : (RingedSpace.globalSectionsComplex R.resolution).homology p),
      T ((((Scheme.ΓSpecIso Γ(S, V)).inv ≫ h.appTop).hom a) • y) = a •
        (show (sectionCohomologyPresheaf K p).obj (op V) from T y) := by
  let h := f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ
  let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let A := RingedSpace.globalSectionsComplex R.resolution
  let B := ((SheafOfModules.forget S.ringCatSheaf).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K
  let E := PresheafOfModules.toPresheaf S.ringCatSheaf.obj ⋙
    (CategoryTheory.evaluation S.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
  dsimp only
  intro a y
  let b := ((Scheme.ΓSpecIso Γ(S, V)).inv ≫ h.appTop).hom a
  let τ : E ⟶ E := {
    app := fun M ↦ ((M.obj (op V)).smul a).asHom
    naturality := fun M N q ↦ by
      ext z
      exact ((q.app (op V)).hom.map_smul a z).symm }
  have hn (n : ℕ) (z : A.X n) :
      R.sections.hom.f n (b • z) =
        a • (show (K.X n).val.obj (op V) from R.sections.hom.f n z) := by
    let φ := R.comparison.hom.f n
    let j := restrictAppIso (f ⁻¹ᵁ V).ι (I.cocomplex.X n) ⊤
    let e := (eqToHom (f ⁻¹ᵁ V).ι_image_top.symm).op
    change Γ(R.resolution.cocomplex.X n, ⊤) at z
    rw [R.components]
    change (I.cocomplex.X n).presheaf.map e (j.hom (Hom.app φ ⊤ (b • z))) =
      a • (show Γ(((pushforward f).obj (I.cocomplex.X n)), V) from
        (I.cocomplex.X n).presheaf.map e (j.hom (Hom.app φ ⊤ z)))
    rw [Hom.app_smul]
    rw [smul_restrictAppIso_hom_apply]
    change (I.cocomplex.X n).val.map e (_ • _) = _
    rw [PresheafOfModules.map_smul]
    have hb : (Scheme.ΓSpecIso Γ(S, V)).inv ≫ h.appTop ≫
        (f ⁻¹ᵁ V).topIso.hom = f.app V := by
      simp only [h, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop,
        Category.assoc, Iso.inv_hom_id_assoc, Scheme.Hom.appTop,
        Scheme.Hom.resLE_app_top, Iso.inv_hom_id,
        Category.comp_id, Scheme.Hom.appLE]
      simp only [homOfLE_refl, op_id]
      rw [X.presheaf.map_id, Category.comp_id]
    have hb' := ConcreteCategory.congr_hom hb a
    let w : (I.cocomplex.X n).val.obj (op (f ⁻¹ᵁ V)) :=
      (I.cocomplex.X n).val.map e (j.hom (Hom.app φ ⊤ z))
    change (X.presheaf.map e).hom ((f ⁻¹ᵁ V).ι.appIso ⊤ |>.inv.hom b) • w =
      (f.app V).hom a • w
    have hw := congrArg (fun r : Γ(X, f ⁻¹ᵁ V) ↦ r • w) hb'
    erw [Scheme.Opens.ι_appIso, Iso.refl_inv, CommRingCat.hom_id]
    change (X.presheaf.map e).hom b • w = (f.app V).hom a • w
    exact hw
  let q := (HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) p).map
    R.sections.hom
  have hq : (A.sc p).mapNatTrans (ModuleCat.smulNatTrans _ b).asHom ≫ q =
      q ≫ (B.sc p).mapNatTrans τ := by
    apply ShortComplex.hom_ext
    · ext z
      exact hn _ z
    · ext z
      exact hn _ z
    · ext z
      exact hn _ z
  have hc := homology_scalar_transport (A.sc p) (B.sc p) E q b τ hq
  exact congrArg (fun g ↦ g y) hc

end AlgebraicGeometry.Scheme.Modules

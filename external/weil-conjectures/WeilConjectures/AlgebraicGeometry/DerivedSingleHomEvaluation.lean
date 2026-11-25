/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap

/-! # Derived single-source Hom evaluation

Source: Stacks Project, duality.tex, Tags 0BUZ, 0BV0, and 0AX3.
-/

@[expose] public section
universe u wY
open CategoryTheory Opposite AlgebraicGeometry
namespace AlgebraicGeometry

private theorem localized_hom_evaluation
    {C E : Type*} [Category* C] [Category* E]
    (Q : C ⥤ E) (W : MorphismProperty C) [Q.IsLocalization W]
    (H : Cᵒᵖ ⥤ C ⥤ C) (D : Eᵒᵖ × E ⥤ E)
    (T : C ⥤ C) (η : 𝟭 C ⟶ T) (L : C) (e : H.obj (op L) ≅ 𝟭 C)
    (d : Q.op.prod Q ⋙ D ≅ (𝟭 _).prod T ⋙ Functor.uncurry.obj H ⋙ Q)
    (hη : ∀ M, IsIso (Q.map (η.app M))) :
    ∃ j : (Functor.curry.obj D).obj (op (Q.obj L)) ≅ 𝟭 E,
      ∀ (B : C) (k : L ⟶ B) (I : C)
        (_ : IsIso (Q.map ((H.obj (op B)).map (η.app I)))),
      ∃ c : Q.obj ((H.obj (op B)).obj I) ≅ D.obj (op (Q.obj B), Q.obj I),
        c.hom ≫ D.map ((Q.map k).op, 𝟙 (Q.obj I)) ≫ j.hom.app (Q.obj I) =
          Q.map ((H.map k.op).app I ≫ e.hom.app I) := by
  let r : Q ≅ T ⋙ Q :=
    NatIso.ofComponents (fun M ↦ asIso (Q.map (η.app M))) (by
      intro M N f
      simpa only [Functor.comp_map, Functor.id_map, asIso_hom, Functor.map_comp] using
        congrArg Q.map (η.naturality f))
  let a := (Functor.curryObjProdComp Q.op Q D).app (op L)
  let b : (Functor.curry.obj
      ((𝟭 _).prod T ⋙ Functor.uncurry.obj H ⋙ Q)).obj (op L) ≅
      T ⋙ H.obj (op L) ⋙ Q :=
    NatIso.ofComponents (fun M ↦ Iso.refl _) (by
      intro M N f
      simp)
  let t := a.symm ≪≫ ((Functor.curry.mapIso d).app (op L)) ≪≫ b ≪≫
    Functor.isoWhiskerLeft T (Functor.isoWhiskerRight e Q) ≪≫
      (Functor.associator T (𝟭 _) Q).symm ≪≫
      Functor.isoWhiskerRight T.rightUnitor Q ≪≫ r.symm ≪≫ Q.rightUnitor.symm
  let ff := Localization.fullyFaithfulWhiskeringLeft Q W E
  let j := ff.preimageIso t
  refine ⟨j, ?_⟩
  intro B k I hI
  have := hI
  let c := asIso (Q.map ((H.obj (op B)).map (η.app I))) ≪≫
    (d.app (op B, I)).symm
  refine ⟨c, ?_⟩
  have hj : j.hom.app (Q.obj I) = t.hom.app I :=
    congrArg (fun f ↦ f.app I) (ff.map_preimage t.hom)
  have ht : t.hom.app I = d.hom.app (op L, I) ≫
      Q.map (e.hom.app (T.obj I)) ≫ inv (Q.map (η.app I)) := by
    simp [t, a, b, r]
  rw [hj, ht]
  change (Q.map ((H.obj (op B)).map (η.app I)) ≫ d.inv.app (op B, I)) ≫
    D.map (show (op (Q.obj B), Q.obj I) ⟶ (op (Q.obj L), Q.obj I) from
      ((Q.map k).op, 𝟙 (Q.obj I))) ≫
      d.hom.app (op L, I) ≫ Q.map (e.hom.app (T.obj I)) ≫
        inv (Q.map (η.app I)) = Q.map ((H.map k.op).app I ≫ e.hom.app I)
  have hd : d.inv.app (op B, I) ≫
      D.map (show (op (Q.obj B), Q.obj I) ⟶ (op (Q.obj L), Q.obj I) from
        ((Q.map k).op, 𝟙 (Q.obj I))) =
      Q.map ((H.map k.op).app (T.obj I)) ≫ d.inv.app (op L, I) := by
    simpa using (d.inv.naturality
      (show (op B, I) ⟶ (op L, I) from (k.op, 𝟙 I))).symm
  rw [Category.assoc, reassoc_of% hd]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← Q.map_comp_assoc, ← Q.map_comp_assoc]
  rw [(H.map k.op).naturality, Category.assoc, e.hom.naturality]
  simp only [Functor.id_map, Q.map_comp, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency true in
-- The scheme/module comparison has several nested functor types.
/-- A natural unit-Hom identification descends to the derived category together
with K-injective comparisons compatible with every map out of the unit.

Source: Stacks Project, sites-cohomology.tex, Section 08J7 and Lemma 0A95;
the localization calculation in lem-sc-affine-hom-kinjective-evaluation, step 1.
(blueprint: lem-sc-derived-single-hom-evaluation).

Proof:
1. Write I0 for the functorial K-injective replacement and eta for its augmentation.
   Use derivedInternalHom_comparison for this replacement. Fixing its first
   variable at O_Y[0], compose it with e on I0 and the inverse of Q(eta).
   This gives a natural isomorphism after precomposition by Q. Fully faithful
   precomposition by Q descends it to j on the derived category.
2. For a K-injective complex I, eta_I is a quasi-isomorphism between K-injectives.
   Hence Hom(B[0], eta_I) is a quasi-isomorphism by quasiIso_homComplex_map.
   Compose Q of this map with the inverse of the comparison at (B[0], I) to
   obtain c from the unresolved Hom complex to derived internal Hom.
3. Naturality of the comparison in the first variable moves precomposition by
   k[0] across it. The comparison at O_Y[0] cancels against its inverse in j.
   Naturality of the Hom-complex bifunctor moves eta across precomposition by k.
   Finally naturality of e moves eta across evaluation, and Q(eta) cancels
   with its inverse. The resulting composite is Q of precomposition by k[0]
   followed by e_I, as asserted. No finiteness or boundedness hypothesis is used;
   the zero map k, zero B, zero ring and empty scheme obey the same identities. -/
theorem derived_single_hom_evaluation (Y : Scheme.{u})
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (e : (homComplexFunctor (R := Y.toRingedSpace.sheaf)).obj
        (op ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
            (SheafOfModules.unit Y.ringCatSheaf))) ≅ 𝟭 _) :
    ∃ j : (Functor.curry.obj
        (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              (SheafOfModules.unit Y.ringCatSheaf))) ≅ 𝟭 _,
      ∀ (B : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
        (k : SheafOfModules.unit Y.ringCatSheaf ⟶ B)
        (I : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (_ : I.IsKInjective),
      ∃ c : DerivedCategory.Q.obj
          (homComplex (R := Y.toRingedSpace.sheaf)
            ((CochainComplex.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj B) I) ≅
          (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
            (op ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj B),
              DerivedCategory.Q.obj I),
        c.hom ≫ (derivedInternalHom (Opens.grothendieckTopology Y)
            Y.toRingedSpace.sheaf).map
          (((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map k).op,
            𝟙 (DerivedCategory.Q.obj I)) ≫
          j.hom.app (DerivedCategory.Q.obj I) =
            DerivedCategory.Q.map
              (((homComplexFunctor (R := Y.toRingedSpace.sheaf)).map
                (((CochainComplex.singleFunctor
                  (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map k).op)).app I ≫
                    e.hom.app I)  := by
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  have : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let T := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  -- Elaborate the comparisons before unpacking their witnesses.
  have hd := derivedInternalHom_comparison.{u, wY}
    (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf T η
    (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2,
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M⟩)
  obtain ⟨d⟩ := hd
  have hη (M : CochainComplex A ℤ) : IsIso (DerivedCategory.Q.map (η.app M)) := by
    have : QuasiIso (η.app M) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2
    infer_instance
  have h := localized_hom_evaluation
    (C := CochainComplex A ℤ) (E := DerivedCategory A) (DerivedCategory.Q (C := A))
    (HomologicalComplex.quasiIso A (.up ℤ))
    (homComplexFunctor (R := Y.toRingedSpace.sheaf))
    (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)
    T η ((CochainComplex.singleFunctor A 0).obj
      (SheafOfModules.unit Y.ringCatSheaf)) e d hη
  obtain ⟨j, hj⟩ := h
  refine ⟨j, ?_⟩
  intro B k I hI
  have : I.IsKInjective := hI
  have : (T.obj I).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A I
  have : QuasiIso (η.app I) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A I).2
  let LB := (CochainComplex.singleFunctor A 0).obj B
  have : QuasiIso
      (((homComplexFunctor (R := Y.toRingedSpace.sheaf)).obj (op LB)).map (η.app I)) := by
    have hid := (homComplexFunctor (R := Y.toRingedSpace.sheaf)).map_id (op LB)
    simpa only [op_id, hid, NatTrans.id_app, Category.id_comp] using
      quasiIso_homComplex_map (R := Y.toRingedSpace.sheaf)
        (show I ⟶ T.obj I from η.app I) (𝟙 LB)
  exact hj LB ((CochainComplex.singleFunctor A 0).map k) I inferInstance

end AlgebraicGeometry

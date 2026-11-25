/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Homology.RingedSiteZerothHypercohomology
import WeilConjectures.Algebra.Homology.HomComplexHypercohomology
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Global sections of derived internal Hom

Source: Stacks Project, Lemma 21.35.1, Tag 08JA, global statement
(blueprint: lem-pur-rhom-global-sections).
-/

@[expose] public section

universe u₁ w₁ u v w

open CategoryTheory Opposite

namespace CategoryTheory

private theorem rhomGlobalSectionsHomComparison
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (I : CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (η : 𝟭 (CochainComplex A ℤ) ⟶ I)
    (hI : ∀ M, (I.obj M).IsKInjective)
    (hη : ∀ M, QuasiIso (η.app M)) :
    Nonempty (((HomotopyCategory.quotient A (ComplexShape.up ℤ)).op.prod
        (I ⋙ HomotopyCategory.quotient A (ComplexShape.up ℤ)) ⋙
        Functor.uncurry.obj preadditiveCoyoneda ⋙ AddCommGrpCat.uliftFunctor.{w, v}) ≅
      (DerivedCategory.Q.op.prod DerivedCategory.Q ⋙
        Functor.uncurry.obj preadditiveCoyoneda ⋙ AddCommGrpCat.uliftFunctor.{v, w})) := by
  classical
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let Q := DerivedCategory.Q (C := A)
  let σ := DerivedCategory.quotientCompQhIso A
  let H := Functor.uncurry.obj (preadditiveCoyoneda (C := DerivedCategory A))
  let HK := Functor.uncurry.obj
    (preadditiveCoyoneda (C := HomotopyCategory A (ComplexShape.up ℤ)))
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let V := AddCommGrpCat.uliftFunctor.{v, w}
  let B := q.op.prod (I ⋙ q) ⋙ HK ⋙ U
  let T := Q.op.prod Q ⋙ H ⋙ V
  have hi (M : CochainComplex A ℤ) : IsIso (Q.map (η.app M)) := by
    have := hη M
    infer_instance
  let t (P : (CochainComplex A ℤ)ᵒᵖ × CochainComplex A ℤ) :
      (DerivedCategory.Qh.obj (q.obj P.1.unop) ⟶
        DerivedCategory.Qh.obj (q.obj (I.obj P.2))) ≃+
      (Q.obj P.1.unop ⟶ Q.obj P.2) := by
    have := hi P.2
    exact
      { toEquiv := Iso.homCongr (σ.app P.1.unop)
          (σ.app (I.obj P.2) ≪≫ (asIso (Q.map (η.app P.2))).symm)
        map_add' := by intros; simp [Preadditive.comp_add, Preadditive.add_comp] }
  let e (P : (CochainComplex A ℤ)ᵒᵖ × CochainComplex A ℤ) : B.obj P ≃+ T.obj P :=
    AddEquiv.ulift.trans
      ((AddEquiv.ofBijective (DerivedCategory.Qh.mapAddHom)
        (by have := hI P.2; exact CochainComplex.IsKInjective.Qh_map_bijective _ _)).trans
        ((t P).trans AddEquiv.ulift.symm))
  let b : B ≅ T := NatIso.ofComponents (fun P ↦ (e P).toAddCommGrpIso) (by
    intro P P' f
    ext x
    apply ULift.ext
    dsimp [B, T, e, t, HK, H, U, V, Functor.uncurry,
      preadditiveCoyoneda, preadditiveCoyonedaObj, AddCommGrpCat.uliftFunctor,
      AddEquiv.toAddCommGrpIso, AddEquiv.ofBijective, Iso.homCongr,
      AddEquiv.ulift, Equiv.ulift, Functor.mapAddHom]
    have := hi P.2
    have := hi P'.2
    have hn : Q.map (I.map f.2) ≫ inv (Q.map (η.app P'.2)) =
        inv (Q.map (η.app P.2)) ≫ Q.map f.2 := by
      apply (cancel_epi (Q.map (η.app P.2))).mp
      rw [← Category.assoc, ← Q.map_comp, ← η.naturality f.2, Q.map_comp]
      simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id,
        IsIso.hom_inv_id_assoc, Functor.id_map]
    simp only [AddMonoidHom.mk'_apply, Functor.map_comp, Category.assoc]
    dsimp only [σ]
    rw [← DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
    rw [DerivedCategory.quotientCompQhIso_hom_naturality_assoc]
    rw [hn])
  exact ⟨b⟩

private theorem rhomGlobalSectionsOfComparison
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (I : CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (η : 𝟭 (CochainComplex A ℤ) ⟶ I)
    (hI : ∀ M, (I.obj M).IsKInjective)
    (hη : ∀ M, QuasiIso (η.app M))
    (F : (DerivedCategory A)ᵒᵖ × DerivedCategory A ⥤ AddCommGrpCat.{v})
    (d : DerivedCategory.Q.op.prod DerivedCategory.Q ⋙ F ≅
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).op.prod
        (I ⋙ HomotopyCategory.quotient A (ComplexShape.up ℤ)) ⋙
          Functor.uncurry.obj preadditiveCoyoneda) :
    ∃ e : ∀ P, F.obj P ≃+ (P.1.unop ⟶ P.2),
      ∀ P P' (f : P ⟶ P') (x : F.obj P),
        e P' (F.map f x) = f.1.unop ≫ e P x ≫ f.2 := by
  classical
  let Q := DerivedCategory.Q (C := A)
  let H := Functor.uncurry.obj (preadditiveCoyoneda (C := DerivedCategory A))
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let V := AddCommGrpCat.uliftFunctor.{v, w}
  obtain ⟨b⟩ := rhomGlobalSectionsHomComparison I η hI hη
  let d' : Q.op.prod Q ⋙ F ⋙ U ≅ Q.op.prod Q ⋙ H ⋙ V :=
    Functor.isoWhiskerRight d U ≪≫ b
  let W := (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).op.prod
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
  let z : F ⋙ U ≅ H ⋙ V :=
    (Localization.fullyFaithfulWhiskeringLeft (Q.op.prod Q) W _).preimageIso d'
  let E (P : (DerivedCategory A)ᵒᵖ × DerivedCategory A) :
      F.obj P ≃+ (P.1.unop ⟶ P.2) := AddEquiv.ulift.symm.trans
    ((z.app P).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift)
  refine ⟨E, ?_⟩
  intro P P' f x
  have hz := ConcreteCategory.congr_hom (z.hom.naturality f) (ULift.up x)
  have hz' := congrArg ULift.down hz
  change E P' (F.map f x) = (f.1.unop ≫ E P x) ≫ f.2 at hz'
  simpa only [Category.assoc] using hz'

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 40000 in
-- Additive Hom inference traverses the derived and sheaf categories in each repeated binder.
/-- The canonical additive identification `H⁰(C, R𝓗om(L, M)) ≃+ Hom_D(O)(L, M)`,
natural contravariantly in `L` and covariantly in `M`.

Source: Stacks Project, Lemma 21.35.1, Tag 08JA, global statement
(blueprint: lem-pur-rhom-global-sections).

Proof:
1. Choose a K-flat representative of `L` using `lem-pc-kflat-resolution` and a
   K-injective representative `I` of `M` using `prop-pur-kinjective-resolutions-exist`.
   By `def-pur-derived-internal-hom` and `lem-pur-rhom-well-defined`, their sheaf Hom
   complex represents `R𝓗om(L,M)` independently of the choices. It is K-injective
   by `lem-pur-hom-kflat-into-kinjective`, so its global sections compute `H⁰`.
2. By `def-pur-hom-complex`, sections of its degree-n term are families of linear
   maps `Lᵖ → Iᵖ⁺ⁿ` (the tensor-Hom identification at the unit). Its differential is
   `d_I f - (-1)^n f d_L`. Thus degree-zero cocycles are chain maps, and degree-zero
   coboundaries are null-homotopic maps. Its zeroth cohomology is consequently the
   additive group of maps in the homotopy category. Since `I` is K-injective,
   `lem-weil-pbc-kinjective-hom-derived` identifies this group with derived morphisms.
3. The map sends a chain map to its image in the localization. Composition commutes
   with localization and with changes of representatives (`lem-pur-rhom-well-defined`),
   proving independence of all choices and the naturality equation below. -/
theorem rhom_global_sections
    {C : Type u₁} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u₁})
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))] :
    ∃ e : ∀ P : (DerivedCategory (SheafOfModules.{u₁}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))ᵒᵖ ×
        DerivedCategory (SheafOfModules.{u₁}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)),
      ((ringedSiteZerothHypercohomology J R).obj ((derivedInternalHom J R).obj P)) ≃+
        (P.1.unop ⟶ P.2),
      ∀ (P P' : (DerivedCategory (SheafOfModules.{u₁}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))ᵒᵖ ×
          DerivedCategory (SheafOfModules.{u₁}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
        (f : P ⟶ P')
        (x : (ringedSiteZerothHypercohomology J R).obj ((derivedInternalHom J R).obj P)),
        e P' ((ringedSiteZerothHypercohomology J R).map ((derivedInternalHom J R).map f) x) =
          f.1.unop ≫ e P x ≫ f.2 := by
  classical
  let A := SheafOfModules.{u₁}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let : IsGrothendieckAbelian.{u₁} A := SheafOfModules.isGrothendieckAbelian _
  let I := CochainComplex.kInjectiveResolutionFunctor.{u₁} A
  let η := CochainComplex.toKInjectiveResolution.{u₁} A
  have hI (M : CochainComplex A ℤ) : (I.obj M).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u₁} A M
  have hη (M : CochainComplex A ℤ) : QuasiIso (η.app M) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u₁} A M).2
  let a := Classical.choice (homComplex_hypercohomology J R I hI)
  let c := Classical.choice
    (derivedInternalHom_comparison J R I η (fun M ↦ ⟨hη M, hI M⟩))
  exact rhomGlobalSectionsOfComparison I η hI hη
    (derivedInternalHom J R ⋙ ringedSiteZerothHypercohomology J R)
    (Functor.isoWhiskerRight c (ringedSiteZerothHypercohomology J R) ≪≫ a)

end CategoryTheory

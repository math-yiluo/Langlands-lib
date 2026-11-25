/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RhomGlobalSections
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteZerothHypercohomologyOfUniverses
import WeilConjectures.CategoryTheory.SmoothPurity.RhomHypercohomologyBridgeOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Global sections of derived internal Hom with independent site universes

Source: Stacks Project, Lemma 21.35.1, Tag 08JA, global statement
(blueprint: lem-pur-rhom-global-sections).

This is the same comparison as the publicly imported `rhom_global_sections`, with site
objects, site arrows and coefficient sizes independent. Both operations are the recorded
constructions on the actual site, with module universe `max c v r`.
-/

@[expose] public section

set_option autoImplicit false

universe c v r w

open CategoryTheory Opposite

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
-- The comparison checks naturality through several large localization functors.
/-- The natural additive identification of zeroth hypercohomology of derived internal Hom
with derived morphisms, without identifying the site object and morphism universes.
The sheafification instances are the canonical abelian-category infrastructure in a
universe containing the site; no flatness, boundedness or product-exactness is assumed.

Source: Stacks Project, Lemma 21.35.1, Tag 08JA, global statement
(blueprint: lem-pur-rhom-global-sections).

Proof:
1. Use the recorded independent-universe K-flat and K-injective resolutions on C.
   For a K-flat representative L and K-injective representative I of M, the sheaf Hom
   complex Hom(L,I) computes derivedInternalHomOfUniverses and is K-injective
   (Tags 0A95 and 0A96). Thus ringedSiteZerothHypercohomologyOfUniverses computes
   its zeroth cohomology by applying Hom_R(R,-) termwise.
2. Sections of degree n of this Hom complex are the families of linear maps
   L^p to I^(p+n), with differential d_I f - (-1)^n f d_L. Its degree-zero cycles
   are chain maps and its boundaries are null-homotopic maps. Consequently H0 is
   the additive group of homotopy classes. For arbitrary source representatives,
   a K-flat resolution and invariance in the first variable transport this comparison;
   common refinements of surjective resolutions show independence and naturality.
3. K-injectivity identifies these homotopy classes with derived morphisms via
   DerivedCategory.Qh.mapAddHom. Compose with quotientCompQhIso and the inverse
   of the localized resolution map. Naturality of that resolution and of the
   quotient comparison gives precomposition by f.1.unop and postcomposition by f.2.
4. Descend this natural additive comparison along Q.op.prod Q using the fully
   faithful whiskering functor for the product localization. ULift places the
   hypercohomology and derived-Hom groups in a common universe; remove those lifts
   from each component to obtain e and the displayed naturality equation.
All products and resolutions are taken in max c v r, which contains the site and
coefficient universes. This changes no section, differential or localization map.
Zero objects and the empty site require no additional hypotheses. -/
theorem rhom_global_sectionsOfUniverses
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))] :
    ∃ e : ∀ P : (DerivedCategory (SheafOfModules.{max c v r}
        ((sheafCompose J
          (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))ᵒᵖ ×
        DerivedCategory (SheafOfModules.{max c v r}
          ((sheafCompose J
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)),
      ((ringedSiteZerothHypercohomologyOfUniverses.{c, v, r, w} J R).obj
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj P)) ≃+ (P.1.unop ⟶ P.2),
      ∀ (P P' : (DerivedCategory (SheafOfModules.{max c v r}
          ((sheafCompose J
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))ᵒᵖ ×
          DerivedCategory (SheafOfModules.{max c v r}
            ((sheafCompose J
              (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
        (f : P ⟶ P')
        (x : (ringedSiteZerothHypercohomologyOfUniverses.{c, v, r, w} J R).obj
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj P)),
        e P' ((ringedSiteZerothHypercohomologyOfUniverses.{c, v, r, w} J R).map
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).map f) x) =
            f.1.unop ≫ e P x ≫ f.2 := by
  classical
  let A := SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
  let : IsGrothendieckAbelian.{max c v r} A :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  let I := CochainComplex.kInjectiveResolutionFunctor.{max c v r} A
  let η := CochainComplex.toKInjectiveResolution.{max c v r} A
  have hI (M : CochainComplex A ℤ) : (I.obj M).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r} A M
  have hη (M : CochainComplex A ℤ) : QuasiIso (η.app M) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r} A M).2
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let Q := DerivedCategory.Q (C := A)
  let σ := DerivedCategory.quotientCompQhIso A
  let H := Functor.uncurry.obj (preadditiveCoyoneda (C := DerivedCategory A))
  let HK := Functor.uncurry.obj
    (preadditiveCoyoneda (C := HomotopyCategory A (ComplexShape.up ℤ)))
  let U := AddCommGrpCat.uliftFunctor.{w, max c v r}
  let V := AddCommGrpCat.uliftFunctor.{max c v r, w}
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
  have hc : Nonempty (((𝟭 _).prod I ⋙
      Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ Q ⋙
        ringedSiteZerothHypercohomologyOfUniverses.{c, v, r, w} J R) ≅
      q.op.prod (I ⋙ q) ⋙ HK) := by
    exact rhom_hypercohomology_bridgeOfUniverses.{c, v, r, w} J R I hI
  obtain ⟨a⟩ := hc
  obtain ⟨c⟩ := derivedInternalHomOfUniverses_comparison.{c, v, r, w} J R I η (fun M ↦ ⟨hη M, hI M⟩)
  let F := derivedInternalHomOfUniverses.{c, v, r, w} J R ⋙
    ringedSiteZerothHypercohomologyOfUniverses.{c, v, r, w} J R ⋙ U
  let G := H ⋙ V
  let d : Q.op.prod Q ⋙ F ≅ Q.op.prod Q ⋙ G :=
    Functor.isoWhiskerRight c (ringedSiteZerothHypercohomologyOfUniverses.{c, v, r, w} J R ⋙ U) ≪≫
      Functor.isoWhiskerRight a U ≪≫ b
  let W := (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).op.prod
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
  let z : F ≅ G :=
    (Localization.fullyFaithfulWhiskeringLeft (Q.op.prod Q) W _).preimageIso d
  let E (P : (DerivedCategory A)ᵒᵖ × DerivedCategory A) :
      ((ringedSiteZerothHypercohomologyOfUniverses.{c, v, r, w} J R).obj
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj P)) ≃+
        (P.1.unop ⟶ P.2) := AddEquiv.ulift.symm.trans
    ((z.app P).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift)
  refine ⟨E, ?_⟩
  intro P P' f x
  have hz := ConcreteCategory.congr_hom (z.hom.naturality f) (ULift.up x)
  simpa [E, F, G, H, U, V, Functor.uncurry, preadditiveCoyoneda,
    preadditiveCoyonedaObj, AddCommGrpCat.uliftFunctor, AddEquiv.ulift,
    Equiv.ulift, Iso.addCommGroupIsoToAddEquiv, AddCommGrpCat.Hom.hom, Category.assoc]
    using congrArg ULift.down hz

end CategoryTheory

import Langlands.Cohomology.AcyclicResolution.ComparisonPostcomposition
import Langlands.AlgebraicGeometry.Modules.AbelianSheafPushforwardComparison
import Langlands.AlgebraicGeometry.Modules.DerivedBaseChange

/-! # Relative module cohomology and actual abelian-sheaf pushforward -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison

open PushforwardInjectiveAcyclic

variable {X Y : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R)

/-- The actual relative sections and absolute sections have the same underlying group. -/
def relativeGlobalSectionsForgetIso :
    DerivedSections.relativeGlobalSections f ⋙
        forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ≅
      DerivedSections.globalSections X ⋙
        forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun _ => Iso.refl _)

/-- Forgetting the relative scalar action on cohomology compares canonically
with right-derived underlying absolute sections. -/
def forgetRelativeDerivedSectionsIso (n : ℕ) :
    DerivedSections.relativeCohomology f n ⋙
        forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ≅
      (DerivedSections.globalSections X ⋙
        forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).rightDerived n :=
  exactPostcompIso (DerivedSections.relativeGlobalSections f)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) _
    (relativeGlobalSectionsForgetIso f ≪≫ (Functor.leftUnitor _).symm) n

/-- The canonical comparison of actual relative module cohomology with
right-derived global sections of the underlying abelian sheaf. -/
def relativeCohomologyIso (M : X.Modules) (n : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
        ((DerivedSections.relativeCohomology f n).obj M) ≅
      ((AbelianSheafDerivedSections.globalSections X.toTopCat).rightDerived n).obj
        ((toAbSheaf X).obj M) := by
  haveI := isIso_compComparison (F := toAbSheaf X)
    (AbelianSheafDerivedSections.globalSections X.toTopCat) (globalSectionsIso X) M
    (isZero_rightDerived_toAbSheaf X M)
    (fun J _ q => isZero_rightDerived_globalSections_of_injective X J q) n
  exact (forgetRelativeDerivedSectionsIso f n).app M ≪≫
    asIso (compComparison (F := toAbSheaf X)
      (AbelianSheafDerivedSections.globalSections X.toTopCat)
      (globalSectionsIso X) M (isZero_rightDerived_toAbSheaf X M) n)

/-- The relative forgetting comparison is computed on the same chosen
injective resolution as the existing exact-target comparison. -/
lemma forgetRelativeDerivedSectionsIso_app (M : X.Modules) (n : ℕ) :
    (forgetRelativeDerivedSectionsIso f n).app M =
      DerivedPlus.rightDerivedCompIsoOfResolution
        (DerivedSections.relativeGlobalSections f)
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
        (relativeGlobalSectionsForgetIso f) (injectiveResolution M) n := by
  apply Iso.ext
  exact (Category.comp_id _).trans
    (DerivedPlus.compIsoOfResolution_id_hom _ _ _ _ _)

private lemma forgetDerivedSectionsIso_app (M : X.Modules) (n : ℕ) :
    (forgetDerivedSectionsIso X n).app M =
      DerivedPlus.rightDerivedCompIsoOfResolution
        (DerivedSections.globalSections X)
        (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u})
        (Iso.refl _) (injectiveResolution M) n := by
  apply Iso.ext
  have he : (Iso.refl (DerivedSections.globalSections X ⋙
      forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u})) ≪≫
        (Functor.leftUnitor _).symm = (Functor.leftUnitor _).symm := Iso.refl_trans _
  have h := DerivedPlus.compIsoOfResolution_id_hom
    (DerivedSections.globalSections X)
    (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u})
    (Iso.refl _) (injectiveResolution M) n
  rw [he] at h
  exact (Category.comp_id _).trans h

/-- Restricting the source scalars, then forgetting them, recovers exactly the
published comparison for underlying absolute module cohomology. -/
lemma forgetRelativeDerivedSectionsIso_restrictScalars (M : X.Modules) (n : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        ((DerivedSections.relativeCohomologyRestrictScalarsIso f n).hom.app M) ≫
      (forgetRelativeDerivedSectionsIso f n).hom.app M =
        (forgetDerivedSectionsIso X n).hom.app M := by
  let c : forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} ≅
      ModuleCat.restrictScalars (DerivedSections.structureRingHom f).hom ⋙
        forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} :=
    NatIso.ofComponents (fun _ => Iso.refl _)
  have he : Functor.isoWhiskerRight (DerivedSections.relativeGlobalSectionsIso f).symm
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (DerivedSections.globalSections X) c.symm ≪≫
      Iso.refl _ = relativeGlobalSectionsForgetIso f := by
    ext Q x
    rfl
  have ht := DerivedPlus.rightDerivedCompIsoOfResolution_hom_comp
    (DerivedSections.globalSections X)
    (ModuleCat.restrictScalars (DerivedSections.structureRingHom f).hom)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
    (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}) c
    (DerivedSections.relativeGlobalSectionsIso f) (Iso.refl _)
    (injectiveResolution M) n
  rw [he, ← forgetRelativeDerivedSectionsIso_app f M n,
    ← DerivedSections.relativeCohomologyRestrictScalarsIso_app f n M,
    ← forgetDerivedSectionsIso_app M n] at ht
  change (forgetRelativeDerivedSectionsIso f n).hom.app M =
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        ((DerivedSections.relativeCohomologyRestrictScalarsIso f n).inv.app M) ≫
      𝟙 _ ≫ (forgetDerivedSectionsIso X n).hom.app M at ht
  erw [Category.id_comp] at ht
  rw [ht, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The actual relative module/sheaf comparison recovers the unchanged
absolute comparison after the published scalar restriction isomorphism. -/
lemma relativeCohomologyIso_restrictScalars (M : X.Modules) (n : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        ((DerivedSections.relativeCohomologyRestrictScalarsIso f n).hom.app M) ≫
      (relativeCohomologyIso f M n).hom = (cohomologyIso X M n).hom := by
  simp only [relativeCohomologyIso, cohomologyIso, Iso.trans_hom, asIso_hom,
    Iso.app_hom]
  rw [reassoc_of% forgetRelativeDerivedSectionsIso_restrictScalars f M n]

/-- The relative module/sheaf comparison is natural in its actual coefficient module. -/
@[reassoc]
lemma relativeCohomologyIso_hom_naturality {M N : X.Modules} (a : M ⟶ N) (n : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        ((DerivedSections.relativeCohomology f n).map a) ≫
      (relativeCohomologyIso f N n).hom =
    (relativeCohomologyIso f M n).hom ≫
      ((AbelianSheafDerivedSections.globalSections X.toTopCat).rightDerived n).map
        ((toAbSheaf X).map a) := by
  have h₁ := (forgetRelativeDerivedSectionsIso f n).hom.naturality a
  have h₂ := compComparison_naturality (F := toAbSheaf X)
    (AbelianSheafDerivedSections.globalSections X.toTopCat) (globalSectionsIso X) a
    (isZero_rightDerived_toAbSheaf X M) (isZero_rightDerived_toAbSheaf X N) n
  simp only [Functor.comp_map] at h₁
  simp only [relativeCohomologyIso, Iso.trans_hom, asIso_hom, Iso.app_hom, Category.assoc]
  rw [reassoc_of% h₁, h₂]

/-- Changing only the specified affine base ring leaves the underlying
abelian-sheaf comparison unchanged. -/
lemma relativeCohomologyIso_baseRing {S : CommRingCat.{u}} (φ : R ⟶ S)
    (f' : X ⟶ Spec S) (w : f = f' ≫ Spec.map φ) (M : X.Modules) (n : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        ((DerivedSections.relativeCohomologyBaseRingIso φ f f' w n).hom.app M) ≫
      (relativeCohomologyIso f' M n).hom = (relativeCohomologyIso f M n).hom := by
  apply (cancel_epi ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
    ((DerivedSections.relativeCohomologyRestrictScalarsIso f n).hom.app M))).1
  rw [relativeCohomologyIso_restrictScalars]
  rw [← Functor.map_comp_assoc]
  simp only [DerivedSections.relativeCohomologyBaseRingIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Iso.hom_inv_id_app_assoc,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  change (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
      (𝟙 _ ≫ (ModuleCat.restrictScalars φ.hom).map
        ((DerivedSections.relativeCohomologyRestrictScalarsIso f' n).hom.app M)) ≫
    (relativeCohomologyIso f' M n).hom = _
  erw [Category.id_comp]
  exact relativeCohomologyIso_restrictScalars f' M n

variable (h : X ⟶ Y) (g : Y ⟶ Spec R)

/-- Exact forgetting of relative target scalars preserves the canonical
pushforward comparison, with the specified underlying section maps. -/
lemma forgetRelativeDerivedSectionsIso_pushforward (M : X.Modules)
    (hM : ∀ q : ℕ, IsZero ((DerivedSections.higherDirectImage h (q + 1)).obj M)) (n : ℕ) :
    (forgetRelativeDerivedSectionsIso (h ≫ g) n).hom.app M ≫
        compComparison (DerivedSections.globalSections Y ⋙
          forget₂ (ModuleCat.{u} Γ(Y, ⊤)) AddCommGrpCat.{u})
          (underlyingPushforwardSectionsIso h) M hM n =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
          (DerivedSections.pushforwardComparison h g M hM n) ≫
        (forgetRelativeDerivedSectionsIso g n).hom.app
          ((Scheme.Modules.pushforward h).obj M) := by
  exact compComparison_postcomp (F := Scheme.Modules.pushforward h)
    (DerivedSections.relativeGlobalSections g)
    (DerivedSections.relativeGlobalSectionsCompIso h g)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
    (relativeGlobalSectionsForgetIso g ≪≫ (Functor.leftUnitor _).symm)
    (relativeGlobalSectionsForgetIso (h ≫ g) ≪≫ (Functor.leftUnitor _).symm)
    (underlyingPushforwardSectionsIso h) M hM (by intro Q; ext x; rfl) n

variable [IsClosedImmersion h] [IsIso h.base]

local instance :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.base).IsEquivalence :=
  (Picard.UnitSheafPushforward.sheafPushforwardEquivalence
    (C := AddCommGrpCat.{u}) (asIso h.base)).isEquivalence_functor

local instance : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.base).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The actual relative module pushforward comparison agrees with the actual
abelian-sheaf comparison through the canonical forgetting isomorphisms. -/
lemma relativeCohomologyIso_pushforward (M : X.Modules) (n : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        (DerivedSections.pushforwardComparison h g M
          (fun q => closedImmersionHigherDirectImageVanishing X Y h inferInstance M q) n) ≫
      (relativeCohomologyIso g ((Scheme.Modules.pushforward h).obj M) n).hom ≫
      ((AbelianSheafDerivedSections.globalSections Y.toTopCat).rightDerived n).map
        ((pushforwardForgetIso h).hom.app M) =
    (relativeCohomologyIso (h ≫ g) M n).hom ≫
      compComparison (F := TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.base)
        (AbelianSheafDerivedSections.globalSections Y.toTopCat)
        (abelianPushforwardSectionsIso h) ((toAbSheaf X).obj M)
        (isZero_rightDerived_abelianPushforward h ((toAbSheaf X).obj M)) n := by
  have hp := forgetRelativeDerivedSectionsIso_pushforward h g M
    (fun q => closedImmersionHigherDirectImageVanishing X Y h inferInstance M q) n
  have ht := twoStepComparison_pushforward h M n
  simp only [twoStepComparison] at ht
  simp only [relativeCohomologyIso, Iso.trans_hom, asIso_hom, Iso.app_hom,
    Category.assoc]
  rw [← reassoc_of% hp]
  exact congrArg ((forgetRelativeDerivedSectionsIso (h ≫ g) n).hom.app M ≫ ·) ht

end Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison

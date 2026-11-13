import Langlands.AlgebraicGeometry.Modules.RelativeDerivedHomPullback

/-! # Compatibility of the relative derived Hom comparison with pullback -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry Opposite
open Langlands.Cohomology

namespace Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison

open PushforwardInjectiveAcyclic
open AbelianSheafCohomologyPullback AbelianSheafDerivedSections
open DerivedSectionsHomComparison

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
set_option maxRecDepth 2048

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)}

lemma relativeSectionsHomIso_pullback (f : Y ⟶ X) (M : Y.left.Modules)
    (s : (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
      ((DerivedSections.relativeGlobalSections X.hom).obj
        ((Scheme.Modules.pushforward f.left).obj M))) :
    (constantPullbackIso f.left.base).inv.app (AddCommGrpCat.of (ULift ℤ)) ≫
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} f.left.base).map
        ((relativeSectionsHomIso X.hom).hom.app _ s) ≫
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
        f.left.base).counit.app ((toAbSheaf Y.left).obj M) =
    (relativeSectionsHomIso Y.hom).hom.app M
      ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        ((DerivedSections.relativePushforwardSectionsIso f).hom.app M) s) := by
  apply ((homGlobalSectionsIso Y.left.toTopCat).app
    ((toAbSheaf Y.left).obj M)).addCommGroupIsoToAddEquiv.injective
  change (homGlobalSectionsIso Y.left.toTopCat).hom.app _ _ =
    (homGlobalSectionsIso Y.left.toTopCat).hom.app _ _
  erw [homGlobalSectionsIso_pullback_counit]
  change (homGlobalSectionsIso X.left.toTopCat).hom.app
      ((toAbSheaf X.left).obj ((Scheme.Modules.pushforward f.left).obj M))
      ((homGlobalSectionsIso X.left.toTopCat).inv.app
        ((toAbSheaf X.left).obj ((Scheme.Modules.pushforward f.left).obj M)) s) =
    (homGlobalSectionsIso Y.left.toTopCat).hom.app ((toAbSheaf Y.left).obj M)
      ((homGlobalSectionsIso Y.left.toTopCat).inv.app ((toAbSheaf Y.left).obj M)
        (((DerivedSections.relativePushforwardSectionsIso f).hom.app M) s))
  simp only [Iso.inv_hom_id_app_apply]
  change s = ((DerivedSections.relativePushforwardSectionsIso f).hom.app M) s
  change s = (((Scheme.Modules.pushforwardCongr f.w).hom.app M).app ⊤).hom
    ((((Scheme.Modules.pushforwardComp f.left X.hom).hom.app M).app ⊤).hom s)
  simp only [Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app]
  change s = M.presheaf.map (𝟙 _) s
  rw [M.presheaf.map_id]
  rfl

/-- Inverse image followed by the actual counit on the complex of integer-sheaf Homs. -/
def relativeHomComplexPullback (f : Y ⟶ X) (K : CochainComplex Y.left.Modules ℤ) :
    ((preadditiveCoyoneda.obj (op (constantIntegers X.left.toTopCat))).mapHomologicalComplex
      (.up ℤ)).obj (((toAbSheaf X.left).mapHomologicalComplex (.up ℤ)).obj
        (((Scheme.Modules.pushforward f.left).mapHomologicalComplex (.up ℤ)).obj K)) ⟶
    ((preadditiveCoyoneda.obj (op (constantIntegers Y.left.toTopCat))).mapHomologicalComplex
      (.up ℤ)).obj (((toAbSheaf Y.left).mapHomologicalComplex (.up ℤ)).obj K) :=
  EquivariantComposite.homComplexMap
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} f.left.base)
    ((constantPullbackIso f.left.base).inv.app (AddCommGrpCat.of (ULift ℤ)))
    (((toAbSheaf X.left).mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.pushforward f.left).mapHomologicalComplex (.up ℤ)).obj K)) ≫
    ((preadditiveCoyoneda.obj (op (constantIntegers Y.left.toTopCat))).mapHomologicalComplex
      (.up ℤ)).map (relativePullbackCounit f K)

lemma relativeSectionsComplexIso_pullback (f : Y ⟶ X)
    (K : CochainComplex.Plus Y.left.Modules) :
    (sectionsComplexIso (DerivedSections.relativeGlobalSections X.hom)
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (toAbSheaf X.left)
      (constantIntegers X.left.toTopCat) (relativeSectionsHomIso X.hom)
      (((Scheme.Modules.pushforward f.left).mapCochainComplexPlus.obj K).obj)).hom ≫
      EquivariantComposite.homComplexMap
        (TopCat.Sheaf.pullback AddCommGrpCat.{u} f.left.base)
        ((constantPullbackIso f.left.base).inv.app (AddCommGrpCat.of (ULift ℤ)))
        (((toAbSheaf X.left).mapHomologicalComplex (.up ℤ)).obj
          (((Scheme.Modules.pushforward f.left).mapHomologicalComplex (.up ℤ)).obj K.obj)) ≫
      ((preadditiveCoyoneda.obj (op (constantIntegers Y.left.toTopCat))).mapHomologicalComplex
        (.up ℤ)).map (relativePullbackCounit f K.obj) =
    ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).map
        (DerivedSections.pullbackSectionsComplexIso f K).hom.hom ≫
      (sectionsComplexIso (DerivedSections.relativeGlobalSections Y.hom)
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (toAbSheaf Y.left)
        (constantIntegers Y.left.toTopCat) (relativeSectionsHomIso Y.hom) K.obj).hom := by
  apply HomologicalComplex.hom_ext
  intro i
  ext s
  have hc : (DerivedSections.pullbackSectionsComplexIso f K).hom.hom.f i =
      (DerivedSections.relativePushforwardSectionsIso f).hom.app (K.obj.X i) := by
    change ((CochainComplex.Plus.ι (ModuleCat.{u} R)).map
      (DerivedSections.pullbackSectionsComplexIso f K).hom).f i = _
    simp only [DerivedSections.pullbackSectionsComplexIso,
      Functor.preimageIso_hom, Functor.map_preimage]
    rfl
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, hc]
  dsimp [sectionsComplexIso, EquivariantComposite.homComplexMap,
    relativePullbackCounit, preadditiveCoyoneda]
  simp only [Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f]
  dsimp only [Iso.refl, NatTrans.id_app]
  change (constantPullbackIso f.left.base).inv.app (AddCommGrpCat.of (ULift ℤ)) ≫
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} f.left.base).map
        ((relativeSectionsHomIso X.hom).hom.app
          ((Scheme.Modules.pushforward f.left).obj (K.obj.X i)) s) ≫
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
        f.left.base).counit.app ((toAbSheaf Y.left).obj (K.obj.X i)) =
    (relativeSectionsHomIso Y.hom).hom.app (K.obj.X i)
      ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        ((DerivedSections.relativePushforwardSectionsIso f).hom.app (K.obj.X i)) s)
  exact relativeSectionsHomIso_pullback f (K.obj.X i) s

end Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison

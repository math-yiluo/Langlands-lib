/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SheafHExtResolutionSectionsIso
import WeilConjectures.AlgebraicGeometry.ExtPullbackHomComplex
import WeilConjectures.AlgebraicGeometry.ConstantSheafPullbackTranspose

/-! # Pullback computed on a comparison of injective resolutions -/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Scheme Etale

private lemma sectionsEquiv_naturality (X : Scheme.{u})
    {F F' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : F ⟶ F')
    (a : SheafPullbackResolution.ZSheaf X ⟶ F) :
    SheafPullbackResolution.sectionsEquiv X F' (a ≫ f) =
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).map f
        (SheafPullbackResolution.sectionsEquiv X F a) := by
  dsimp only [SheafPullbackResolution.sectionsEquiv, AddEquiv.trans_apply,
    Adjunction.homAddEquiv_apply]
  rw [Adjunction.homEquiv_naturality_right]
  rfl

/-- Ext pullback is the homology map of the unit section map followed by the lift.
Source: Stacks Project, Tag 01F8, equations 01F9 and 01FA; site version Tag 08J6.
(blueprint: lem-weil-pbc-ext-pullback-resolution-sections)

Proof: Represent an Ext class by a cocycle from the constant integer sheaf into
its chosen injective resolution. Apply exact inverse image, precompose with the
constant-sheaf comparison, and postcompose with φ. The augmentation homotopy hφ
identifies this cocycle with the Ext pullback, using localization on the K-injective
target. Evaluation at 1 transforms the inverse-image cocycle into the section-unit
map η; evaluation commutes with φ by naturality of the constant-sheaf adjunction.
Thus the two maps of cocycles agree after evaluation. Coboundaries map to
coboundaries, so this equality descends to homology. The explicit extSectionsIso
is exactly the Ext/resolution equivalence followed by this evaluation map.
Degree zero has no incoming boundaries in the chosen resolutions; the same
argument works there, and for the zero sheaf and empty schemes. -/
theorem extPullback_resolution_sections
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (φ : ((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplex (.up ℤ)).obj
      (injectiveResolution G).cochainComplex ⟶
      (injectiveResolution ((upperStar AddCommGrpCat.{u + 1} g').obj G)).cochainComplex)
    (hφ : Nonempty (Homotopy
      (((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplex (.up ℤ)).map
        (injectiveResolution G).ι' ≫ φ)
      ((HomologicalComplex.singleMapHomologicalComplex
        (upperStar AddCommGrpCat.{u + 1} g') (.up ℤ) 0).hom.app G ≫
        (injectiveResolution ((upperStar AddCommGrpCat.{u + 1} g').obj G)).ι'))) :
    let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
    let Γ' := Sheaf.Γ X'.smallEtaleTopology AddCommGrpCat.{u + 1}
    let L := upperStar AddCommGrpCat.{u + 1} g'
    let η : Γ ⟶ L ⋙ Γ' :=
      (Functor.leftUnitor Γ).inv ≫
        Functor.whiskerRight (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g').unit Γ ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft L (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g').hom
    let b := (NatTrans.mapHomologicalComplex η (.up ℤ)).app
      (injectiveResolution G).cochainComplex ≫
        (Γ'.mapHomologicalComplex (.up ℤ)).map φ
    (SheafPullbackResolution.extSectionsIso X G q).hom ≫
        HomologicalComplex.homologyMap b (q : ℤ) =
      AddCommGrpCat.ofHom (cohomologyMap g' G q) ≫
        (SheafPullbackResolution.extSectionsIso X' (L.obj G) q).hom := by
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let Γ' := Sheaf.Γ X'.smallEtaleTopology AddCommGrpCat.{u + 1}
  let L := upperStar AddCommGrpCat.{u + 1} g'
  let η : Γ ⟶ L ⋙ Γ' :=
    (Functor.leftUnitor Γ).inv ≫
      Functor.whiskerRight (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g').unit Γ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft L (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g').hom
  let R := injectiveResolution G
  let R' := injectiveResolution (L.obj G)
  let α := (upperStarConstantSheafIso AddCommGrpCat.{u + 1} g').inv.app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let c := SheafPullbackResolution.homPullbackMap L α R.cochainComplex R'.cochainComplex φ
  let b := (NatTrans.mapHomologicalComplex η (.up ℤ)).app R.cochainComplex ≫
    (Γ'.mapHomologicalComplex (.up ℤ)).map φ
  have htranspose (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (a : SheafPullbackResolution.ZSheaf X ⟶ F) :
      SheafPullbackResolution.sectionsEquiv X' (L.obj F) (α ≫ L.map a) =
        (η.app F) (SheafPullbackResolution.sectionsEquiv X F a) := by
    have h := constantSheaf_pullback_transpose g'
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) F a
    dsimp only [SheafPullbackResolution.sectionsEquiv, AddEquiv.trans_apply,
      Adjunction.homAddEquiv_apply]
    rw [h]
    rfl
  have hc : c ≫ (SheafPullbackResolution.complexSectionsIso X' R'.cochainComplex).hom =
      (SheafPullbackResolution.complexSectionsIso X R.cochainComplex).hom ≫ b := by
    ext n a
    obtain ⟨a, rfl⟩ :=
      CochainComplex.HomComplex.Cochain.fromSingleMk_surjective a n (zero_add n)
    change SheafPullbackResolution.sectionsEquiv X' (R'.cochainComplex.X n)
        (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add n)
          (CochainComplex.HomComplex.Cochain.fromSingleMk
            (α ≫ L.map (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add n)
              (CochainComplex.HomComplex.Cochain.fromSingleMk a (zero_add n))) ≫ φ.f n)
            (zero_add n))) =
      Γ'.map (φ.f n) ((η.app (R.cochainComplex.X n))
        (SheafPullbackResolution.sectionsEquiv X (R.cochainComplex.X n)
          (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add n)
            (CochainComplex.HomComplex.Cochain.fromSingleMk a (zero_add n)))))
    simp only [CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
    rw [← Category.assoc, sectionsEquiv_naturality, htranspose]
    rfl
  have hh := congrArg
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) (q : ℤ)).map) hc
  simp only [HomologicalComplex.homologyFunctor_map,
    HomologicalComplex.homologyMap_comp] at hh
  dsimp only [b] at hh
  have he := SheafPullbackResolution.extPullback_homComplex g' G q φ hφ
  dsimp only [SheafPullbackResolution.extSectionsIso,
    SheafPullbackResolution.classSectionsIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  simp only [HomologicalComplex.homologyFunctor_map, Category.assoc]
  rw [← hh]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ f ≫ HomologicalComplex.homologyMap
      (SheafPullbackResolution.complexSectionsIso X' R'.cochainComplex).hom (q : ℤ)) he

end AlgebraicGeometry

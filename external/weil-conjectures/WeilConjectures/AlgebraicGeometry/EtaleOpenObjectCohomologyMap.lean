/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! # The canonical open-object cohomology map

Source: Stacks Project, Cohomology on Sites, Tag 03F3.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The actual free abelian representable sheaf functor used in object cohomology.
Source: Stacks Project, Tag 03F3, sections represented by free abelian sheaves.
(blueprint: def-weil-pbc-etale-open-object-cohomology-map) -/
def etaleOpenFreeSheaf (X : Scheme.{u}) :
    X.Etale ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  uliftYoneda.{u + 1} ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}

/-- The identity generator, transported to sections of the inverse image on the open.
Source: Stacks Project, Tag 03F3, the free-sheaf/Yoneda adjunction.
(blueprint: def-weil-pbc-etale-open-object-cohomology-map) -/
def etaleOpenFreeSheafSection {X : Scheme.{u}} (U : X.Opens) :
    ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj
      ((etaleOpenFreeSheaf X).obj (Scheme.Etale.mk U.ι))).obj.obj
        (op (Scheme.Etale.mk (𝟙 U.toScheme))) := by
  let A := (etaleOpenFreeSheaf X).obj (Scheme.Etale.mk U.ι)
  let b : U.toScheme.Etale := Scheme.Etale.mk (𝟙 U.toScheme)
  let a := (MorphismProperty.Over.map ⊤ (inferInstance : Etale U.ι)).obj b
  let t : a ⟶ Scheme.Etale.mk U.ι :=
    MorphismProperty.Over.homMk (𝟙 U.toScheme) (by rfl)
  let s : A.obj.obj (op a) :=
    (toSheafify X.smallEtaleTopology
      (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk U.ι) ⋙ AddCommGrpCat.free)).app
        (op a) (FreeAbelianGroup.of ⟨t⟩)
  exact ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} U.ι
    inferInstance).inv.app A).hom.app (op b) s

/-- The constant-to-pulled-back-free-sheaf map classifying the identity generator.
Source: Stacks Project, Tag 03F3, the sections adjunction at the terminal object.
(blueprint: def-weil-pbc-etale-open-object-cohomology-map) -/
def etaleOpenFreeSheafUnit {X : Scheme.{u}} (U : X.Opens) :
    (constantSheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶
      (Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj
        ((etaleOpenFreeSheaf X).obj (Scheme.Etale.mk U.ι)) :=
  (constantSheafAdj U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}
    (show IsTerminal (Scheme.Etale.mk (𝟙 U.toScheme)) from
      IsTerminal.ofUniqueHom
        (fun a ↦ MorphismProperty.Over.homMk a.hom (Category.comp_id _))
        (fun a f ↦ by
          apply MorphismProperty.Over.Hom.ext
          exact (Category.comp_id _).symm.trans (MorphismProperty.Over.w f)))).homEquiv _ _ |>.symm
        ((AddCommGrpCat.uliftZMultiplesAddEquiv _).symm (etaleOpenFreeSheafSection U))

/-- Pull an Ext class back to the open and precompose with the identity generator.
This is a real construction, with no choice of a comparison isomorphism.
Source: Stacks Project, Tag 03F3, identification of section complexes.
(blueprint: def-weil-pbc-etale-open-object-cohomology-map) -/
def etaleOpenObjectCohomologyMap {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (U : X.Opens) :
    ((Functor.flip ((etaleOpenFreeSheaf X).op ⋙ Abelian.extFunctor q)).obj F).obj
        (op (Scheme.Etale.mk U.ι)) ⟶
      AddCommGrpCat.of (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj F) q) :=
  AddCommGrpCat.ofHom
    (((Abelian.Ext.mk₀ (etaleOpenFreeSheafUnit U)).precomp _ (zero_add q)).comp
      ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).mapExtAddHom _ F q))

end AlgebraicGeometry

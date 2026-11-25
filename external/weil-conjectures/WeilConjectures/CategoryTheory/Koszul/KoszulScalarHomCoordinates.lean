/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Strict.StrictScalarKoszulInstances
import all WeilConjectures.CategoryTheory.Koszul.KoszulScalarTensorComparison
import all WeilConjectures.CategoryTheory.Koszul.KoszulScalarHomDiagram
import all WeilConjectures.Algebra.Homology.StrictScalarHom.StrictScalarHomChain

/-! # KoszulScalarHomCoordinates for strict Koszul comparison

Source: Stacks Project, Tags 0A0E and 0913.
(blueprint: lem-f5-koszul-scalar-hom-coordinates).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.FlatScalarKoszul

variable {S : Type u} [SmallCategory S] {J : GrothendieckTopology S}
variable {R B : Sheaf J CommRingCat.{u}}

open MonoidalCategory
open scoped CategoryTheory.Prod

attribute [local irreducible] homComplexFunctor
  SheafOfModules.tensorObjIsoSheafification PresheafOfModules.sheafificationAdjunction
  Localization.Monoidal.tensorBifunctor

attribute [local instance] gradedTensorCache gradedGoodTensorLeftCache
  gradedGoodTensorRightCache gradedFourCache tensorPreservesEmptyLeftCache
  tensorPreservesEmptyRightCache cachedModuleMonoidal cachedModuleSymmetric
  cachedModulePreadditive cachedModuleClosed cachedComplexMonoidal
  cachedComplexBraided cachedComplexClosed

/-- Evaluate the Hom projection on a specified positive Koszul basis vector.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-koszul-scalar-hom-coordinates). -/
def homCoordinate (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (a : Fin r → (O.obj ⋙ forget CommRingCat).sections) (N : ringedSiteComplex O)
    (m : ℕ) (e : Fin r → Bool) (n : ℤ) :
    (homComplex (R := O) ((ringedKoszulDiagram O r a).obj m) N).X n ⟶
      N.X (n + degree r e) :=
  homComplexπ ((ringedKoszulDiagram O r a).obj m) N n (degree r e)
      (n + degree r e) (add_comm _ _) ≫
    SheafOfModules.homObjMap (R := O) (positiveBasis O r a m e) (𝟙 _) ≫
    (SheafOfModules.homObjUnitIso (R := O) (N.X (n + degree r e))).hom

/-- Coordinates of the scalar Koszul Hom comparison.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
Proof step 1: Expand the Hom coordinate and comparison into theta and precomposition by the
positive comparison. Apply the normalized theta local-evaluation formula to identify the
coordinate after theta.
Proof step 2: The assumed positive basis identity replaces the image of the R basis by the B
basis after the unit isomorphism. Naturality of the module Hom maps and unit evaluation cancels
this unit isomorphism. Reassociate the composites to obtain restricted B Hom coordinate.
(blueprint: lem-f5-koszul-scalar-hom-coordinates). -/
private theorem homDiagramComparison_coordinates (φ : R ⟶ B) (r : ℕ)
    (a : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (e : ringedKoszulDiagram R r a ⋙
      (extension φ).mapHomologicalComplex (.up ℤ) ≅
        ringedKoszulDiagram B r (imageSections φ a))
    (hb : ∀ (m : ℕ) (b : Fin r → Bool),
      (extension φ).map (positiveBasis R r a m b) ≫ (e.hom.app m).f (degree r b) =
        (SheafOfModules.scalarExtensionUnitIso φ).hom ≫
          positiveBasis B r (imageSections φ a) m b)
    (N : ringedSiteComplex B) (m : ℕ) (b : Fin r → Bool) (n : ℤ) :
    ((homDiagramComparison φ r a e N).hom.app (op m)).f n ≫
        homCoordinate R r a ((restrictComplex φ).obj N) m b n =
      (restriction φ).map (homCoordinate B r (imageSections φ a) N m b n) := by
  have hb' (U : Sᵒᵖ) :
      ((e.hom.app m).f (degree r b)).val.app U
        (SheafOfModules.scalarExtensionSection.{u, u, u, u} φ
          (((ringedKoszulDiagram R r a).obj m).X (degree r b)) U 1
          ((positiveBasis R r a m b).val.app U (1 : R.obj.obj U))) =
        (positiveBasis B r (imageSections φ a) m b).val.app U (1 : B.obj.obj U) := by
    have h := congrArg (fun f ↦ f.val.app U
      (SheafOfModules.scalarExtensionSection.{u, u, u, u} φ (one R) U
        (1 : B.obj.obj U) (1 : R.obj.obj U))) (hb m b)
    change ((e.hom.app m).f (degree r b)).val.app U
        ((SheafOfModules.changeOfRingsHomOfUniverses.{u, u, u, u} φ _
          (positiveBasis R r a m b)).val.app U _) =
      (positiveBasis B r (imageSections φ a) m b).val.app U
        ((SheafOfModules.scalarExtensionUnitIso φ).hom.val.app U _) at h
    simpa only [SheafOfModules.scalarExtension_map_tmul,
      SheafOfModules.scalarExtensionUnitIso_tmul, map_one, one_mul] using h
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  change SheafOfModules.StrictScalarHom.evaluate
      ((ringedKoszulDiagram R r a).obj m) ((restrictComplex φ).obj N)
      n (degree r b) (n + degree r b) (add_comm _ _) U
      ((((homDiagramComparison φ r a e N).hom.app (op m)).f n).val.app U g)
      ((positiveBasis R r a m b).val.app U (1 : R.obj.obj U)) =
    SheafOfModules.StrictScalarHom.evaluate
      ((ringedKoszulDiagram B r (imageSections φ a)).obj m) N
      n (degree r b) (n + degree r b) (add_comm _ _) U g
      ((positiveBasis B r (imageSections φ a) m b).val.app U (1 : B.obj.obj U))
  change SheafOfModules.StrictScalarHom.evaluate _ _ _ _ _ _ U
      (((SheafOfModules.StrictScalarHom.canonicalData.{u, u, u} φ).theta _ N).hom.f n
        |>.val.app U
          ((((homComplexFunctor (R := B)).map (e.hom.app m).op).app N).f n
            |>.val.app U g)) _ = _
  rw [(SheafOfModules.StrictScalarHom.canonicalData.{u, u, u} φ).theta_evaluate]
  have he := homComplexFunctor_map_f_π (e.hom.app m) (𝟙 N)
    n (degree r b) (n + degree r b) (add_comm _ _)
  simp only [Functor.map_id, Category.comp_id, HomologicalComplex.id_f] at he
  change _ = _
  have hev := congrArg (fun f ↦
    (((f.val.app U g).app (op (Over.mk (𝟙 U.unop)))).hom
      (SheafOfModules.scalarExtensionSection.{u, u, u, u} φ
        (((ringedKoszulDiagram R r a).obj m).X (degree r b)) U 1
        ((positiveBasis R r a m b).val.app U (1 : R.obj.obj U))))) he
  change _ = _ at hev
  exact hev.trans (congrArg
    (SheafOfModules.StrictScalarHom.evaluate _ N n (degree r b)
      (n + degree r b) (add_comm _ _) U g) (hb' U))

end CategoryTheory.FlatScalarKoszul

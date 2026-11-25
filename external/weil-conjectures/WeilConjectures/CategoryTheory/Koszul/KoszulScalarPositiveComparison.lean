/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Koszul.KoszulScalarTensorComparison
import all WeilConjectures.CategoryTheory.Koszul.KoszulScalarTensorComparison
import all WeilConjectures.CategoryTheory.ScalarKoszulTransport.KoszulScalarTransport

/-! # KoszulScalarPositiveComparison for strict Koszul comparison

Source: Stacks Project, Tags 0A0E and 0913.
(blueprint: lem-f5-koszul-scalar-positive-comparison).
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

/-- The scalar-extension unit isomorphism intertwines every scalar in the ordered list.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-koszul-scalar-positive-comparison). -/
theorem scalar_intertwines_any (φ : R ⟶ B)
    (s : (R.obj ⋙ forget CommRingCat).sections)
    (e : (extension φ).obj (one R) ≅ one B) :
    (extension φ).map (ringedKoszulScalar R s).asHom ≫ e.hom =
      e.hom ≫ (ringedKoszulScalar B (imageSections φ (fun _ : Fin 1 ↦ s) 0)).asHom := by
  let j := SheafOfModules.scalarExtensionUnitIso φ
  have hc :
      (ringedKoszulScalar B (imageSections φ (fun _ : Fin 1 ↦ s) 0)).asHom ≫
          (j.inv ≫ e.hom) =
        (j.inv ≫ e.hom) ≫
          (ringedKoszulScalar B (imageSections φ (fun _ : Fin 1 ↦ s) 0)).asHom := by
    rw [ScalarKoszulTransport.scalar_eq_smul]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((j.inv ≫ e.hom).val.app U).hom
      ((imageSections φ (fun _ : Fin 1 ↦ s) 0).val U • x) =
      (imageSections φ (fun _ : Fin 1 ↦ s) 0).val U •
        ((j.inv ≫ e.hom).val.app U).hom x
    exact ((j.inv ≫ e.hom).val.app U).hom.map_smul _ _
  calc
    _ = (extension φ).map (ringedKoszulScalar R s).asHom ≫ j.hom ≫ j.inv ≫ e.hom := by
      simp only [Iso.hom_inv_id_assoc]
    _ = j.hom ≫ (ringedKoszulScalar B
        (imageSections φ (fun _ : Fin 1 ↦ s) 0)).asHom ≫ j.inv ≫ e.hom := by
      rw [← Category.assoc, ← Category.assoc, scalar_intertwines]
      simp only [Category.assoc, j]
    _ = _ := by rw [← Category.assoc _ j.inv, Category.assoc, hc]; simp

private def positiveIso (φ : R ⟶ B) (r : ℕ)
    (a : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (H : ScalarKoszulTransport.TensorPullbackComparison
      ((extension φ).mapHomologicalComplex (.up ℤ))
      (ringedKoszulTensor R) (ringedKoszulTensor B)
      (ringedSiteRingComplex R) (ringedSiteRingComplex B)
      (ringedKoszulRightUnitIso R) (ringedKoszulRightUnitIso B))
    (u : ((extension φ).mapHomologicalComplex (.up ℤ)).obj
      (ringedSiteRingComplex R) ≅ ringedSiteRingComplex B) :
    ringedKoszulDiagram R r a ⋙ (extension φ).mapHomologicalComplex (.up ℤ) ≅
      ringedKoszulDiagram B r (imageSections φ a) := by
  induction r generalizing u with
  | zero =>
    exact NatIso.ofComponents (fun _ ↦ u) (by
      intro m n f
      simp [ringedKoszulDiagram])
  | succ r ih =>
    exact ScalarKoszulTransport.tensorDiagramIso H
      (ScalarKoszulTransport.factorsIso (extension φ) (a 0) (imageSections φ a 0)
        (ScalarKoszulTransport.rankOneIso (extension φ) u)
        (scalar_intertwines_any φ (a 0) _))
      (ih (fun i ↦ a i.succ) H.j)

private theorem positiveIso_projection (φ : R ⟶ B) (r : ℕ)
    (a : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (H : ScalarKoszulTransport.TensorPullbackComparison
      ((extension φ).mapHomologicalComplex (.up ℤ))
      (ringedKoszulTensor R) (ringedKoszulTensor B)
      (ringedSiteRingComplex R) (ringedSiteRingComplex B)
      (ringedKoszulRightUnitIso R) (ringedKoszulRightUnitIso B))
    (u : ((extension φ).mapHomologicalComplex (.up ℤ)).obj
      (ringedSiteRingComplex R) ≅ ringedSiteRingComplex B) (m : ℕ) :
    ((extension φ).mapHomologicalComplex (.up ℤ)).map
        (ringedKoszulProjection R r a m) ≫ u.hom =
      (positiveIso φ r a H u).hom.app m ≫
        ringedKoszulProjection B r (imageSections φ a) m := by
  induction r generalizing u with
  | zero => simp [positiveIso, ringedKoszulProjection]
  | succ r ih =>
    let P := extension φ
    let s := a 0
    let t := imageSections φ a 0
    have h : P.map (ringedKoszulScalar R s).asHom ≫
          (ScalarKoszulTransport.rankOneIso P u).hom =
        (ScalarKoszulTransport.rankOneIso P u).hom ≫ (ringedKoszulScalar B t).asHom :=
      scalar_intertwines_any φ s (ScalarKoszulTransport.rankOneIso P u)
    let e := ScalarKoszulTransport.factorsIso P s t (ScalarKoszulTransport.rankOneIso P u) h
    have hp := ScalarKoszulTransport.tensor_augmented H
      (ringedKoszulFactorProjection R s m)
      (ringedKoszulProjection R r (fun i ↦ a i.succ) m)
      (ringedKoszulFactorProjection B t m)
      (ringedKoszulProjection B r (imageSections φ (fun i ↦ a i.succ)) m)
      (e.app m) ((positiveIso φ r (fun i ↦ a i.succ) H H.j).app m) u
      (ScalarKoszulTransport.factorIso_projection P s t u h m)
      (ih (fun i ↦ a i.succ) H.j) (ScalarKoszulTransport.koszulRight_natural B)
    simpa only [← ScalarKoszulTransport.koszulUnit_right] using! hp

/-- Positive Koszul comparison preserving projection.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
Proof step 1: Intertwine the scalar maps for each entry of the list using the scalar-extension
generator formula. Powers intertwine by the generic power lemma.
Proof step 2: Apply the generic factor comparison and its transition naturality to obtain the
positive diagram isomorphism. Tensor induction and the normalized right-unit formula give the
projection identity. Pair the explicitly constructed isomorphism with this proved identity.
(blueprint: lem-f5-koszul-scalar-positive-comparison). -/
private def positiveComparison (φ : R ⟶ B) (r : ℕ)
    (a : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (H : ScalarKoszulTransport.TensorPullbackComparison
      ((extension φ).mapHomologicalComplex (.up ℤ))
      (ringedKoszulTensor R) (ringedKoszulTensor B)
      (ringedSiteRingComplex R) (ringedSiteRingComplex B)
      (ringedKoszulRightUnitIso R) (ringedKoszulRightUnitIso B))
    (u : ((extension φ).mapHomologicalComplex (.up ℤ)).obj
      (ringedSiteRingComplex R) ≅ ringedSiteRingComplex B) :
    {e : ringedKoszulDiagram R r a ⋙
          (extension φ).mapHomologicalComplex (.up ℤ) ≅
        ringedKoszulDiagram B r (imageSections φ a) //
      ∀ m : ℕ,
        ((extension φ).mapHomologicalComplex (.up ℤ)).map
            (ringedKoszulProjection R r a m) ≫ u.hom =
          e.hom.app m ≫ ringedKoszulProjection B r (imageSections φ a) m} :=
  ⟨positiveIso φ r a H u, fun m ↦ positiveIso_projection φ r a H u m⟩

end CategoryTheory.FlatScalarKoszul

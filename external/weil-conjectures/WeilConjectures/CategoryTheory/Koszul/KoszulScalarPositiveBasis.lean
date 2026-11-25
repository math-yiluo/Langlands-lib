/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Strict.StrictScalarKoszulInstances
import all WeilConjectures.CategoryTheory.ScalarKoszulTransport.KoszulScalarTransport
import all WeilConjectures.CategoryTheory.Koszul.KoszulScalarTensorComparison
import all WeilConjectures.CategoryTheory.Koszul.KoszulScalarPositiveComparison
import all WeilConjectures.CategoryTheory.Koszul.KoszulScalarFactorBasis

/-! # KoszulScalarPositiveBasis for strict Koszul comparison

Source: Stacks Project, Tags 0A0E and 0913.
(blueprint: lem-f5-koszul-scalar-positive-basis).
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

/-- The homogeneous summand inclusion is natural in both complexes.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-koszul-scalar-positive-basis). -/
theorem tensorInclusion_natural (O : Sheaf J CommRingCat.{u})
    (P Q P' Q' : ringedSiteComplex O) (f : P ⟶ P') (g : Q ⟶ Q')
    (p q n : ℤ) (h : p + q = n) :
    let : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
    let := SheafOfModules.monoidalCategory O
    let := SheafOfModules.symmetricCategory O
    let := Classical.choice (SheafOfModules.tensorClosed O).1
    let := SheafOfModules.monoidalClosed (R := O)
    CochainComplex.ιMapBifunctor P Q (tensor O) p q n h ≫
        (((ringedKoszulTensor O).map f).app Q).f n ≫
        (((ringedKoszulTensor O).obj P').map g).f n =
      tensorHom (f.f p) (g.f q) ≫
        CochainComplex.ιMapBifunctor P' Q' (tensor O) p q n h := by
  let : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := SheafOfModules.monoidalClosed (R := O)
  dsimp only
  change HomologicalComplex.ιMapBifunctor P Q (tensor O) (.up ℤ) p q n h ≫
    (HomologicalComplex.mapBifunctorMap f (𝟙 Q) (tensor O) (.up ℤ)).f n ≫
    (HomologicalComplex.mapBifunctorMap (𝟙 P') g (tensor O) (.up ℤ)).f n = _
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc,
    HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, curriedTensor_map_app,
    curriedTensor_obj_map, whiskerLeft_id, id_whiskerRight, tensorHom_def_assoc]
  erw [Category.id_comp, Category.id_comp]

private theorem tensorBasisTransport
    {D : Type*} [Category D] [MonoidalCategory D]
    {D' : Type*} [Category D'] [MonoidalCategory D']
    (F : D ⥤ D') {X Y Z : D} {X' Y' Z' : D'}
    (μ₀ : F.obj (𝟙_ D ⊗ 𝟙_ D) ⟶ F.obj (𝟙_ D) ⊗ F.obj (𝟙_ D))
    (μ : F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y)
    (j : F.obj (𝟙_ D) ⟶ 𝟙_ D')
    (x : 𝟙_ D ⟶ X) (y : 𝟙_ D ⟶ Y)
    (x' : 𝟙_ D' ⟶ X') (y' : 𝟙_ D' ⟶ Y')
    (f : F.obj X ⟶ X') (g : F.obj Y ⟶ Y')
    (i : X ⊗ Y ⟶ Z) (i' : X' ⊗ Y' ⟶ Z') (t : F.obj Z ⟶ Z')
    (hn : F.map (x ⊗ₘ y) ≫ μ = μ₀ ≫ (F.map x ⊗ₘ F.map y))
    (hi : F.map i ≫ t = μ ≫ (f ⊗ₘ g) ≫ i')
    (hx : F.map x ≫ f = j ≫ x') (hy : F.map y ≫ g = j ≫ y')
    (hu : F.map (λ_ (𝟙_ D)).inv ≫ μ₀ ≫ (j ⊗ₘ j) =
      j ≫ (λ_ (𝟙_ D')).inv) :
    F.map ((λ_ (𝟙_ D)).inv ≫ (x ⊗ₘ y) ≫ i) ≫ t =
      j ≫ (λ_ (𝟙_ D')).inv ≫ (x' ⊗ₘ y') ≫ i' := by
  simp only [F.map_comp, Category.assoc]
  rw [hi, ← Category.assoc (F.map (x ⊗ₘ y)), hn]
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc, hx, hy, ← tensorHom_comp_tensorHom_assoc,
    reassoc_of% hu]

private theorem inclusionCompositionCore {D : Type*} [Category D]
    {A B C E F G H : D} {a : A ⟶ B} {b : B ⟶ C} {c : C ⟶ E} {d : E ⟶ F}
    {m : A ⟶ G} {i : G ⟶ C} {t : G ⟶ H} {j : H ⟶ F}
    (h₁ : a ≫ b = m ≫ i) (h₂ : i ≫ c ≫ d = t ≫ j) :
    a ≫ b ≫ c ≫ d = m ≫ t ≫ j := by
  rw [← Category.assoc a, h₁, Category.assoc, h₂]

private theorem scalarTensorMap_inclusion (φ : R ⟶ B)
    (P Q : ringedSiteComplex R) (P' Q' : ringedSiteComplex B)
    (f : ((extension φ).mapHomologicalComplex (.up ℤ)).obj P ⟶ P')
    (g : ((extension φ).mapHomologicalComplex (.up ℤ)).obj Q ⟶ Q')
    (p q n : ℤ) (h : p + q = n) :
    let := SheafOfModules.monoidalCategory B
    (extension φ).map (CochainComplex.ιMapBifunctor P Q (tensor R) p q n h) ≫
        (((scalarTensorComparison φ).t P Q).hom ≫
          ((ringedKoszulTensor B).map f).app
            (((extension φ).mapHomologicalComplex (.up ℤ)).obj Q) ≫
          ((ringedKoszulTensor B).obj P').map g).f n =
      (extensionTensorIso φ (P.X p) (Q.X q)).hom ≫ (f.f p ⊗ₘ g.f q) ≫
        CochainComplex.ιMapBifunctor P' Q' (tensor B) p q n h := by
  let := SheafOfModules.monoidalCategory B
  dsimp only
  change (extension φ).map (CochainComplex.ιMapBifunctor P Q (tensor R) p q n h) ≫
      ((scalarTensorComparison φ).t P Q).hom.f n ≫
        (((ringedKoszulTensor B).map f).app
          (((extension φ).mapHomologicalComplex (.up ℤ)).obj Q)).f n ≫
        (((ringedKoszulTensor B).obj P').map g).f n = _
  exact inclusionCompositionCore (scalarTensor_inclusion φ P Q p q n h)
    (tensorInclusion_natural B _ _ P' Q' f g p q n h)

-- Normalize the recursive total-tensor basis and its component inclusions.
/-- Scalar extension of every ordered positive Koszul basis vector.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
Proof step 1: Prove naturality of total tensor inclusions by the mapBifunctor inclusion formula.
Transport inclusions across the total scalar tensor comparison using its inverse generator
formula.
Proof step 2: Induct on the length of the list. For zero entries use the rank-one comparison. In
the successor case rewrite positiveBasis as the total tensor inclusion of the factor and tail
basis; apply the factor basis comparison and the induction hypothesis. Tensor naturality, the
scalar tensor inclusion identity and the scalar unit tensor formula identify the resulting
composite with the image basis.
(blueprint: lem-f5-koszul-scalar-positive-basis). -/
private theorem scalarPositiveBasis (φ : R ⟶ B) (r : ℕ)
    (a : Fin r → (R.obj ⋙ forget CommRingCat).sections) (m : ℕ) (b : Fin r → Bool) :
    (extension φ).map (positiveBasis R r a m b) ≫
        (((positiveComparison φ r a (scalarTensorComparison φ)
          (scalarTensorComparison φ).j).1).hom.app m).f (degree r b) =
      (SheafOfModules.scalarExtensionUnitIso φ).hom ≫
        positiveBasis B r (imageSections φ a) m b := by
  let : IsGrothendieckAbelian.{u} (Modules R) := SheafOfModules.isGrothendieckAbelian _
  let : IsGrothendieckAbelian.{u} (Modules B) := SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory B
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.symmetricCategory B
  let := Classical.choice (SheafOfModules.tensorClosed R).1
  let := Classical.choice (SheafOfModules.tensorClosed B).1
  let := SheafOfModules.monoidalClosed (R := R)
  let := SheafOfModules.monoidalClosed (R := B)
  induction r with
  | zero =>
    apply (cancel_mono
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (one B)).hom).mp
    change (extension φ).map
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (one R)).inv ≫
      (scalarTensorComparison φ).j.hom.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (one B)).hom =
        (SheafOfModules.scalarExtensionUnitIso φ).hom
    have h := congrArg Iso.hom (scalarRankOne φ)
    simpa only [ScalarKoszulTransport.rankOneIso, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_inv, HomologicalComplex.Hom.isoApp_hom, Category.assoc] using! h
  | succ r ih =>
    have hR : positiveBasis R (r + 1) a m b =
        (λ_ (one R)).inv ≫
          (factorBasis R (a 0) m (b 0) ⊗ₘ
            positiveBasis R r (fun i ↦ a i.succ) m (fun i ↦ b i.succ)) ≫
          CochainComplex.ιMapBifunctor (ringedKoszulFactor R (a 0) m)
            ((ringedKoszulDiagram R r (fun i ↦ a i.succ)).obj m) (tensor R)
            (if b 0 then 1 else 0) (degree r (fun i ↦ b i.succ))
            (degree (r + 1) b) rfl := rfl
    have hB : positiveBasis B (r + 1) (imageSections φ a) m b =
        (λ_ (one B)).inv ≫
          (factorBasis B (imageSections φ a 0) m (b 0) ⊗ₘ
            positiveBasis B r (imageSections φ (fun i ↦ a i.succ)) m
              (fun i ↦ b i.succ)) ≫
          CochainComplex.ιMapBifunctor (ringedKoszulFactor B (imageSections φ a 0) m)
            ((ringedKoszulDiagram B r (imageSections φ (fun i ↦ a i.succ))).obj m)
            (tensor B) (if b 0 then 1 else 0) (degree r (fun i ↦ b i.succ))
            (degree (r + 1) b) rfl := rfl
    have he : (positiveComparison φ (r + 1) a (scalarTensorComparison φ)
        (scalarTensorComparison φ).j).1 =
        ScalarKoszulTransport.tensorDiagramIso (scalarTensorComparison φ)
          (ScalarKoszulTransport.factorsIso (extension φ) (a 0) (imageSections φ a 0)
            (ScalarKoszulTransport.rankOneIso (extension φ) (scalarTensorComparison φ).j)
            (scalar_intertwines_any φ (a 0) _))
          (positiveComparison φ r (fun i ↦ a i.succ) (scalarTensorComparison φ)
            (scalarTensorComparison φ).j).1 := rfl
    rw [hR, hB, he]
    simp only [ScalarKoszulTransport.tensorDiagramIso, NatIso.ofComponents_hom_app,
      Iso.trans_hom, Functor.mapIso_hom, Iso.prod, Iso.app_hom,
      Functor.uncurry_obj_map, Functor.prod'_obj, Functor.comp_obj,
      HomologicalComplex.comp_f]
    let PR := ringedKoszulFactor R (a 0) m
    let QR := (ringedKoszulDiagram R r (fun i ↦ a i.succ)).obj m
    let PB := ringedKoszulFactor B (imageSections φ a 0) m
    let QB := (ringedKoszulDiagram B r (imageSections φ (fun i ↦ a i.succ))).obj m
    let ef := ScalarKoszulTransport.factorIso (extension φ) (a 0)
      (imageSections φ a 0)
      (ScalarKoszulTransport.rankOneIso (extension φ) (scalarTensorComparison φ).j)
      (scalar_intertwines_any φ (a 0) _) m
    let et := (positiveComparison φ r (fun i ↦ a i.succ) (scalarTensorComparison φ)
      (scalarTensorComparison φ).j).1.app m
    refine tensorBasisTransport (extension φ)
      (extensionTensorIso φ (one R) (one R)).hom
      (extensionTensorIso φ (PR.X (if b 0 then 1 else 0))
        (QR.X (degree r (fun i ↦ b i.succ)))).hom
      (SheafOfModules.scalarExtensionUnitIso φ).hom
      (factorBasis R (a 0) m (b 0))
      (positiveBasis R r (fun i ↦ a i.succ) m (fun i ↦ b i.succ))
      (factorBasis B (imageSections φ a 0) m (b 0))
      (positiveBasis B r (imageSections φ (fun i ↦ a i.succ)) m (fun i ↦ b i.succ))
      (ef.hom.f (if b 0 then 1 else 0)) (et.hom.f (degree r (fun i ↦ b i.succ)))
      (CochainComplex.ιMapBifunctor PR QR (tensor R) (if b 0 then 1 else 0)
        (degree r (fun i ↦ b i.succ)) (degree (r + 1) b) rfl)
      (CochainComplex.ιMapBifunctor PB QB (tensor B) (if b 0 then 1 else 0)
        (degree r (fun i ↦ b i.succ)) (degree (r + 1) b) rfl) _
      (extensionTensorIso_natural φ _ _)
      (scalarTensorMap_inclusion φ PR QR PB QB ef.hom et.hom _ _ _ rfl)
      ?_ (ih (fun i ↦ a i.succ) (fun i ↦ b i.succ)) (scalarUnitTensor φ)
    dsimp only [ef]
    simpa only [scalarRankOne, imageSections] using! scalarFactorBasis φ (a 0) m (b 0)
      (ScalarKoszulTransport.rankOneIso (extension φ) (scalarTensorComparison φ).j)
      (scalar_intertwines_any φ (a 0) _)

attribute [local irreducible] positiveComparison scalarTensorComparison positiveBasis
  ringedKoszulDiagram ringedKoszulProjection ringedComplexTensorEvaluation

end CategoryTheory.FlatScalarKoszul

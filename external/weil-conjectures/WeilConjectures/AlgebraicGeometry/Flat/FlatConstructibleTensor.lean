/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Tensor with a flat constructible etale sheaf

Source: Stacks Project, Etale Cohomology, Tags 095I and 0961, with the exact-functor
cohomology computation of Homology, Tag 010N
(blueprint: lem-fd-flat-constructible-tensor).

The two auxiliary bifunctors express naturality in both the bounded constructible complex
and the flat constructible sheaf. They use the existing small-etale module-sheaf tensor,
its unbounded derived tensor, and the recorded finite-value constructibility predicates.

## Main definitions

* `flatConstructibleEtaleSheafProperty`: the two hypotheses on the sheaf factor.
* `flatConstructibleTensorCohomologyLeft`: cohomology after derived tensor.
* `flatConstructibleTensorCohomologyRight`: ordinary tensor after cohomology.

## Main statements

* `flatConstructibleTensor_cohomology_and_bounds`: the natural comparison,
  constructibility, bounded constructibility, and preservation of every cohomology interval.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

section NativeCollapse

variable {M : Type*} [Category* M] [Preadditive M] [HasZeroObject M]
  (T : M ⥤ M ⥤ M) [T.Additive] [∀ X, (T.obj X).Additive]
  [∀ A B : CochainComplex M ℤ, CochainComplex.HasMapBifunctor A B T]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc] private theorem nativeCollapse_ι (L : M) (E : CochainComplex M ℤ) (i : ℤ) :
    HomologicalComplex.ιMapBifunctor E ((CochainComplex.singleFunctor _ 0).obj L)
        T (.up ℤ) i 0 i (Int.add_zero i) ≫
      (CochainComplex.mapBifunctorSingle₂Iso T L E).hom.f i =
        (T.obj (E.X i)).map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L).hom := by
  dsimp [CochainComplex.mapBifunctorSingle₂Iso, CochainComplex.mapBifunctorSingle₁Iso,
    HomologicalComplex.Hom.isoOfComponents]
  erw [HomologicalComplex.ι_mapBifunctorFlipIso_inv_assoc]
  simp [CochainComplex.mapBifunctorSingle₁XIso, HomologicalComplex.singleObjXSelf]

set_option backward.isDefEq.respectTransparency false in
private theorem nativeCollapse_naturality {L L' : M} (g : L ⟶ L')
    {E E' : CochainComplex M ℤ} (f : E ⟶ E') :
    HomologicalComplex.mapBifunctorMap f
        ((CochainComplex.singleFunctor _ 0).map g) T (.up ℤ) ≫
      (CochainComplex.mapBifunctorSingle₂Iso T L' E').hom =
    (CochainComplex.mapBifunctorSingle₂Iso T L E).hom ≫
      ((T.flip.obj L).mapHomologicalComplex (.up ℤ)).map f ≫
        (NatTrans.mapHomologicalComplex (T.flip.map g) (.up ℤ)).app E' := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  by_cases hq : q = 0
  · subst q
    have hp : p = i := by simpa using hpq
    subst p
    simp only [HomologicalComplex.comp_f,
      HomologicalComplex.ι_mapBifunctorMap_assoc]
    erw [nativeCollapse_ι, nativeCollapse_ι_assoc]
    have hg : ((CochainComplex.singleFunctor M 0).map g).f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L').hom =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L).hom ≫ g := by
      change ((HomologicalComplex.single M (.up ℤ) 0).map g).f 0 ≫ _ = _
      simp [HomologicalComplex.single_map_f_self]
    simp [← Functor.map_comp, hg]
  · apply IsZero.eq_of_src
    exact Functor.map_isZero (T.obj _)
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)

end NativeCollapse

section NativeFlatTensor

universe v c

variable {C : Type c} [Category.{v} C] [Abelian C]
  [IsGrothendieckAbelian.{v} C] [HasDerivedCategory.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

omit [Abelian C] [IsGrothendieckAbelian.{v} C] [HasDerivedCategory.{v} C]
  [MonoidalPreadditive C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C] in
private theorem nativeFlat (L : C) (hL : exactFunctor _ _ (tensorRight L)) :
    ObjectProperty.flat L := by
  have := hL.preservesFiniteLimits
  have := hL.preservesFiniteColimits
  exact ⟨⟨preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight L).symm,
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight L).symm⟩, hL⟩

private theorem nativeTensorMuIso (L : C) (hL : exactFunctor _ _ (tensorRight L))
    (K : CochainComplex C ℤ) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q K
      ((CochainComplex.singleFunctor C 0).obj L)) := by
  let P := (CochainComplex.singleFunctor C 0).obj L
  have hP := (CochainComplex.kFlat_single_obj_iff_flat L 0).2 (nativeFlat L hL)
  have hP' := (HomotopyCategory.kFlat_quotient_obj_iff _).2 hP
  have hh := DerivedCategory.isIso_tensorRightCounit
    ((HomotopyCategory.quotient C (.up ℤ)).obj P) hP'
  have hm : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient C (.up ℤ)).obj K)
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)) := by
    exact inferInstanceAs (IsIso ((DerivedCategory.tensorRightCounit _).app _))
  change IsIso ((_ ⊗ₘ _) ≫
    (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫
      DerivedCategory.Qh.map
        (Functor.LaxMonoidal.μ (HomotopyCategory.quotient C (.up ℤ)) K P)) ≫ _)
  infer_instance

private noncomputable def nativeQTensorIso (L : C)
    (hL : exactFunctor _ _ (tensorRight L)) :
    DerivedCategory.Q ⋙ tensorRight ((DerivedCategory.singleFunctor C 0).obj L) ≅
      tensorRight ((CochainComplex.singleFunctor C 0).obj L) ⋙ DerivedCategory.Q := by
  let a : DerivedCategory.Q ⋙ tensorRight ((DerivedCategory.singleFunctor C 0).obj L) ⟶
      tensorRight ((CochainComplex.singleFunctor C 0).obj L) ⋙ DerivedCategory.Q :=
    { app K := Functor.LaxMonoidal.μ DerivedCategory.Q K _
      naturality K K' f := Functor.LaxMonoidal.μ_natural_left _ f _ }
  have : IsIso a := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact nativeTensorMuIso L hL
  exact asIso a

private noncomputable def nativeCohomologyComparison (L : C)
    (hL : exactFunctor _ _ (tensorRight L)) (K : CochainComplex C ℤ) (i : ℤ) :
    (K ⊗ (CochainComplex.singleFunctor C 0).obj L).homology i ≅ K.homology i ⊗ L := by
  have := hL.preservesFiniteLimits
  have := hL.preservesFiniteColimits
  exact HomologicalComplex.homologyMapIso
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) L K) i ≪≫
    (K.sc i).mapHomologyIso (tensorRight L)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def nativeCohomologyNatIso (L : C)
    (hL : exactFunctor _ _ (tensorRight L)) (i : ℤ) :
    tensorRight ((CochainComplex.singleFunctor C 0).obj L) ⋙
        HomologicalComplex.homologyFunctor C (.up ℤ) i ≅
      HomologicalComplex.homologyFunctor C (.up ℤ) i ⋙ tensorRight L := by
  have := hL.preservesFiniteLimits
  have := hL.preservesFiniteColimits
  refine NatIso.ofComponents (fun K ↦ nativeCohomologyComparison L hL K i) ?_
  intro K K' f
  dsimp only [nativeCohomologyComparison, Iso.trans_hom,
    HomologicalComplex.homologyMapIso]
  change HomologicalComplex.homologyMap (f ▷ _) i ≫ _ = _
  have hn := congrArg (fun t ↦ HomologicalComplex.homologyMap t i)
    (CochainComplex.mapBifunctorSingle₂Iso_hom_naturality (curriedTensor C) L f)
  simp only [HomologicalComplex.homologyMap_comp] at hn
  change HomologicalComplex.homologyMap (f ▷ _) i ≫ _ = _ at hn
  erw [← Category.assoc, hn, Category.assoc]
  have hf := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor C (.up ℤ) i).map f) (tensorRight L)
  change HomologicalComplex.homologyMap
      (((tensorRight L).mapHomologicalComplex (.up ℤ)).map f) i ≫
      ((K'.sc i).mapHomologyIso (tensorRight L)).hom =
    ((K.sc i).mapHomologyIso (tensorRight L)).hom ≫
      (HomologicalComplex.homologyMap f i ▷ L) at hf
  erw [hf]
  simp only [Category.assoc]
  rfl

private noncomputable def nativeRestrictedIso (L : C)
    (hL : exactFunctor _ _ (tensorRight L)) (i : ℤ) :
    DerivedCategory.Q ⋙ (tensorRight ((DerivedCategory.singleFunctor C 0).obj L) ⋙
        DerivedCategory.homologyFunctor C i) ≅
      DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor C i ⋙ tensorRight L) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (nativeQTensorIso L hL)
      (DerivedCategory.homologyFunctor C i) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors C i) ≪≫
    nativeCohomologyNatIso L hL i ≪≫
    Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors C i).symm _ ≪≫
    Functor.associator _ _ _

private noncomputable def nativeDerivedCohomologyIso (L : C)
    (hL : exactFunctor _ _ (tensorRight L)) (i : ℤ) :
    tensorRight ((DerivedCategory.singleFunctor C 0).obj L) ⋙
        DerivedCategory.homologyFunctor C i ≅
      DerivedCategory.homologyFunctor C i ⋙ tensorRight L :=
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    _ _ _ _ (nativeRestrictedIso L hL i)

set_option backward.isDefEq.respectTransparency false in
private theorem nativeDerivedCohomologyIso_comparison (L : C)
    (hL : exactFunctor _ _ (tensorRight L)) (K : CochainComplex C ℤ) (i : ℤ) :
    (DerivedCategory.homologyFunctor C i).map
        (Functor.LaxMonoidal.μ DerivedCategory.Q K
          ((CochainComplex.singleFunctor C 0).obj L)) ≫
      (DerivedCategory.homologyFunctorFactors C i).hom.app
        (K ⊗ (CochainComplex.singleFunctor C 0).obj L) ≫
      (nativeCohomologyComparison L hL K i).hom =
    (nativeDerivedCohomologyIso L hL i).hom.app (DerivedCategory.Q.obj K) ≫
      ((DerivedCategory.homologyFunctorFactors C i).hom.app K ▷ L) := by
  dsimp only [nativeDerivedCohomologyIso]
  erw [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso, Iso.refl_hom, NatTrans.id_app, Iso.refl_inv,
    Category.comp_id, Category.id_comp]
  dsimp only [nativeRestrictedIso, nativeQTensorIso, nativeCohomologyNatIso,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, NatIso.ofComponents_hom_app, asIso_hom]
  simp only [Category.comp_id, Category.id_comp, Category.assoc]
  erw [← comp_whiskerRight, Iso.inv_hom_id_app, id_whiskerRight, Category.comp_id]
  rfl

omit [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C] in
omit [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C] in
set_option backward.isDefEq.respectTransparency false in
private theorem nativeCohomologyComparison_right (L L' : C)
    (hL : exactFunctor _ _ (tensorRight L)) (hL' : exactFunctor _ _ (tensorRight L'))
    (g : L ⟶ L') (K : CochainComplex C ℤ) (i : ℤ) :
    HomologicalComplex.homologyMap
        (K ◁ (CochainComplex.singleFunctor C 0).map g) i ≫
      (nativeCohomologyComparison L' hL' K i).hom =
    (nativeCohomologyComparison L hL K i).hom ≫ (K.homology i ◁ g) := by
  have := hL.preservesFiniteLimits
  have := hL.preservesFiniteColimits
  have := hL'.preservesFiniteLimits
  have := hL'.preservesFiniteColimits
  have hn := nativeCollapse_naturality (curriedTensor C) g (𝟙 K)
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at hn
  have hh := congrArg (fun t ↦ HomologicalComplex.homologyMap t i) hn
  simp only [HomologicalComplex.homologyMap_comp] at hh
  dsimp only [nativeCohomologyComparison, Iso.trans_hom,
    HomologicalComplex.homologyMapIso]
  erw [← Category.assoc, hh]
  simp only [Category.assoc]
  have ht : HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex ((curriedTensor C).flip.map g) (.up ℤ)).app K) i ≫
        ((K.sc i).mapHomologyIso (tensorRight L')).hom =
      ((K.sc i).mapHomologyIso (tensorRight L)).hom ≫ (K.homology i ◁ g) := by
    change ShortComplex.homologyMap ((K.sc i).mapNatTrans
      ((curriedTensor C).flip.map g)) ≫ _ = _
    rw [ShortComplex.homologyMap_mapNatTrans]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  erw [ht]

attribute [local irreducible] nativeDerivedCohomologyIso nativeRestrictedIso
  nativeCohomologyNatIso nativeCohomologyComparison

set_option backward.isDefEq.respectTransparency false in
private theorem nativeDerivedCohomologyIso_right (L L' : C)
    (hL : exactFunctor _ _ (tensorRight L)) (hL' : exactFunctor _ _ (tensorRight L'))
    (g : L ⟶ L') (i : ℤ) :
    Functor.whiskerRight
        ((curriedTensor (DerivedCategory C)).flip.map
          ((DerivedCategory.singleFunctor C 0).map g))
        (DerivedCategory.homologyFunctor C i) ≫
      (nativeDerivedCohomologyIso L' hL' i).hom =
    (nativeDerivedCohomologyIso L hL i).hom ≫
      Functor.whiskerLeft (DerivedCategory.homologyFunctor C i)
        ((curriedTensor C).flip.map g) := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))
  intro E
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  let H := DerivedCategory.homologyFunctor C i
  let h := DerivedCategory.homologyFunctorFactors C i
  let σ := (curriedTensor (DerivedCategory C)).flip.map
    ((DerivedCategory.singleFunctor C 0).map g)
  let τ := (curriedTensor C).flip.map g
  apply (cancel_mono (h.hom.app E ▷ L')).1
  have hn : (nativeQTensorIso L hL).hom.app E ≫
      DerivedCategory.Q.map (E ◁ (CochainComplex.singleFunctor C 0).map g) =
    σ.app (DerivedCategory.Q.obj E) ≫ (nativeQTensorIso L' hL').hom.app E := by
    exact (Functor.LaxMonoidal.μ_natural_right DerivedCategory.Q E
      ((CochainComplex.singleFunctor C 0).map g)).symm
  have hc := nativeCohomologyComparison_right L L' hL hL' g E i
  have ht := τ.naturality (h.hom.app E)
  change (h.hom.app E ▷ L) ≫ (E.homology i ◁ g) =
    (H.obj (DerivedCategory.Q.obj E) ◁ g) ≫ (h.hom.app E ▷ L') at ht
  calc
    _ = H.map (σ.app (DerivedCategory.Q.obj E)) ≫
        (H.map ((nativeQTensorIso L' hL').hom.app E) ≫
          h.hom.app (E ⊗ (CochainComplex.singleFunctor C 0).obj L') ≫
          (nativeCohomologyComparison L' hL' E i).hom) := by
      erw [Category.assoc, ← nativeDerivedCohomologyIso_comparison L' hL' E i]
      rfl
    _ = H.map ((nativeQTensorIso L hL).hom.app E) ≫
        H.map (DerivedCategory.Q.map (E ◁ (CochainComplex.singleFunctor C 0).map g)) ≫
        h.hom.app (E ⊗ (CochainComplex.singleFunctor C 0).obj L') ≫
        (nativeCohomologyComparison L' hL' E i).hom := by
      erw [← H.map_comp_assoc, ← hn, H.map_comp, Category.assoc]
    _ = H.map ((nativeQTensorIso L hL).hom.app E) ≫
        h.hom.app (E ⊗ (CochainComplex.singleFunctor C 0).obj L) ≫
        (nativeCohomologyComparison L hL E i).hom ≫ (E.homology i ◁ g) := by
      erw [DerivedCategory.homologyFunctorFactors_hom_naturality_assoc]
      erw [hc]
      rfl
    _ = _ := by
      erw [reassoc_of% (nativeDerivedCohomologyIso_comparison L hL E i)]
      simp only [Category.assoc]
      erw [ht]
      rfl

private noncomputable def nativeComparison
    {D : Type*} [Category D] (P : ObjectProperty C)
    (hP : ∀ L, P L → exactFunctor _ _ (tensorRight L))
    (G : D ⥤ DerivedCategory C) (i : ℤ) :
    P.ι ⋙ DerivedCategory.singleFunctor C 0 ⋙ (curriedTensor (DerivedCategory C)).flip ⋙
        (Functor.whiskeringLeft _ _ _).obj G ⋙
        (Functor.whiskeringRight _ _ _).obj (DerivedCategory.homologyFunctor C i) ≅
      P.ι ⋙ (curriedTensor C).flip ⋙
        (Functor.whiskeringLeft _ _ _).obj (G ⋙ DerivedCategory.homologyFunctor C i) := by
  refine NatIso.ofComponents
    (fun L ↦ Functor.isoWhiskerLeft G
      (nativeDerivedCohomologyIso L.obj (hP L.obj L.property) i)) ?_
  intro L L' g
  apply NatTrans.ext
  funext K
  exact congr_app (nativeDerivedCohomologyIso_right L.obj L'.obj
    (hP L.obj L.property) (hP L'.obj L'.property) g.hom i) (G.obj K)

end NativeFlatTensor

attribute [local irreducible] nativeDerivedCohomologyIso nativeRestrictedIso
  nativeCohomologyNatIso nativeCohomologyComparison nativeQTensorIso nativeComparison

namespace AlgebraicGeometry.Etale

attribute [local irreducible] derivedTensor

end AlgebraicGeometry.Etale

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.InverseImageModuleFunctor
import WeilConjectures.AlgebraicGeometry.RelativeTensorPullbackComplexComparison
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # The relative tensor comparison on K-flat representatives

Source: Stacks Project, Cohomology, Lemma 20.27.4 (Tag 08DE).
(blueprint: lem-pc-relative-tensor-pullback-kflat-model)
-/

@[expose] public section

universe u w

open CategoryTheory MonoidalCategory Limits

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme

noncomputable local instance modelModuleTensor (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

private theorem relativeTensorPullback_kFlat_counit
    {X S : Scheme.{u}} (f : X ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (L : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
    (hL : CochainComplex.IsKFlatTensor (R := S.sheaf) L) :
    ∃ (G : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (hG : ∀ M, G.obj M = Modules.tensorPullbackObj f M)
      (_ : ∀ {M N} (a : M ⟶ N),
        G.map a = eqToHom (hG M) ≫ Modules.tensorPullbackMap f a ≫ eqToHom (hG N).symm)
      (_ : G.Additive),
      Nonempty ((derivedPullback f).obj (DerivedCategory.Q.obj L) ≅
        DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj L)) := by
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    G, hG, hGmap, hGadd, ε, _, _, hε⟩ := derivedPullback_spec f
  have := hGadd
  have := hε L hL
  refine ⟨G, hG, hGmap, hGadd, ⟨?_⟩⟩
  exact (derivedPullback f).mapIso
      ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (moduleRings S.toRingedSpace))).app L).symm ≪≫
    asIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj L)) ≪≫
    DerivedCategory.Qh.mapIso ((G.mapHomotopyCategoryFactors (.up ℤ)).app L) ≪≫
    (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))).app _

private theorem relativeTensorPullback_kFlat_tensor (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (A L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hA : CochainComplex.IsKFlatTensor (R := X.sheaf) A) :
    Nonempty (DerivedCategory.Q.obj A ⊗ DerivedCategory.Q.obj L ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor A L
        (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))))) := by
  obtain ⟨e⟩ := kFlat_derivedTensor_comparison_natIso X
    ((CategoryTheory.Functor.const (Discrete PUnit.{1})).obj A)
    ((CategoryTheory.Functor.const (Discrete PUnit.{1})).obj L) (fun _ ↦ hA)
  exact ⟨(e.app ⟨PUnit.unit⟩).app ⟨PUnit.unit⟩⟩

private theorem relativeTensorPullback_model_homology
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    (W : C ⥤ E) (V : D ⥤ E) [W.Additive] [V.Additive]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (Z : CochainComplex C ℤ) (Z' : CochainComplex D ℤ)
    (e : (W.mapHomologicalComplex (.up ℤ)).obj Z ≅
      (V.mapHomologicalComplex (.up ℤ)).obj Z') (i : ℤ) :
    Nonempty (W.obj (Z.homology i) ≅ V.obj (Z'.homology i)) :=
  ⟨((Z.sc i).mapHomologyIso W).symm ≪≫
    (HomologicalComplex.homologyFunctor E (.up ℤ) i).mapIso e ≪≫
    (Z'.sc i).mapHomologyIso V⟩

private theorem relativeTensorPullback_kFlat_derived
    {X S : Scheme.{u}} (f : X ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (A : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hA : CochainComplex.IsKFlatTensor (R := X.sheaf) A)
    (L : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
    (hL : CochainComplex.IsKFlatTensor (R := S.sheaf) L) :
    ∃ (G : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (hG : ∀ M, G.obj M = Modules.tensorPullbackObj f M)
      (_ : ∀ {M N} (a : M ⟶ N),
        G.map a = eqToHom (hG M) ≫ Modules.tensorPullbackMap f a ≫ eqToHom (hG N).symm)
      (_ : G.Additive),
      Nonempty (DerivedCategory.Q.obj A ⊗ (derivedPullback f).obj (DerivedCategory.Q.obj L) ≅
        DerivedCategory.Q.obj (CochainComplex.mapBifunctor A
          ((G.mapHomologicalComplex (.up ℤ)).obj L)
          (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))))) := by
  obtain ⟨G, hG, hGmap, hGadd, ⟨ep⟩⟩ := relativeTensorPullback_kFlat_counit f L hL
  have := hGadd
  obtain ⟨et⟩ := relativeTensorPullback_kFlat_tensor X A
    ((G.mapHomologicalComplex (.up ℤ)).obj L) hA
  exact ⟨G, hG, hGmap, hGadd,
    ⟨(tensorLeft (DerivedCategory.Q.obj A)).mapIso ep ≪≫ et⟩⟩

private theorem relativeTensorPullback_ordinary_homology
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hG : ∀ M, G.obj M = Modules.tensorPullbackObj f M)
    (hGmap : ∀ {M N} (a : M ⟶ N),
      G.map a = eqToHom (hG M) ≫ Modules.tensorPullbackMap f a ≫ eqToHom (hG N).symm)
    [G.Additive]
    (A : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (L : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ) (i : ℤ) :
    Nonempty
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj
          ((CochainComplex.mapBifunctor A
            ((G.mapHomologicalComplex (.up ℤ)).obj L)
            (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)))).homology i) ≅
        (SheafOfModules.toSheaf
          ((sheafCompose (Opens.grothendieckTopology X)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (TopCat.Sheaf.inverseImageRing f.base S.sheaf))).obj
          ((CochainComplex.mapBifunctor
            (((SheafOfModules.restrictScalars
              ((sheafCompose (Opens.grothendieckTopology X)
                (forget₂ CommRingCat.{u} RingCat.{u})).map
                  (Modules.tensorPullbackRingMap f))).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj A)
            (((TopCat.Sheaf.inverseImageModuleFunctor f.base S.sheaf).mapHomologicalComplex
               (ComplexShape.up ℤ)).obj L)
            (@curriedTensor _ _ (SheafOfModules.monoidalCategory
              (TopCat.Sheaf.inverseImageRing f.base S.sheaf)))).homology i)) := by
  classical
  -- The module and tensor instances share these sheafification hypotheses.
  have : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance
  have : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  have : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance
  have : HasSheafify (Opens.grothendieckTopology S) AddCommGrpCat.{u} := inferInstance
  have : (Opens.grothendieckTopology S).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let : Abelian C := inferInstance
  let R := TopCat.Sheaf.inverseImageRing f.base S.sheaf
  let B := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let : Abelian (SheafOfModules.{u} B) := inferInstance
  let V := SheafOfModules.toSheaf B
  let W := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
  have hV := CategoryTheory.moduleSheaves_colimits_forgetful.{u, u, u, u}
    B
  have : PreservesFiniteLimits V := hV.2.1
  have : PreservesFiniteColimits V := hV.2.2.1
  have hW := CategoryTheory.moduleSheaves_colimits_forgetful.{u, u, u, u}
    (moduleRings X.toRingedSpace)
  have : PreservesFiniteLimits W := hW.2.1
  have : PreservesFiniteColimits W := hW.2.2.1
  have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, u, u} C
  have : HasColimitsOfSize.{0, 0} (SheafOfModules.{u} B) :=
    hasColimitsOfSizeShrink.{0, 0, u, u} (SheafOfModules.{u} B)
  have (M N : CochainComplex C ℤ) :
      CochainComplex.HasMapBifunctor M N (curriedTensor C) := fun _ ↦ inferInstance
  have (M N : CochainComplex (SheafOfModules.{u} B) ℤ) :
      CochainComplex.HasMapBifunctor M N
        (@curriedTensor _ _ (SheafOfModules.monoidalCategory R)) := fun _ ↦ inferInstance
  obtain ⟨eb⟩ := relativeTensorPullback_complex_comparison f G hG hGmap A L
  let Z := CochainComplex.mapBifunctor A
    ((G.mapHomologicalComplex (.up ℤ)).obj L) (curriedTensor C)
  let U := SheafOfModules.restrictScalars
    ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).map (Modules.tensorPullbackRingMap f))
  let IL := ((TopCat.Sheaf.inverseImageModuleFunctor f.base S.sheaf).mapHomologicalComplex
     (.up ℤ)).obj L
  let := SheafOfModules.monoidalCategory R
  let Z' := CochainComplex.mapBifunctor
    ((U.mapHomologicalComplex (.up ℤ)).obj A) IL (curriedTensor (SheafOfModules.{u} B))
  exact relativeTensorPullback_model_homology W V Z Z' eb i

-- Derived and ordinary homology comparisons involve several nested functors.
/-- On K-flat representatives in both source module categories, the balanced tensor
identity computes the underlying homology of derived tensor with derived pullback.
This is only the representative calculation: no replacement of the restricted first
complex by an arbitrary K-flat resolution is asserted here.
Source: Stacks Project, Cohomology, Lemma 20.27.4 (Tag 08DE), proof.

Proof: the K-flat counit for derived pullback identifies Lf*(Q(L)) with Q(f*L).
The K-flat first-factor comparison then identifies Q(A) tensor Q(f*L) with
Q(Tot(A tensor f*L)). In each bidegree the balanced tensor isomorphism
A^p tensor over O_X (O_X tensor over f-inverse O_S f-inverse L^q)
is A^p restricted to f-inverse O_S tensor f-inverse L^q. Its naturality
commutes with both differentials; the same sign (-1)^p occurs on both sides.
Restriction of scalars preserves coproducts, so these summand identifications
induce an isomorphism of total complexes. Exact restriction of scalars commutes
with homology, and forgetting to abelian sheaves removes the scalar action.
Compose these identifications with the localization homology comparison.
The construction is valid for unbounded complexes and empty schemes; it does not
require the restriction of A to be K-flat.
(blueprint: lem-pc-relative-tensor-pullback-kflat-model) -/
theorem relativeTensorPullback_kFlat_model
    {X S : Scheme.{u}} (f : X ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (A : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hA : CochainComplex.IsKFlatTensor (R := X.sheaf) A)
    (L : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
    (hL : CochainComplex.IsKFlatTensor (R := S.sheaf) L) (i : ℤ) :
    Nonempty
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj
          ((DerivedCategory.homologyFunctor _ i).obj
            (DerivedCategory.Q.obj A ⊗ (derivedPullback f).obj
              (DerivedCategory.Q.obj L))) ≅
        (SheafOfModules.toSheaf
          ((sheafCompose (Opens.grothendieckTopology X)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (TopCat.Sheaf.inverseImageRing f.base S.sheaf))).obj
          ((CochainComplex.mapBifunctor
            (((SheafOfModules.restrictScalars
              ((sheafCompose (Opens.grothendieckTopology X)
                (forget₂ CommRingCat.{u} RingCat.{u})).map
                  (Modules.tensorPullbackRingMap f))).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj A)
            (((TopCat.Sheaf.inverseImageModuleFunctor f.base S.sheaf).mapHomologicalComplex
               (ComplexShape.up ℤ)).obj L)
            (@curriedTensor _ _ (SheafOfModules.monoidalCategory
              (TopCat.Sheaf.inverseImageRing f.base S.sheaf)))).homology i)) := by
  obtain ⟨G, hG, hGmap, hGadd, ⟨ed⟩⟩ := relativeTensorPullback_kFlat_derived f A hA L hL
  have := hGadd
  obtain ⟨eh⟩ := relativeTensorPullback_ordinary_homology f G hG hGmap A L i
  exact ⟨(SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).mapIso
    ((DerivedCategory.homologyFunctor _ i).mapIso ed ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app _) ≪≫ eh⟩

end AlgebraicGeometry.Scheme

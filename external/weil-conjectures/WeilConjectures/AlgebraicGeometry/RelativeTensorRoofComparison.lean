/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictPerfectRelativeTensorComplex
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.DerivedTensorOpenRestrictionUniverses
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison
import WeilConjectures.AlgebraicGeometry.LocalizedOpenTensorEquivalence
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Derived comparison for the relative tensor complexes

Source: Stacks Project, Tags 0DJQ and 08CI, local tensor calculation.
(blueprint: lem-pc-strict-perfect-relative-tensor-roof-comparison).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] CategoryTheory.module_overFunctor_preservesZero
  Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace AlgebraicGeometry.Scheme

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

@[instance_reducible]
private noncomputable def roofComparison_localizedTensor (X : Scheme.{u}) (U : X.Opens) :
    MonoidalCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
  SheafOfModules.monoidalCategory (X.sheaf.over U)

attribute [local instance] roofComparison_localizedTensor


private local instance roofComparison_globalTensorZero (X : Scheme.{u}) :
    (@curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _
            (SheafOfModules.monoidalCategory X.sheaf)).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf

private local instance roofComparison_globalTensorObjZero (X : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    ((@curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _
            (SheafOfModules.monoidalCategory X.sheaf)).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

private local instance roofComparison_localTensorZero (X : Scheme.{u}) (U : X.Opens) :
    (@curriedTensor (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) _
          (SheafOfModules.monoidalCategory (X.sheaf.over U))).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor (X.sheaf.over U)

private local instance roofComparison_localTensorObjZero (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :
    ((@curriedTensor (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) _
          (SheafOfModules.monoidalCategory (X.sheaf.over U))).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj (X.sheaf.over U) M

private local instance roofComparison_globalColimits (X : Scheme.{u}) :
    CategoryTheory.Limits.HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := inferInstance

private local instance roofComparison_localColimits (X : Scheme.{u}) (U : X.Opens) :
    CategoryTheory.Limits.HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) := inferInstance

private local instance roofComparison_globalTotal (X : Scheme.{u})
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    HomologicalComplex.HasMapBifunctor P N
      (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)) (.up ℤ) :=
  fun _ ↦ inferInstance

private local instance roofComparison_localTotal (X : Scheme.{u}) (U : X.Opens)
    (A B : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ) :
    HomologicalComplex.HasMapBifunctor A B
      (@curriedTensor _ _ (SheafOfModules.monoidalCategory (X.sheaf.over U))) (.up ℤ) :=
  fun _ ↦ inferInstance

private theorem equivalence_totalTensor_iso (X : Scheme.{u}) (U : X.Opens)
    (F : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ≌
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
    (e : ∀ M N, F.functor.obj (M ⊗ N) ≅ F.functor.obj M ⊗ F.functor.obj N)
    (he : ∀ (M M' N N' : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (f : M ⟶ M') (g : N ⟶ N'),
      F.functor.map (f ⊗ₘ g) ≫ (e M' N').hom =
        (e M N).hom ≫ (F.functor.map f ⊗ₘ F.functor.map g))
    (A B : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ) :
    let E := F.functor
    Nonempty (((E.mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mapBifunctor A B (curriedTensor _))) ≅
      CochainComplex.mapBifunctor ((E.mapHomologicalComplex (.up ℤ)).obj A)
        ((E.mapHomologicalComplex (.up ℤ)).obj B) (curriedTensor _)) := by
  let E := F.functor
  let K := (((curriedTensor
    (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))).mapBifunctorHomologicalComplex
      (.up ℤ) (.up ℤ)).obj A).obj B
  have : E.PreservesTotalComplex K (.up ℤ) := fun _ ↦ inferInstance
  let e₁ := (HomologicalComplex₂.mapTotalIso E K (.up ℤ)).symm
  let e₂ :
      (((E.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj K) ≅
        (((curriedTensor (SheafOfModules.{u}
          (moduleRings U.toScheme.toRingedSpace))).mapBifunctorHomologicalComplex
            (.up ℤ) (.up ℤ)).obj ((E.mapHomologicalComplex (.up ℤ)).obj A)).obj
              ((E.mapHomologicalComplex (.up ℤ)).obj B) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents (fun q ↦ e (A.X p) (B.X q))
        (by
          intro q q' hq
          change (e (A.X p) (B.X q)).hom ≫ E.obj (A.X p) ◁ E.map (B.d q q') =
            E.map (A.X p ◁ B.d q q') ≫ (e (A.X p) (B.X q')).hom
          simpa [E] using (he (A.X p) (A.X p) (B.X q) (B.X q') (𝟙 _) (B.d q q')).symm))
      (by
        intro p p' hp
        apply HomologicalComplex.Hom.ext
        funext q
        change (e (A.X p) (B.X q)).hom ≫ E.map (A.d p p') ▷ E.obj (B.X q) =
          E.map (A.d p p' ▷ B.X q) ≫ (e (A.X p') (B.X q)).hom
        simpa [E] using (he (A.X p) (A.X p') (B.X q) (B.X q) (A.d p p') (𝟙 _)).symm)
  exact ⟨e₁ ≪≫ HomologicalComplex₂.total.mapIso e₂ (.up ℤ)⟩


private theorem flat_retract (Y : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (I : Type u)
    (i : M ⟶ SheafOfModules.free (R := moduleRings Y.toRingedSpace) I)
    (r : SheafOfModules.free (R := moduleRings Y.toRingedSpace) I ⟶ M)
    (h : i ≫ r = 𝟙 M) : SheafOfModules.IsFlat M := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  let := SheafOfModules.symmetricCategory Y.sheaf
  obtain ⟨⟨mp⟩, ⟨mc⟩, _⟩ := SheafOfModules.tensorClosed Y.sheaf
  let := mp
  let := mc
  have := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  have hf : ObjectProperty.flat
      (SheafOfModules.free (R := moduleRings Y.toRingedSpace) I) :=
    ObjectProperty.flat_coproduct _ (fun _ ↦ ObjectProperty.prop_unit _)
  exact (ObjectProperty.flat_of_retract ⟨i, r, h⟩ hf).2


-- Tensor comparison transports through complex and derived module equivalences.
/-- The open restriction of the derived tensor is computed by the ordinary total tensor.
Source: Stacks Project, Tags 0DJQ and 06YH (local strict-perfect tensor calculation).
(blueprint: lem-pc-strict-perfect-open-tensor-comparison).

The finite-free retract terms of a strictly perfect complex are flat and bounded, hence
K-flat. Exact open restriction and the K-flat derived tensor comparison identify the
restricted derived tensor with the ordinary total tensor. The compatibility with the
localized open site is transported through the canonical module equivalence.
-/
private theorem strictPerfect_openTensor_comparison
    {X : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X)
    (G K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (eK : DerivedCategory.Q.obj K ≅ E ⊗ DerivedCategory.Q.obj G)
    (U : X.Opens)
    (L : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hL : IsStrictlyPerfect X U L)
    (eL : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj L) :
    Nonempty
      (DerivedCategory.Q.obj
        (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≅
        DerivedCategory.Q.obj
          (CochainComplex.mapBifunctor L
            (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj G)
            (@curriedTensor _ _
              (SheafOfModules.monoidalCategory (X.sheaf.over U))))) := by
  classical
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
  let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let A := Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
    (Modules.overEquiv U)
  let B := Equivalence.inverse
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
    (Modules.overEquiv U)
  let AC := A.mapHomologicalComplex (.up ℤ)
  let RC := R.mapHomologicalComplex (.up ℤ)
  let P := AC.obj L
  let N := AC.obj (RC.obj G)
  have hPbounded : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (P.X n) := by
    obtain ⟨a, b, hb⟩ := hL.1
    exact ⟨b, fun n hn ↦ A.map_isZero (hb n (Or.inr hn))⟩
  have hPflat : ∀ n : ℤ, SheafOfModules.IsFlat (P.X n) := by
    intro n
    obtain ⟨m, i, r, hir⟩ := hL.2 n
    let ei : A.obj (SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m))) ≅
        SheafOfModules.free (R := moduleRings U.toScheme.toRingedSpace)
          (ULift.{u} (Fin m)) :=
      (asIso (sigmaComparison A (fun _ : ULift.{u} (Fin m) ↦
        SheafOfModules.unit ((moduleRings X.toRingedSpace).over U)))).symm ≪≫
      Sigma.mapIso (fun _ ↦ U.sheafOfModulesEquivOverUnit (moduleRings X.toRingedSpace))
    apply flat_retract U.toScheme (P.X n) (ULift.{u} (Fin m))
      (A.map i ≫ ei.hom) (ei.inv ≫ A.map r)
    change (A.map i ≫ ei.hom) ≫ ei.inv ≫ A.map r = 𝟙 (A.obj (L.X n))
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hir]
    exact A.map_id _
  have hP : CochainComplex.IsKFlatTensor (R := U.toScheme.sheaf) P :=
    CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
      U.toScheme.toRingedSpace P hPbounded hPflat
  obtain ⟨t⟩ := derivedTensor_openRestriction_iso_universes X U E (DerivedCategory.Q.obj G)
  let dL : (R ⋙ A).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj P :=
    (Functor.mapDerivedCategoryCompIso R A).symm.app E ≪≫
      A.mapDerivedCategory.mapIso eL ≪≫ A.mapDerivedCategoryFactors.app L
  let dG : (R ⋙ A).mapDerivedCategory.obj (DerivedCategory.Q.obj G) ≅
      DerivedCategory.Q.obj N := (R ⋙ A).mapDerivedCategoryFactors.app G
  obtain ⟨c⟩ := kFlat_derivedTensor_comparison_natIso U.toScheme
    ((Functor.const (Discrete PUnit.{1})).obj P)
    ((Functor.const (Discrete PUnit.{1})).obj N) (fun _ ↦ hP)
  let T := CochainComplex.mapBifunctor L (RC.obj G)
    (@curriedTensor _ _ (SheafOfModules.monoidalCategory (X.sheaf.over U)))
  obtain ⟨e, he⟩ := exists_localizedOpen_tensor_equivalence X U
  obtain ⟨z⟩ := equivalence_totalTensor_iso X U (Modules.overEquiv U) e he L (RC.obj G)
  let d : DerivedCategory.Q.obj (AC.obj (RC.obj K)) ≅
      DerivedCategory.Q.obj (AC.obj T) :=
    ((R ⋙ A).mapDerivedCategoryFactors.app K).symm ≪≫
      (R ⋙ A).mapDerivedCategory.mapIso eK ≪≫ t ≪≫ tensorIso dL dG ≪≫
      (c.app ⟨PUnit.unit⟩).app ⟨PUnit.unit⟩ ≪≫ DerivedCategory.Q.mapIso z.symm
  let eqv : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ≌
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) := Modules.overEquiv U
  let eC := eqv.mapHomologicalComplex (.up ℤ)
  let back (V : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ) :
      B.mapDerivedCategory.obj (DerivedCategory.Q.obj (AC.obj V)) ≅
        DerivedCategory.Q.obj V :=
    B.mapDerivedCategoryFactors.app (AC.obj V) ≪≫
      DerivedCategory.Q.mapIso (eC.unitIso.app V).symm
  exact ⟨(back (RC.obj K)).symm ≪≫ B.mapDerivedCategory.mapIso d ≪≫ back T⟩


private theorem restrictScalars_exact
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {R A : Sheaf J RingCat.{u}} (α : R ⟶ A) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{u} α) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{u} α) := by
  let F := SheafOfModules.restrictScalars.{u} α
  have : PreservesFiniteLimits (F ⋙ SheafOfModules.toSheaf.{u} R) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} A))
  have : PreservesFiniteColimits (F ⋙ SheafOfModules.toSheaf.{u} R) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} A))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F (SheafOfModules.toSheaf.{u} R),
    preservesFiniteColimits_of_reflects_of_preserves F (SheafOfModules.toSheaf.{u} R)⟩

-- Scalar restriction and localization comparisons unfold nested ring-sheaf restrictions.
/-- The two fixed base-ring complexes are isomorphic after localization.
Source: Stacks Project, Tags 0DJQ and 06YH (local K-flat tensor computation).

Proof: finite-free retracts are flat, so the bounded strictly perfect L is K-flat.
Apply exact monoidal open restriction to eK, and identify the first factor with L
using eL. The K-flat comparison identifies this tensor with the ordinary total
of L and the restriction of G. Restriction of scalars is exact, so it preserves
quasi-isomorphisms and induces a functor on derived categories. Apply that functor
to the preceding isomorphism. Open restriction commutes with scalar restriction
sectionwise; its comparison with the localization functor identifies the first
object with the displayed scalar-restricted K and the second with the explicit
strictPerfectRelativeTensorComplex. This works also for the empty open. The
standard localization of the base-ring category is used, since the hypotheses
only choose localizations for structure-ring modules. This statement concerns
only the derived tensor computation; it does not assert or choose a roof.
(blueprint: lem-pc-strict-perfect-relative-tensor-roof-comparison). -/
theorem strictPerfect_relativeTensor_roof_comparison
    {X S : Scheme.{u}} (f : X ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X)
    (G K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (eK : DerivedCategory.Q.obj K ≅ E ⊗ DerivedCategory.Q.obj G)
    (U : X.Opens)
    (L : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hL : IsStrictlyPerfect X U L)
    (eL : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj L) :
    let R := TopCat.Sheaf.inverseImageRing f.base S.sheaf
    let A := (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R
    letI : HasDerivedCategory.{u + 1} (SheafOfModules.{u} (A.over U)) :=
      HasDerivedCategory.standard _
    Nonempty
      (DerivedCategory.Q.obj
        (((SheafOfModules.overFunctor.{u} A U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          (((SheafOfModules.restrictScalars
            ((sheafCompose (Opens.grothendieckTopology X)
              (forget₂ CommRingCat.{u} RingCat.{u})).map
                (Modules.tensorPullbackRingMap f))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) ≅
        DerivedCategory.Q.obj (strictPerfectRelativeTensorComplex f U L G)) := by
  classical
  dsimp only
  let R := TopCat.Sheaf.inverseImageRing f.base S.sheaf
  let A := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let α := ((Opens.grothendieckTopology X).overPullback CommRingCat.{u} U).map
    (Modules.tensorPullbackRingMap f)
  let B := (sheafCompose ((Opens.grothendieckTopology X).over U)
    (forget₂ CommRingCat.{u} RingCat.{u})).map α
  let F : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ⥤
      SheafOfModules.{u} (A.over U) := SheafOfModules.restrictScalars B
  let := HasDerivedCategory.standard (SheafOfModules.{u} (A.over U))
  obtain ⟨e⟩ := strictPerfect_openTensor_comparison E G K eK U L hL eL
  let T : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ :=
    CochainComplex.mapBifunctor L
    (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapHomologicalComplex
      (.up ℤ)).obj G)
    (@curriedTensor _ _ (SheafOfModules.monoidalCategory (X.sheaf.over U)))
  have := (restrictScalars_exact B).1
  have := (restrictScalars_exact B).2
  let c := (F.mapDerivedCategoryFactors.{w, u + 1}.app _).symm ≪≫
    F.mapDerivedCategory.{w, u + 1}.mapIso e ≪≫
      F.mapDerivedCategoryFactors.{w, u + 1}.app T
  exact ⟨c⟩

end AlgebraicGeometry.Scheme

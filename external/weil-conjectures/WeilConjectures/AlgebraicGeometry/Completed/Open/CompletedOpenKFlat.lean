/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedExtensionZeroComparison
import WeilConjectures.Algebra.Homology.Ringed.RingedOpenFlatResolution
import WeilConjectures.AlgebraicGeometry.Ringed.RingedOpenStrictReduction
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

/-! # K-flatness under completed-coefficient open extension

Source: Stacks Tags 00XZ, 0E8I and 06YN.
(blueprint: lem-cbc-completed-open-kflat).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [local irreducible] SheafOfModules.monoidalCategory HasDerivedCategory.standard
  Functor.leftAdjoint limit

private theorem algebraicInverseImage_kFlat
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf K CommRingCat.{u + 1}}
    (L : Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1))) [L.IsEquivalence]
    (I : SheafOfModules.AlgebraicInverseImage L R S) [I.modules.Additive]
    (P : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hf : ∀ q : ℤ, exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) (P.X q))) :
    CochainComplex.IsKFlatIndependentCoefficients (R := S)
      ((I.modules.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ q : ℤ, exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory S)
          (((I.modules.mapHomologicalComplex (.up ℤ)).obj P).X q)) := by
  let := HasDerivedCategory.standard (SheafOfModules.{u + 1}
    ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
  obtain ⟨E⟩ := SheafOfModules.nonempty_derivedChangeOfRingsCochainModel (𝟙 S)
  let F := I.modules ⋙ E.E
  obtain ⟨θ, _, _, hθ⟩ :=
    SheafOfModules.exists_scalarExtensionRingIso.{u + 1, u, u + 1, u + 1} (Iso.refl S)
  let ι : SheafOfModules.restrictScalars
      ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (𝟙 S)) ≅
      𝟭 _ := NatIso.ofComponents
    (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦
        { hom := ModuleCat.ofHom
            { toFun := fun x ↦ x
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun _ _ ↦ rfl }
          inv := ModuleCat.ofHom
            { toFun := fun x ↦ x
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun _ _ ↦ rfl }
          hom_inv_id := by ext x; rfl
          inv_hom_id := by ext x; rfl }) (by intros; rfl))) (by intros; rfl)
  let e₁ : E.E ≅ SheafOfModules.restrictScalars
      ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (𝟙 S)) :=
    NatIso.ofComponents (fun M ↦ eqToIso (E.obj_eq M) ≪≫ θ M) (by
      intro M N f
      dsimp only [Iso.trans_hom, eqToIso.hom]
      rw [E.map_eq]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      have h := congrArg (fun k ↦ eqToHom (E.obj_eq M) ≫ k) (hθ M N f)
      with_unfolding_all exact h)
  let e₀ := e₁ ≪≫ ι
  let e := NatIso.mapHomologicalComplex (Functor.isoWhiskerLeft I.modules e₀) (.up ℤ)
  obtain ⟨hk, ht⟩ :=
    SheafOfModules.isKFlat_ringedToposPullback.{u + 1, u, u + 1, u, u + 1} L
    (Functor.asEquivalence L).inverse (Functor.asEquivalence L).toAdjunction I (𝟙 S) F
    (fun M ↦ E.obj_eq (I.modules.obj M)) (fun f ↦ E.map_eq (I.modules.map f)) P hP
    (fun q ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (P.X q)).symm (hf q))
  refine ⟨SheafOfModules.kFlat_iso_independent S (e.app P) hk, ?_⟩
  intro q
  have h := SheafOfModules.flatOnSite_of_iso S
    ((Functor.isoWhiskerLeft I.modules e₀).app (P.X q)) (ht q)
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso S _ ) h

private abbrev reindexModule
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {K : GrothendieckTopology C} {J : GrothendieckTopology D}
    (f : C ⥤ D) [f.IsContinuous K J]
    {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf K CommRingCat.{u + 1}}
    (c : S ≅ (f.sheafPushforwardContinuous CommRingCat.{u + 1} K J).obj R) :
    SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⥤
      SheafOfModules.{u + 1}
        ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) :=
  SheafOfModules.pushforward.{u + 1} (F := f) (J := K) (K := J)
    (R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
    (S := (sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
    ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)

private theorem reindex_kFlat
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
    {K : GrothendieckTopology C} {J : GrothendieckTopology D}
    (f : C ⥤ D) [f.IsContinuous K J]
    [(f.sheafPushforwardContinuous (Type (u + 1)) K J).IsEquivalence]
    {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf K CommRingCat.{u + 1}}
    (c : S ≅ (f.sheafPushforwardContinuous CommRingCat.{u + 1} K J).obj R)
    [(reindexModule f c).Additive]
    (P : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hf : ∀ q : ℤ, exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) (P.X q))) :
    CochainComplex.IsKFlatIndependentCoefficients (R := S)
      ((Functor.mapHomologicalComplex
        (reindexModule f c)
            (.up ℤ)).obj P) ∧
      ∀ q : ℤ, exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory S)
          (((Functor.mapHomologicalComplex
            (reindexModule f c)
                (.up ℤ)).obj P).X q)) := by
  let L := f.sheafPushforwardContinuous (Type (u + 1)) K J
  let I : SheafOfModules.AlgebraicInverseImage L R S :=
    { ringUnderlying := (sheafCompose K (CategoryTheory.forget CommRingCat)).mapIso c.symm
      ringAdd := by
        intro T a b t h V x
        change c.inv.hom.app V (t.hom.app (f.op.obj V) x) =
          c.inv.hom.app V (a.hom.app (f.op.obj V) x) +
            c.inv.hom.app V (b.hom.app (f.op.obj V) x)
        simp only [id_eq] at h
        rw [h (f.op.obj V) x, map_add]
      ringMul := by
        intro T a b t h V x
        change c.inv.hom.app V (t.hom.app (f.op.obj V) x) =
          c.inv.hom.app V (a.hom.app (f.op.obj V) x) *
            c.inv.hom.app V (b.hom.app (f.op.obj V) x)
        simp only [id_eq] at h
        rw [h (f.op.obj V) x, map_mul]
      ringZero := by
        intro T a h V x
        change c.inv.hom.app V (a.hom.app (f.op.obj V) x) = _
        simp only [id_eq] at h
        rw [h (f.op.obj V) x, map_zero]
      ringOne := by
        intro T a h V x
        change c.inv.hom.app V (a.hom.app (f.op.obj V) x) = _
        simp only [id_eq] at h
        rw [h (f.op.obj V) x, map_one]
      modules := reindexModule f c
      moduleUnderlying := Iso.refl _
      moduleAdd := by
        intro M T a b t h V x
        exact h (f.op.obj V) x
      moduleZero := by
        intro M T a h V x
        exact h (f.op.obj V) x
      moduleSMul := by
        intro M T a b t h V x
        change t.hom.app (f.op.obj V) x =
          (show R.obj.obj (f.op.obj V) from
            c.hom.hom.app V (c.inv.hom.app V (a.hom.app (f.op.obj V) x))) •
            (show M.val.obj (f.op.obj V) from b.hom.app (f.op.obj V) x)
        have hc := ConcreteCategory.congr_hom
          (congrArg (fun k ↦ k.hom.app V) c.inv_hom_id) (a.hom.app (f.op.obj V) x)
        change c.hom.hom.app V (c.inv.hom.app V _) = _ at hc
        rw [hc]
        exact h (f.op.obj V) x }
  exact algebraicInverseImage_kFlat L I P hP hf

attribute [local irreducible] SheafOfModules.pushforward
  SheafOfModules.extensionByZeroPresheaf PresheafOfModules.sheafification

private theorem cbcModuleToSlice_kFlat
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (X : Scheme.{u}) (W : X.ProEt) [(cbcModuleToSlice d X W).Additive]
    (P : CochainComplex (pbcModules W.left (pbcAdicCompletion W.left d)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := pbcAdicCompletion W.left d) P)
    (hf : ∀ q : ℤ, exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _
        (SheafOfModules.monoidalCategory (pbcAdicCompletion W.left d)) (P.X q))) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := (pbcAdicCompletion X d).over W)
      (((cbcModuleToSlice d X W).mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ q : ℤ, exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _
          (SheafOfModules.monoidalCategory ((pbcAdicCompletion X d).over W))
          ((((cbcModuleToSlice d X W).mapHomologicalComplex (.up ℤ)).obj P).X q)) := by
  let f := cbcSliceFunctor X W
  let K := (ProEt.topology X).over W
  let J := ProEt.topology W.left
  let R := pbcAdicCompletion W.left d
  let S := (pbcAdicCompletion X d).over W
  have : (ProEt.sliceEquiv X W).inverse.IsDenseSubsite J K := ProEt.sliceDense X W
  have : f.IsDenseSubsite K J :=
    inferInstanceAs ((ProEt.sliceEquiv X W).functor.IsDenseSubsite K J)
  let L := f.sheafPushforwardContinuous (Type (u + 1)) K J
  have : L.IsEquivalence := inferInstance
  let c : S ≅ (f.sheafPushforwardContinuous CommRingCat.{u + 1} K J).obj R :=
    asIso (cbcCompletedSliceMap d X W)
  have : (reindexModule f c).Additive :=
    ⟨by intros; with_unfolding_all rfl⟩
  exact reindex_kFlat f c P hP hf

/-- Completed-coefficient open extension preserves K-flat flat-term representatives.
Source: Stacks Tags 00XZ, 0E8I and 06YN
(blueprint: lem-cbc-completed-open-kflat).

Proof: the projection-normalized completed slice map is an isomorphism. The
concrete equivalence of the open pro-etale site with the ambient slice, with
this ring identification, preserves tensor products, exact sequences and direct
sums. It therefore takes a K-flat flat-term complex to such a complex over the
restricted ambient ring. Apply ringedOpen_preserves_flat_resolution: its total
projection formula identifies tensor against the extension with extension of
tensor against exact restriction. Restriction preserves acyclicity, K-flatness
kills this tensor, and exact extension preserves the resulting acyclicity.
The same formula on short exact sequences preserves flatness of each term. -/
theorem cbcOpenShriek_kFlat_of_flatTerms
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {U X : Scheme.{u}} (j : U ⟶ X) (hj : IsOpenImmersion j)
    (P : CochainComplex (pbcModules U (pbcAdicCompletion U d)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion U d) P)
    (hflat : ∀ q : ℤ, exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _
        (SheafOfModules.monoidalCategory (pbcAdicCompletion U d)) (P.X q))) :
    CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion X d)
      (((cbcOpenShriek d j hj).mapHomologicalComplex (.up ℤ)).obj P) := by
  let W := cbcOpenObject j hj
  have : (cbcModuleToSlice d X W).Additive := by
    exact ⟨by intros; with_unfolding_all rfl⟩
  obtain ⟨hk, _⟩ := cbcModuleToSlice_kFlat d X W P hP hflat
  change CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion X d)
    ((SheafOfModules.ringedOpenExtensionOnComplexes.{u + 1, u, u + 1}
      (pbcAdicCompletion X d) W).obj
        (((cbcModuleToSlice d X W).mapHomologicalComplex (.up ℤ)).obj P))
  exact (SheafOfModules.ringedOpen_preserves_flat_resolution.{u + 1, u, u + 1}
    (pbcAdicCompletion X d) W).1
      (((cbcModuleToSlice d X W).mapHomologicalComplex (.up ℤ)).obj P) hk

end AlgebraicGeometry.Scheme

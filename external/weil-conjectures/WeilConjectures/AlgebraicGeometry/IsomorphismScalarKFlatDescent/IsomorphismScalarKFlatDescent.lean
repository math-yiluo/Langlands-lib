/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Localization
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Quotient
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.Algebra.Homology.Localization

/-! # Descent of a supplied scalar chain comparison along a scheme isomorphism

The geometric functors are the existing ringed inverse images. Scalar extension is
presented by its existing universal cochain model, retaining its canonical counit.
The input comparison is supplied only on flat-term K-flat complexes. The conclusion
fixes its descent on every resolution and includes the two- and three-resolution laws.

## References

* Tag 04VG
* Stacks 0G7D
* Stacks 03D3, 0G7E
* Stacks 06YT
* Stacks 06YU
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.IsomorphismScalarKFlatDescent

/-- The full-subcategory predicate in the statement: K-flat, with every term flat. -/
def good {W : Scheme.{u}} (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) :
    ObjectProperty (CochainComplex (proEtaleRingModules W R) ℤ) :=
  fun P ↦ CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1} (R := R) P ∧
    ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (R := R) (P.X n)

set_option backward.isDefEq.respectTransparency.types false in
private theorem descend_good
    {M : Type*} [Category M] [Abelian M] [HasDerivedCategory M]
    {D : Type*} [Category D] (p : ObjectProperty (CochainComplex M ℤ))
    (hres : ∀ K, ∃ (P : CochainComplex M ℤ) (s : P ⟶ K), QuasiIso s ∧ p P)
    (F G : DerivedCategory M ⥤ D)
    (t : p.ι ⋙ DerivedCategory.Q ⋙ F ≅ p.ι ⋙ DerivedCategory.Q ⋙ G) :
    ∃! β : F ≅ G, ∀ P : p.FullSubcategory,
      β.hom.app (DerivedCategory.Q.obj P.obj) = t.hom.app P := by
  classical
  let H := HomotopyCategory.quotient M (.up ℤ)
  let W := HomotopyCategory.quasiIso M (.up ℤ)
  have hr : ∀ X, ∃ (Y : HomotopyCategory M (.up ℤ)) (s : Y ⟶ X), p Y.as ∧ W s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨P, s, hs, hP⟩ := hres K
    exact ⟨H.obj P, H.map s, hP,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  let α (X : HomotopyCategory M (.up ℤ)) (hX : p X.as) := t.hom.app ⟨X.as, hX⟩
  have hinv : W.IsInvertedBy (DerivedCategory.Qh ⋙ F) := by
    intro X Y f hf
    have := Localization.inverts DerivedCategory.Qh W f hf
    change IsIso (F.map (DerivedCategory.Qh.map f))
    infer_instance
  have hn : ∀ X Y (hX : p X.as) (hY : p Y.as) (s : X ⟶ Y),
      (DerivedCategory.Qh ⋙ F).map s ≫ α Y hY =
        α X hX ≫ (DerivedCategory.Qh ⋙ G).map s := by
    intro X Y hX hY s
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨Q, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    obtain ⟨f, rfl⟩ := H.map_surjective s
    exact t.hom.naturality (ObjectProperty.homMk f : (⟨P, hX⟩ : p.FullSubcategory) ⟶ ⟨Q, hY⟩)
  obtain ⟨τ, hτ⟩ := exists_natTrans_from_resolvingClass W
    (fun X ↦ p X.as) hr (DerivedCategory.Qh ⋙ F) (DerivedCategory.Qh ⋙ G) hinv α hn
  let FF := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Qh W D
  let β := FF.preimage τ
  have hβ : Functor.whiskerLeft DerivedCategory.Qh β = τ := FF.map_preimage τ
  have he (P : p.FullSubcategory) : β.app (DerivedCategory.Q.obj P.obj) = t.hom.app P :=
    (congr_app hβ (H.obj P.obj)).trans (hτ (H.obj P.obj) P.property)
  have hk (K : CochainComplex M ℤ) : IsIso (β.app (DerivedCategory.Q.obj K)) := by
    obtain ⟨P, s, hs, hP⟩ := hres K
    have := hs
    have hi : IsIso (β.app (DerivedCategory.Q.obj P)) := by
      rw [he ⟨P, hP⟩]
      infer_instance
    have hc : IsIso (F.map (DerivedCategory.Q.map s) ≫ β.app (DerivedCategory.Q.obj K)) := by
      rw [β.naturality]
      infer_instance
    exact (isIso_comp_left_iff _ _).1 hc
  have hi (X : DerivedCategory M) : IsIso (β.app X) := by
    let e := DerivedCategory.Q.objObjPreimageIso X
    have := hk (DerivedCategory.Q.objPreimage X)
    have hc : IsIso (F.map e.hom ≫ β.app X) := by
      rw [β.naturality]
      infer_instance
    exact (isIso_comp_left_iff _ _).1 hc
  have : IsIso β := NatIso.isIso_of_isIso_app β
  refine ⟨asIso β, he, ?_⟩
  intro β' he'
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso M (.up ℤ))
  intro K
  obtain ⟨P, s, hs, hP⟩ := hres K
  have := hs
  change β'.hom.app _ = β.app _
  apply (cancel_epi (F.map (DerivedCategory.Q.map s))).1
  rw [β'.hom.naturality, β.naturality, he' ⟨P, hP⟩, he ⟨P, hP⟩]

private theorem conjugate_cancel {C : Type*} [Category C] {X Y Z T : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (d : T ≅ Z) :
    (a ≫ b ≫ d.inv) ≫ d.hom = a ≫ b := by
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private def composeSquare
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (Q₀ : C₀ ⥤ D₀) (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂)
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (F' : D₀ ⥤ D₁) (G' : D₁ ⥤ D₂)
    (a : Q₀ ⋙ F' ⟶ F ⋙ Q₁) (b : Q₁ ⋙ G' ⟶ G ⋙ Q₂) :
    Q₀ ⋙ (F' ⋙ G') ⟶ (F ⋙ G) ⋙ Q₂ where
  app P := G'.map (a.app P) ≫ b.app (F.obj P)
  naturality P Q f := by
    dsimp only [Functor.comp_map, Functor.comp_obj]
    have ha := a.naturality f
    have hb := b.naturality (F.map f)
    dsimp only [Functor.comp_map] at ha hb
    rw [← Category.assoc, ← G'.map_comp, ha,
      G'.map_comp, Category.assoc, hb]
    exact (Category.assoc _ _ _).symm

private theorem normalized_map
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Q : C ⥤ D) (F G : D ⥤ E) (U V : C ⥤ E)
    (a : Q ⋙ F ⟶ U) (d : Q ⋙ G ⟶ V) (β : F ≅ G)
    {P K : C} (s : P ⟶ K) [IsIso (Q.map s)] (b : U.obj P ⟶ V.obj P)
    (h : β.hom.app (Q.obj P) ≫ d.app P = a.app P ≫ b) :
    β.hom.app (Q.obj K) ≫ (G.map (inv (Q.map s)) ≫ d.app P) =
      (F.map (inv (Q.map s)) ≫ a.app P) ≫ b := by
  rw [← Category.assoc, ← β.hom.naturality]
  simp only [Category.assoc]
  rw [h]

private theorem inv_map_id {C D : Type*} [Category C] [Category D]
    (Q : C ⥤ D) (P : C) : inv (Q.map (𝟙 P)) = 𝟙 (Q.obj P) := by
  apply IsIso.inv_eq_of_hom_inv_id
  simp only [Q.map_id, Category.comp_id]

private theorem normalized_id
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Q : C ⥤ D) (F G : D ⥤ E) (U V : C ⥤ E)
    (a : Q ⋙ F ⟶ U) (d : Q ⋙ G ⟶ V) (β : F ≅ G)
    (P : C) (b : U.obj P ⟶ V.obj P)
    (h : β.hom.app (Q.obj P) ≫ (G.map (inv (Q.map (𝟙 P))) ≫ d.app P) =
      (F.map (inv (Q.map (𝟙 P))) ≫ a.app P) ≫ b) :
    β.hom.app (Q.obj P) ≫ d.app P = a.app P ≫ b := by
  rw [inv_map_id, F.map_id, G.map_id, Category.id_comp, Category.id_comp] at h
  exact h

set_option backward.isDefEq.respectTransparency.types false in
private theorem descend_normalized
    {M : Type*} [Category M] [Abelian M] [HasDerivedCategory M]
    {D : Type*} [Category D] (p : ObjectProperty (CochainComplex M ℤ))
    (hres : ∀ K, ∃ (P : CochainComplex M ℤ) (s : P ⟶ K), QuasiIso s ∧ p P)
    (F G : DerivedCategory M ⥤ D) (U V : CochainComplex M ℤ ⥤ D)
    (a : DerivedCategory.Q ⋙ F ⟶ U) (d : DerivedCategory.Q ⋙ G ⟶ V)
    (ha : ∀ P : p.FullSubcategory, IsIso (a.app P.obj))
    (hd : ∀ P : p.FullSubcategory, IsIso (d.app P.obj))
    (b : p.ι ⋙ U ≅ p.ι ⋙ V) :
    ∃! β : F ≅ G, ∀ (P K : CochainComplex M ℤ) (s : P ⟶ K) (_ : QuasiIso s)
      (hP : p P),
      β.hom.app (DerivedCategory.Q.obj K) ≫
          (G.map (inv (DerivedCategory.Q.map s)) ≫ d.app P) =
        (F.map (inv (DerivedCategory.Q.map s)) ≫ a.app P) ≫ b.hom.app ⟨P, hP⟩ := by
  classical
  have (P : p.FullSubcategory) : IsIso ((Functor.whiskerLeft p.ι a).app P) := ha P
  have (P : p.FullSubcategory) : IsIso ((Functor.whiskerLeft p.ι d).app P) := hd P
  have : IsIso (Functor.whiskerLeft p.ι a) := NatIso.isIso_of_isIso_app _
  have : IsIso (Functor.whiskerLeft p.ι d) := NatIso.isIso_of_isIso_app _
  let ai := asIso (Functor.whiskerLeft p.ι a)
  let di := asIso (Functor.whiskerLeft p.ι d)
  let t : p.ι ⋙ DerivedCategory.Q ⋙ F ≅ p.ι ⋙ DerivedCategory.Q ⋙ G :=
    ai ≪≫ b ≪≫ di.symm
  obtain ⟨β, hβ, huniq⟩ := descend_good p hres F G t
  have hbase (P : p.FullSubcategory) :
      β.hom.app (DerivedCategory.Q.obj P.obj) ≫ d.app P.obj =
        a.app P.obj ≫ b.hom.app P := by
    rw [hβ P]
    change (ai.hom.app P ≫ b.hom.app P ≫ di.inv.app P) ≫ di.hom.app P =
      ai.hom.app P ≫ b.hom.app P
    exact conjugate_cancel _ _ (di.app P)
  refine ⟨β, ?_, ?_⟩
  · intro P K s hs hP
    exact normalized_map DerivedCategory.Q F G U V a d β s
      (b.hom.app ⟨P, hP⟩) (hbase ⟨P, hP⟩)
  · intro β' hn'
    apply huniq
    intro P
    have h := hn' P.obj P.obj (𝟙 P.obj) inferInstance P.property
    have he := normalized_id DerivedCategory.Q F G U V a d β' P.obj (b.hom.app P) h
    have := hd P
    exact ((cancel_mono (d.app P.obj)).1 (he.trans (hbase P).symm)).trans (hβ P)

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (RY SY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (RX SX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (jY : RY ⟶ SY) (jX : RX ⟶ SX)
  (cR : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RY ≅ RX)
  (cS : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj SY ≅ SX)

/-- `G_R`: the actual module inverse image with coefficients identified by `cR`.
Extension along a ring isomorphism is canonical action transport, by multiplication
and the inverse `m ↦ m ⊗ 1`. -/
abbrev inverseR := proEtaleRingModulePullback g RY RX cR

/-- `G_S`, with the same geometric inverse image and the specified coefficient transport. -/
abbrev inverseS := proEtaleRingModulePullback g SY SX cS

variable (CY : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2}
    (J := ProEt.topology Y) jY)
  (CX : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2}
    (J := ProEt.topology X) jX)

/-- `U(P) = G_R(P) ⊗ S_X`, with the ordinary termwise scalar extension. -/
abbrev U := (inverseR g RY RX cR).mapHomologicalComplex (.up ℤ) ⋙
  CX.E.mapHomologicalComplex (.up ℤ)

/-- `V(P) = G_S(P ⊗ S_Y)`, with ordinary termwise scalar extension. -/
abbrev V := CY.E.mapHomologicalComplex (.up ℤ) ⋙
  (inverseS g SY SX cS).mapHomologicalComplex (.up ℤ)

/-- The source derived composite `C_X G_R`. -/
abbrev A := (inverseR g RY RX cR).mapDerivedCategory ⋙ CX.T

/-- The target derived composite `G_S C_Y`. -/
abbrev B := CY.T ⋙ (inverseS g SY SX cS).mapDerivedCategory

/-- The canonical source representative identification for a good resolution `s`.
Its first factor inverts the localized resolution; its second is exact inverse image;
its last is the K-flat counit of ordinary derived change of rings. -/
def sourceIso (P K : CochainComplex (proEtaleRingModules Y RY) ℤ)
    (s : P ⟶ K) [QuasiIso s]
    (hP : good RX (((inverseR g RY RX cR).mapHomologicalComplex (.up ℤ)).obj P)) :
    (A g RY RX SX jX cR CX).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((U g RY RX SX jX cR CX).obj P) :=
  ((A g RY RX SX jX cR CX).mapIso (asIso (DerivedCategory.Q.map s))).symm ≪≫
    CX.T.mapIso ((inverseR g RY RX cR).mapDerivedCategoryFactors.app P) ≪≫
    @asIso _ _ _ _ (CX.ε.app
      (((inverseR g RY RX cR).mapHomologicalComplex (.up ℤ)).obj P))
      (CX.computes _ hP.1)

/-- The canonical target representative identification for a good resolution `s`.
It uses the scalar counit on `P` and then the exact `G_S` representative comparison. -/
def targetIso (P K : CochainComplex (proEtaleRingModules Y RY) ℤ)
    (s : P ⟶ K) [QuasiIso s] (hP : good RY P) :
    (B g RY SY SX jY cS CY).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((V g RY SY SX jY cS CY).obj P) :=
  ((B g RY SY SX jY cS CY).mapIso (asIso (DerivedCategory.Q.map s))).symm ≪≫
    (inverseS g SY SX cS).mapDerivedCategory.mapIso
      (@asIso _ _ _ _ (CY.ε.app P) (CY.computes _ hP.1)) ≪≫
    (inverseS g SY SX cS).mapDerivedCategoryFactors.app
      ((CY.E.mapHomologicalComplex (.up ℤ)).obj P)

/-- The component normalization on every flat-term K-flat resolution. Both sides are
isomorphisms with exactly the same source and target; the source identification
includes the localized quasi-isomorphism `G_R P → G_R K` through exact descent. -/
def Normalized
    (hGR : ∀ P : CochainComplex (proEtaleRingModules Y RY) ℤ,
      good RY P → good RX (((inverseR g RY RX cR).mapHomologicalComplex (.up ℤ)).obj P))
    (b : (good RY).ι ⋙ U g RY RX SX jX cR CX ≅
      (good RY).ι ⋙ V g RY SY SX jY cS CY)
    (β : A g RY RX SX jX cR CX ≅ B g RY SY SX jY cS CY) : Prop :=
  ∀ (P K : CochainComplex (proEtaleRingModules Y RY) ℤ)
    (s : P ⟶ K) (_ : QuasiIso s) (hP : good RY P),
    β.app (DerivedCategory.Q.obj K) ≪≫ targetIso g RY SY SX jY cS CY P K s hP =
      sourceIso g RY RX SX jX cR CX P K s (hGR P hP) ≪≫
        DerivedCategory.Q.mapIso (b.app ⟨P, hP⟩)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem inverse_good (P : CochainComplex (proEtaleRingModules Y RY) ℤ)
    (hP : good RY P) :
    good RX (((inverseR g RY RX cR).mapHomologicalComplex (.up ℤ)).obj P) := by
  have : PreservesFiniteLimits (proEtaleSheafInverseImage g (Type (u + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage g (𝟙 Y)).2.2.2.1
  obtain ⟨I, hI⟩ := proEtaleAlgebraicInverseImage_exists g RY
  let C := proEtaleRingModules Y RY
  let D := proEtaleRingModules X
    ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RY)
  let c := cR.hom
  have hm (F : C ⥤ D) (h : I.modules = F) {M N : C} (f : M ⟶ N) :
      SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} c (F.obj M) (F.map f) =
        eqToHom (congrArg (fun G : C ⥤ D ↦
          SheafOfModules.changeOfRings.{u, u + 1, u + 1} c (G.obj M)) h.symm) ≫
        SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
          c (I.modules.obj M) (I.modules.map f) ≫
        eqToHom (congrArg (fun G : C ⥤ D ↦
          SheafOfModules.changeOfRings.{u, u + 1, u + 1} c (G.obj N)) h.symm).symm := by
    subst F
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact SheafOfModules.isKFlat_ringedToposPullback
    (proEtaleSheafInverseImage g (Type (u + 1)))
    (proEtaleSheafDirectImage g (Type (u + 1)))
    (proEtaleSheafAdjunction g (Type (u + 1))) I cR.hom (inverseR g RY RX cR)
    (fun M ↦ congrArg (fun F : C ⥤ D ↦
      SheafOfModules.changeOfRings.{u, u + 1, u + 1} c (F.obj M)) hI.symm)
    (fun f ↦ hm _ hI f) P hP.1 hP.2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def identityInverse {W : Scheme.{u}}
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) :
    SheafOfModules.AlgebraicInverseImage (𝟭 (Sheaf (ProEt.topology W) (Type (u + 1))))
      R R where
  ringUnderlying := Iso.refl _
  ringAdd := fun _ _ _ _ h ↦ h
  ringMul := fun _ _ _ _ h ↦ h
  ringZero := fun _ _ h ↦ h
  ringOne := fun _ _ h ↦ h
  modules := 𝟭 _
  moduleUnderlying := Iso.refl _
  moduleAdd := fun _ _ _ _ _ h ↦ h
  moduleZero := fun _ _ _ h ↦ h
  moduleSMul := fun _ _ _ _ _ h ↦ h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalar_good {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} {j : R ⟶ S}
    (C : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2} j)
    (P : CochainComplex (proEtaleRingModules W R) ℤ) (hP : good R P) :
    good S ((C.E.mapHomologicalComplex (.up ℤ)).obj P) := by
  exact SheafOfModules.isKFlat_ringedToposPullback (𝟭 _) (𝟭 _) Adjunction.id
    (identityInverse R) j C.E C.obj_eq C.map_eq P hP.1 hP.2

set_option backward.isDefEq.respectTransparency true in
@[irreducible] private def sourceCounit :
    DerivedCategory.Q ⋙ A g RY RX SX jX cR CX ⟶
      U g RY RX SX jX cR CX ⋙ DerivedCategory.Q :=
  composeSquare DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    ((inverseR g RY RX cR).mapHomologicalComplex (.up ℤ))
    (CX.E.mapHomologicalComplex (.up ℤ))
    (inverseR g RY RX cR).mapDerivedCategory CX.T
    (inverseR g RY RX cR).mapDerivedCategoryFactors.hom CX.ε

set_option backward.isDefEq.respectTransparency true in
@[irreducible] private def targetCounit :
    DerivedCategory.Q ⋙ B g RY SY SX jY cS CY ⟶
      V g RY SY SX jY cS CY ⋙ DerivedCategory.Q :=
  composeSquare DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    (CY.E.mapHomologicalComplex (.up ℤ))
    ((inverseS g SY SX cS).mapHomologicalComplex (.up ℤ))
    CY.T (inverseS g SY SX cS).mapDerivedCategory
    CY.ε (inverseS g SY SX cS).mapDerivedCategoryFactors.hom

set_option backward.isDefEq.respectTransparency true in
attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh
  proEtaleRingModulePullback Functor.mapDerivedCategory

end AlgebraicGeometry.Scheme.IsomorphismScalarKFlatDescent

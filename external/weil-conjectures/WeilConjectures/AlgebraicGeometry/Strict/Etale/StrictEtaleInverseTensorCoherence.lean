/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleSystemInterfaces
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

/-! # Coherence of inverse image with quotient coefficient extension

Source: Zheng, Construction 4.1 and Lemma 5.16; Stacks Tag 0D6D.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
attribute [local irreducible] coefficientQuotientSheaf coefficientQuotientMap
  siteCoefficientTensorAdj

/-- Transporting an adjunction transpose across an underlying-functor comparison. -/
private theorem transpose_underlying
    {C₁ C₂ B : Type*} [Category C₁] [Category C₂] [Category B]
    {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₁} (a : F ⊣ G)
    (U : C₁ ⥤ B) (V : C₂ ⥤ B) (q : G ⋙ U ≅ V)
    (M : C₁) (N : C₂) (f : F.obj M ⟶ N) :
    U.map (a.homEquiv M N f) ≫ q.hom.app N =
      (U.map (a.unit.app M) ≫ q.hom.app (F.obj M)) ≫ V.map f := by
  rw [a.homEquiv_unit, U.map_comp, Category.assoc]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun k ↦ U.map (a.unit.app M) ≫ k) (q.hom.naturality f)

section SiteHelpers
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (T : GrothendieckTopology C)
  [T.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
  [T.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasSheafify T AddCommGrpCat.{u + 1}] [HasWeakSheafify T CommRingCat.{u + 1}]
  [HasWeakSheafify T (Type (u + 1))]
  [T.HasSheafCompose (CategoryTheory.forget CommRingCat.{u + 1})]
  [T.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1})]
  {O : Type (u + 1)} [CommRing O] {t : O}

private abbrev tensor {m n : ℕ} (h : n ≤ m) :=
  coefficientTensor.{u + 1, u, u + 1} (J := T) (O := O) (ell := t) h

private abbrev tensorAdj {m n : ℕ} (h : n ≤ m) :=
  coefficientTensorAdj.{u + 1, u, u + 1} (J := T) (O := O) (ell := t) h

private abbrev underlying (n : ℕ) :=
  coefficientUnderlying (J := T) O t n

private def insertion {m n : ℕ} (h : n ≤ m)
    (M : coefficientLevelModules (J := T) O t m) :
    (underlying (O := O) (t := t) T m).obj M ⟶
      (underlying (O := O) (t := t) T n).obj ((tensor T h).obj M) :=
  (underlying T m).map ((tensorAdj T h).unit.app M) ≫
    (coefficientRestrictionUnderlying (J := T) O t h).hom.app
      ((tensor T h).obj M)

private theorem insertion_naturality {m n : ℕ} (h : n ≤ m)
    {M N : coefficientLevelModules (J := T) O t m} (f : M ⟶ N) :
    (underlying T m).map f ≫ insertion T h N =
      insertion T h M ≫ (underlying T n).map ((tensor T h).map f) := by
  have hu := congrArg ((underlying T m).map) ((tensorAdj T h).unit.naturality f)
  have hr := (coefficientRestrictionUnderlying (J := T) O t h).hom.naturality
    ((tensor T h).map f)
  dsimp only [insertion]
  dsimp only [underlying, coefficientUnderlying, Functor.comp_map] at hu hr ⊢
  simp only [Functor.map_comp, Category.assoc] at hu ⊢
  rw [reassoc_of% hu, hr]

private theorem insertion_transpose {m n : ℕ} (h : n ≤ m)
    (M : coefficientLevelModules (J := T) O t m)
    (N : coefficientLevelModules (J := T) O t n) (f : (tensor T h).obj M ⟶ N) :
    (underlying T m).map ((tensorAdj T h).homEquiv M N f) ≫
      (coefficientRestrictionUnderlying (J := T) O t h).hom.app N =
    insertion T h M ≫ (underlying T n).map f := by
  exact transpose_underlying (tensorAdj T h) (underlying T m) (underlying T n)
    (coefficientRestrictionUnderlying (J := T) O t h) M N f

variable [∀ n, HasDerivedCategory.{u + 2} (coefficientLevelModules (J := T) O t n)]
  [HasDerivedCategory.{u + 2} (CoefficientSystem (J := T) O t)]

private theorem insertion_unit
    (P : CoefficientEvaluationDerivedPackage (J := T) (O := O) (ell := t))
    (n : ℕ) (M : coefficientLevelModules (J := T) O t n) :
    insertion T (Nat.le_refl n) M ≫ (underlying T n).map ((P.tensorUnit n).hom.app M) =
      𝟙 _ := by
  ext U x
  exact congrArg (fun f ↦ f.hom.app U x) (P.tensorUnit_normalized n M)

private theorem insertion_comp
    (P : CoefficientEvaluationDerivedPackage (J := T) (O := O) (ell := t))
    {r m n : ℕ} (h₁ : m ≤ r) (h₂ : n ≤ m)
    (M : coefficientLevelModules (J := T) O t r) :
    insertion T h₁ M ≫ insertion T h₂ ((tensor T h₁).obj M) ≫
      (underlying T n).map ((P.tensorAssoc h₁ h₂).hom.app M) =
        insertion T (h₂.trans h₁) M := by
  ext U x
  exact congrArg (fun f ↦ f.hom.app U x) (P.tensorAssoc_normalized h₁ h₂ M)

private def identityInverse (n : ℕ) :
    AlgebraicInverseImage (𝟭 (Sheaf T (Type (u + 1))))
      (coefficientQuotientSheaf (J := T) O t n)
      (coefficientQuotientSheaf (J := T) O t n) where
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

private theorem scalar_good {m n : ℕ} (h : n ≤ m)
    (P : CochainComplex (coefficientLevelModules (J := T) O t m) ℤ)
    (hk : P.IsKFlatIndependentCoefficients)
    (hf : ∀ i : ℤ, IsFlatOnSite (J := T)
      (R := coefficientQuotientSheaf (J := T) O t m) (P.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients
      (((tensor T h).mapHomologicalComplex (.up ℤ)).obj P) ∧
    ∀ i : ℤ, IsFlatOnSite (J := T)
      (R := coefficientQuotientSheaf (J := T) O t n)
      ((((tensor T h).mapHomologicalComplex (.up ℤ)).obj P).X i) := by
  exact isKFlat_ringedToposPullback (𝟭 _) (𝟭 _) Adjunction.id
    (identityInverse T m) (coefficientQuotientMap (J := T) O t h) (tensor T h)
    (fun _ ↦ rfl) (by intro M N f; simp only [eqToHom_refl, Category.id_comp,
      Category.comp_id]; rfl) P hk hf

private theorem hom_ext_flat (n : ℕ)
    {B : Type*} [Category B]
    {F G : DerivedCategory (coefficientLevelModules (J := T) O t n) ⥤ B} (α β : F ⟶ G)
    (h : ∀ (P : CochainComplex (coefficientLevelModules (J := T) O t n) ℤ),
      P.IsKFlatIndependentCoefficients →
      (∀ i : ℤ, IsFlatOnSite (J := T)
      (R := coefficientQuotientSheaf (J := T) O t n) (P.X i)) →
      α.app (DerivedCategory.Q.obj P) = β.app (DerivedCategory.Q.obj P)) : α = β := by
  ext N
  obtain ⟨P, q, hk, hf, hq, _⟩ := CochainComplex.exists_isKFlatResolutionIndependentCoefficients
    (R := coefficientQuotientSheaf (J := T) O t n)
    (DerivedCategory.Q.objPreimage N)
  let := hq
  let i : DerivedCategory.Q.obj P ≅ N :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso N
  apply (cancel_epi (F.map i.hom)).1
  rw [α.naturality, β.naturality]
  rw [h P hk (fun j ↦ (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso _ (P.X j)).symm (hf j))]

end SiteHelpers

section Images
variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasSheafify J AddCommGrpCat.{u + 1}] [HasWeakSheafify J CommRingCat.{u + 1}]
  [HasWeakSheafify J (Type (u + 1))]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u + 1})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasSheafify K AddCommGrpCat.{u + 1}] [HasWeakSheafify K CommRingCat.{u + 1}]
  [HasWeakSheafify K (Type (u + 1))]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{u + 1})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1})]
  {O : Type (u + 1)} [CommRing O] {t : O}
  [∀ n, HasDerivedCategory.{u + 2} (coefficientLevelModules (J := J) O t n)]
  [∀ n, HasDerivedCategory.{u + 2} (coefficientLevelModules (J := K) O t n)]
  [HasDerivedCategory.{u + 2} (CoefficientSystem (J := J) O t)]
  [HasDerivedCategory.{u + 2} (CoefficientSystem (J := K) O t)]
  {L : Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1))}
  {R : Sheaf K (Type (u + 1)) ⥤ Sheaf J (Type (u + 1))} {adj : L ⊣ R}
  (PW : CoefficientEvaluationDerivedPackage (J := J) (O := O) (ell := t))
  (PV : CoefficientEvaluationDerivedPackage (J := K) (O := O) (ell := t))
  (A : CoefficientSystemOrdinaryImage O t L R adj)
  (E : CoefficientSystemDerivedImage O t L R adj A PW PV)

-- The nested transpose exposes the underlying sheaf functors through several quotients.
private theorem insertion_ext {m n : ℕ} (h : n ≤ m)
    (M : coefficientLevelModules (J := J) O t m) (N : coefficientLevelModules (J := K) O t n)
    (f k : (A.lift n).modules.obj ((tensor J h).obj M) ⟶ N)
    (he : L.map (insertion J h M) ≫
        (A.lift n).moduleUnderlying.inv.app _ ≫ (underlying K n).map f =
      L.map (insertion J h M) ≫
        (A.lift n).moduleUnderlying.inv.app _ ≫ (underlying K n).map k) : f = k := by
  apply ((A.levelAdj n).homEquiv _ N).injective
  apply ((tensorAdj J h).homEquiv M _).injective
  apply (underlying J m).map_injective
  apply (cancel_mono ((coefficientRestrictionUnderlying (J := J) O t h).hom.app
    ((A.right n).obj N) ≫ (A.rightUnderlying n).hom.app N)).1
  have hf := insertion_transpose J h M ((A.right n).obj N)
    ((A.levelAdj n).homEquiv _ _ f)
  have hk := insertion_transpose J h M ((A.right n).obj N)
    ((A.levelAdj n).homEquiv _ _ k)
  erw [reassoc_of% hf, reassoc_of% hk]
  have tf := A.levelTranspose n ((tensor J h).obj M) N f
  have tk := A.levelTranspose n ((tensor J h).obj M) N k
  dsimp only [coefficientUnderlying, Functor.comp_map] at tf tk
  erw [tf, tk]
  erw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_left]
  exact congrArg (adj.homEquiv _ _) he

-- The nested transpose exposes the underlying sheaf functors through several quotients.
private theorem insertion_ext_double {r m n : ℕ} (h₁ : m ≤ r) (h₂ : n ≤ m)
    (M : coefficientLevelModules (J := J) O t r) (N : coefficientLevelModules (J := K) O t n)
    (f k : (A.lift n).modules.obj
      ((tensor J h₂).obj ((tensor J h₁).obj M)) ⟶ N)
    (he : L.map (insertion J h₁ M) ≫
        L.map
          (insertion J h₂ ((tensor J h₁).obj M)) ≫
        (A.lift n).moduleUnderlying.inv.app _ ≫ (underlying K n).map f =
      L.map (insertion J h₁ M) ≫
        L.map
          (insertion J h₂ ((tensor J h₁).obj M)) ≫
        (A.lift n).moduleUnderlying.inv.app _ ≫ (underlying K n).map k) : f = k := by
  apply ((A.levelAdj n).homEquiv _ N).injective
  apply ((tensorAdj J h₂).homEquiv _ _).injective
  apply ((tensorAdj J h₁).homEquiv M _).injective
  apply (underlying J r).map_injective
  apply (cancel_mono ((coefficientRestrictionUnderlying (J := J) O t h₁).hom.app
    ((coefficientRestriction (J := J) O t h₂).obj ((A.right n).obj N)) ≫
      (coefficientRestrictionUnderlying (J := J) O t h₂).hom.app ((A.right n).obj N) ≫
        (A.rightUnderlying n).hom.app N)).1
  have hf := insertion_transpose J h₁ M
    ((coefficientRestriction (J := J) O t h₂).obj ((A.right n).obj N))
    ((tensorAdj J h₂).homEquiv _ _ ((A.levelAdj n).homEquiv _ _ f))
  have hk := insertion_transpose J h₁ M
    ((coefficientRestriction (J := J) O t h₂).obj ((A.right n).obj N))
    ((tensorAdj J h₂).homEquiv _ _ ((A.levelAdj n).homEquiv _ _ k))
  have hf' := insertion_transpose J h₂ ((tensor J h₁).obj M)
    ((A.right n).obj N) ((A.levelAdj n).homEquiv _ _ f)
  have hk' := insertion_transpose J h₂ ((tensor J h₁).obj M)
    ((A.right n).obj N) ((A.levelAdj n).homEquiv _ _ k)
  erw [reassoc_of% hf, reassoc_of% hk, reassoc_of% hf', reassoc_of% hk']
  have tf := A.levelTranspose n ((tensor J h₂).obj ((tensor J h₁).obj M)) N f
  have tk := A.levelTranspose n ((tensor J h₂).obj ((tensor J h₁).obj M)) N k
  dsimp only [coefficientUnderlying, Functor.comp_map] at tf tk
  erw [tf, tk]
  erw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_left]
  erw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_left]
  apply congrArg (adj.homEquiv _ _)
  change L.map (insertion J h₁ M) ≫
      L.map (insertion J h₂ ((tensor J h₁).obj M)) ≫
      (A.lift n).moduleUnderlying.inv.app _ ≫ (underlying K n).map f =
    L.map (insertion J h₁ M) ≫
      L.map (insertion J h₂ ((tensor J h₁).obj M)) ≫
      (A.lift n).moduleUnderlying.inv.app _ ≫ (underlying K n).map k
  exact he

private theorem tensor_insertion {m n : ℕ} (h : n ≤ m)
    (M : coefficientLevelModules (J := J) O t m) :
    L.map (insertion J h M) ≫
        (A.lift n).moduleUnderlying.inv.app _ ≫
        (underlying K n).map ((E.tensor h).hom.app M) =
      (A.lift m).moduleUnderlying.inv.app M ≫
        insertion K h ((A.lift m).modules.obj M) := by
  apply (cancel_epi ((A.lift m).moduleUnderlying.hom.app M)).1
  have hn := (A.lift m).moduleUnderlying.hom.naturality
    ((tensorAdj J h).unit.app M)
  have hd := A.restrictInverseUnderlying h ((tensor J h).obj M)
  have hu := congrArg ((underlying K m).map) (E.tensor_unit h M)
  have hq := (coefficientRestrictionUnderlying (J := K) O t h).hom.naturality
    ((E.tensor h).hom.app M)
  dsimp only [insertion]
  dsimp only [underlying, coefficientUnderlying, Functor.comp_map] at hn hd hu hq ⊢
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% hn, ← reassoc_of% hd]
  simp only [Iso.hom_inv_id_app_assoc]
  erw [← hq]
  have hh := congrArg (fun f ↦ f ≫
    (coefficientRestrictionUnderlying (J := K) O t h).hom.app
      ((tensor K h).obj ((A.lift m).modules.obj M))) hu
  simp only [Functor.map_comp, Category.assoc] at hh
  convert hh using 1 <;> rfl

private theorem ordinary_unit (n : ℕ) (M : coefficientLevelModules (J := J) O t n) :
    (E.tensor (Nat.le_refl n)).hom.app M ≫
      (PV.tensorUnit n).hom.app ((A.lift n).modules.obj M) =
    (A.lift n).modules.map ((PW.tensorUnit n).hom.app M) := by
  apply insertion_ext A (Nat.le_refl n) M
  have hn := (A.lift n).moduleUnderlying.inv.naturality ((PW.tensorUnit n).hom.app M)
  dsimp only [Functor.comp_map] at hn
  change L.map ((underlying J n).map ((PW.tensorUnit n).hom.app M)) ≫ _ =
    _ ≫ (underlying K n).map ((A.lift n).modules.map
      ((PW.tensorUnit n).hom.app M)) at hn
  simp only [Functor.map_comp]
  erw [reassoc_of% tensor_insertion PW PV A E (Nat.le_refl n) M,
    insertion_unit K PV n ((A.lift n).modules.obj M)]
  erw [← hn, ← L.map_comp_assoc, insertion_unit J PW]
  change (A.lift n).moduleUnderlying.inv.app M ≫ 𝟙 _ =
    L.map (𝟙 _) ≫ (A.lift n).moduleUnderlying.inv.app M
  erw [L.map_id, Category.id_comp, Category.comp_id]

private theorem ordinary_composition {r m n : ℕ} (h₁ : m ≤ r) (h₂ : n ≤ m)
    (M : coefficientLevelModules (J := J) O t r) :
    (A.lift n).modules.map ((PW.tensorAssoc h₁ h₂).hom.app M) ≫
        (E.tensor (h₂.trans h₁)).hom.app M =
      (E.tensor h₂).hom.app ((tensor J h₁).obj M) ≫
        (tensor K h₂).map ((E.tensor h₁).hom.app M) ≫
        (PV.tensorAssoc h₁ h₂).hom.app ((A.lift r).modules.obj M) := by
  apply insertion_ext_double A h₁ h₂ M
  have hn := (A.lift n).moduleUnderlying.inv.naturality
    ((PW.tensorAssoc h₁ h₂).hom.app M)
  dsimp only [Functor.comp_map] at hn
  have hi := insertion_naturality K h₂ ((E.tensor h₁).hom.app M)
  change L.map ((underlying J n).map ((PW.tensorAssoc h₁ h₂).hom.app M)) ≫ _ =
    _ ≫ (underlying K n).map ((A.lift n).modules.map
      ((PW.tensorAssoc h₁ h₂).hom.app M)) at hn
  simp only [Functor.map_comp]
  erw [← reassoc_of% hn, ← L.map_comp_assoc,
    ← L.map_comp_assoc]
  erw [Category.assoc (insertion J h₁ M), insertion_comp J PW h₁ h₂ M,
    tensor_insertion PW PV A E (h₂.trans h₁) M]
  -- Focus on each insertion to avoid unfolding unrelated functor composites while matching.
  conv_rhs =>
    arg 2
    erw [reassoc_of% tensor_insertion PW PV A E h₂ ((tensor J h₁).obj M)]
  conv_rhs =>
    arg 2; arg 2
    erw [← reassoc_of% hi]
  conv_rhs => erw [reassoc_of% tensor_insertion PW PV A E h₁ M]
  conv_rhs =>
    arg 2
    erw [insertion_comp K PV h₁ h₂ ((A.lift r).modules.obj M)]

variable [PreservesFiniteLimits L]

include PV in
private theorem inverse_good (n : ℕ)
    (P : CochainComplex (coefficientLevelModules (J := J) O t n) ℤ)
    (hk : P.IsKFlatIndependentCoefficients)
    (hf : ∀ i : ℤ, IsFlatOnSite (J := J)
      (R := coefficientQuotientSheaf (J := J) O t n) (P.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients
      (((A.lift n).modules.mapHomologicalComplex (.up ℤ)).obj P) ∧
    ∀ i : ℤ, IsFlatOnSite (J := K)
      (R := coefficientQuotientSheaf (J := K) O t n)
      ((((A.lift n).modules.mapHomologicalComplex (.up ℤ)).obj P).X i) := by
  let F := (A.lift n).modules
  let S := coefficientTensor (J := K) (O := O) (ell := t)
    (Nat.le_refl n)
  have ht := isKFlat_ringedToposPullback L _
    adj (A.lift n)
    (coefficientQuotientMap (J := K) O t (Nat.le_refl n))
    (F ⋙ S) (fun _ ↦ rfl) (by
      intro M N f
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl) P hk hf
  let e : F ⋙ S ≅ F := Functor.isoWhiskerLeft F (PV.tensorUnit n) ≪≫ F.rightUnitor
  let ec := (NatIso.mapHomologicalComplex e (.up ℤ)).app P
  exact ⟨kFlat_iso_independent (coefficientQuotientSheaf (J := K) O t n) ec ht.1,
    fun i ↦ flatOnSite_of_iso (coefficientQuotientSheaf (J := K) O t n)
      (e.app (P.X i)) (ht.2 i)⟩

private theorem composition_on_flat {r m n : ℕ} (h₁ : m ≤ r) (h₂ : n ≤ m)
    (P : CochainComplex (coefficientLevelModules (J := J) O t r) ℤ)
    (hk : P.IsKFlatIndependentCoefficients)
    (hf : ∀ i : ℤ, IsFlatOnSite (J := J)
      (R := coefficientQuotientSheaf (J := J) O t r) (P.X i)) :
    (E.level n).inverse.map ((PW.derivedAssoc h₁ h₂).hom.app (DerivedCategory.Q.obj P)) ≫
        (E.derivedTensor (h₂.trans h₁)).hom.app (DerivedCategory.Q.obj P) =
      (E.derivedTensor h₂).hom.app ((PW.scalar h₁).derived.obj (DerivedCategory.Q.obj P)) ≫
        (PV.scalar h₂).derived.map ((E.derivedTensor h₁).hom.app (DerivedCategory.Q.obj P)) ≫
        (PV.derivedAssoc h₁ h₂).hom.app ((E.level r).inverse.obj (DerivedCategory.Q.obj P)) := by
  let I := (A.lift r).modules.mapHomologicalComplex (.up ℤ)
  have hI := inverse_good PV A r P hk hf
  let := (PV.scalar (h₂.trans h₁)).computes (I.obj P) hI.1
  apply (cancel_mono ((PV.scalar (h₂.trans h₁)).derived.map
    ((E.level r).inverseFactors.hom.app P) ≫
      (PV.scalar (h₂.trans h₁)).counit.app (I.obj P))).1
  simp only [Category.assoc]
  erw [E.derivedTensor_rep (h₂.trans h₁) P hk hf]
  have hn := (PV.derivedAssoc h₁ h₂).hom.naturality ((E.level r).inverseFactors.hom.app P)
  dsimp only [Functor.comp_map] at hn
  erw [← reassoc_of% hn, PV.derivedAssoc_rep h₁ h₂ (I.obj P) hI.1 hI.2]
  have ha := congrArg (fun f ↦ (PV.scalar h₂).derived.map f)
    (E.derivedTensor_rep h₁ P hk hf)
  simp only [Functor.map_comp] at ha
  erw [reassoc_of% ha]
  have hc := (PV.scalar h₂).counit.naturality
    ((NatTrans.mapHomologicalComplex (E.tensor h₁).hom (.up ℤ)).app P)
  dsimp only [Functor.comp_map] at hc
  change (PV.scalar h₂).derived.map (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (E.tensor h₁).hom (.up ℤ)).app P)) ≫
      (PV.scalar h₂).counit.app
        (((tensor K h₁).mapHomologicalComplex (.up ℤ)).obj (I.obj P)) =
    (PV.scalar h₂).counit.app
      (((A.lift m).modules.mapHomologicalComplex (.up ℤ)).obj
        (((tensor J h₁).mapHomologicalComplex (.up ℤ)).obj P)) ≫
      DerivedCategory.Q.map (((tensor K h₂).mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (E.tensor h₁).hom (.up ℤ)).app P)) at hc
  conv_rhs =>
    arg 2; arg 2; arg 2
    erw [reassoc_of% hc]
  have hb := scalar_good J h₁ P hk hf
  have hnb := (E.derivedTensor h₂).hom.naturality ((PW.scalar h₁).counit.app P)
  dsimp only [Functor.comp_map] at hnb
  conv_rhs => erw [← reassoc_of% hnb]
  conv_rhs =>
    arg 2
    erw [reassoc_of% E.derivedTensor_rep h₂ _ hb.1 hb.2]
  have hy := congrArg (fun f ↦ (E.level n).inverse.map f)
    (PW.derivedAssoc_rep h₁ h₂ P hk hf)
  simp only [Functor.map_comp] at hy
  conv_lhs => erw [reassoc_of% hy]
  have hnA := (E.level n).inverseFactors.hom.naturality (PW.tensorAssocComplex h₁ h₂ P).hom
  dsimp only [Functor.comp_map] at hnA
  conv_lhs =>
    arg 2; arg 2
    erw [reassoc_of% hnA]
  simp only [← DerivedCategory.Q.map_comp]
  congr 3
  apply congrArg DerivedCategory.Q.map
  ext i : 1
  simp only [I, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, NatIso.mapHomologicalComplex_hom_app_f,
    PW.tensorAssocComplex_f,
    PV.tensorAssocComplex_f]
  convert ordinary_composition PW PV A E h₁ h₂ (P.X i) using 1 <;> rfl

private theorem unit_on_flat (n : ℕ)
    (P : CochainComplex (coefficientLevelModules (J := J) O t n) ℤ)
    (hk : P.IsKFlatIndependentCoefficients)
    (hf : ∀ i : ℤ, IsFlatOnSite (J := J)
      (R := coefficientQuotientSheaf (J := J) O t n) (P.X i)) :
    (E.derivedTensor (Nat.le_refl n)).hom.app (DerivedCategory.Q.obj P) ≫
        (PV.derivedUnit n).hom.app ((E.level n).inverse.obj (DerivedCategory.Q.obj P)) =
      (E.level n).inverse.map ((PW.derivedUnit n).hom.app (DerivedCategory.Q.obj P)) := by
  let I := (A.lift n).modules.mapHomologicalComplex (.up ℤ)
  have hI := inverse_good PV A n P hk hf
  apply (cancel_mono ((E.level n).inverseFactors.hom.app P)).1
  have hn := (PV.derivedUnit n).hom.naturality ((E.level n).inverseFactors.hom.app P)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [Category.assoc]
  erw [← hn, PV.derivedUnit_rep n (I.obj P) hI.1]
  have he := congrArg (fun f ↦ f ≫ DerivedCategory.Q.map (PV.tensorUnitComplex n (I.obj P)).hom)
    (E.derivedTensor_rep (Nat.le_refl n) P hk hf)
  simp only [Category.assoc] at he
  have ho : (NatTrans.mapHomologicalComplex (E.tensor (Nat.le_refl n)).hom (.up ℤ)).app P ≫
      (PV.tensorUnitComplex n (I.obj P)).hom =
    I.map (PW.tensorUnitComplex n P).hom := by
    ext i : 1
    simp only [I, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      NatTrans.mapHomologicalComplex_app_f,
      PW.tensorUnitComplex_f,
      PV.tensorUnitComplex_f]
    convert ordinary_unit PW PV A E n (P.X i) using 1 <;> rfl
  apply he.trans
  erw [← DerivedCategory.Q.map_comp, ho]
  have hnU := (E.level n).inverseFactors.hom.naturality (PW.tensorUnitComplex n P).hom
  dsimp only [Functor.comp_map] at hnU
  erw [← hnU, ← (E.level n).inverse.map_comp_assoc, ← PW.derivedUnit_rep n P hk]

private theorem generic_coherence :
    (∀ (n : ℕ) P,
      (E.derivedTensor (Nat.le_refl n)).hom.app P ≫
        (PV.derivedUnit n).hom.app ((E.level n).inverse.obj P) =
      (E.level n).inverse.map ((PW.derivedUnit n).hom.app P)) ∧
    (∀ {r m n : ℕ} (h₁ : m ≤ r) (h₂ : n ≤ m) P,
      (E.level n).inverse.map ((PW.derivedAssoc h₁ h₂).hom.app P) ≫
        (E.derivedTensor (h₂.trans h₁)).hom.app P =
      (E.derivedTensor h₂).hom.app ((PW.scalar h₁).derived.obj P) ≫
        (PV.scalar h₂).derived.map ((E.derivedTensor h₁).hom.app P) ≫
        (PV.derivedAssoc h₁ h₂).hom.app ((E.level r).inverse.obj P)) := by
  constructor
  · intro n P
    let α : (PW.scalar (Nat.le_refl n)).derived ⋙ (E.level n).inverse ⟶
        (E.level n).inverse :=
      (E.derivedTensor (Nat.le_refl n)).hom ≫
        Functor.whiskerLeft (E.level n).inverse (PV.derivedUnit n).hom
    let β : (PW.scalar (Nat.le_refl n)).derived ⋙ (E.level n).inverse ⟶
        (E.level n).inverse :=
      Functor.whiskerRight (PW.derivedUnit n).hom (E.level n).inverse
    exact NatTrans.congr_app
      (hom_ext_flat J n α β (unit_on_flat PW PV A E n)) P
  · intro r m n h₁ h₂ P
    let α : ((PW.scalar h₁).derived ⋙ (PW.scalar h₂).derived) ⋙
        (E.level n).inverse ⟶ (E.level r).inverse ⋙
          (PV.scalar (h₂.trans h₁)).derived :=
      Functor.whiskerRight (PW.derivedAssoc h₁ h₂).hom (E.level n).inverse ≫
        (E.derivedTensor (h₂.trans h₁)).hom
    let β : ((PW.scalar h₁).derived ⋙ (PW.scalar h₂).derived) ⋙
        (E.level n).inverse ⟶ (E.level r).inverse ⋙
          (PV.scalar (h₂.trans h₁)).derived :=
      Functor.whiskerLeft (PW.scalar h₁).derived (E.derivedTensor h₂).hom ≫
        Functor.whiskerRight (E.derivedTensor h₁).hom (PV.scalar h₂).derived ≫
        Functor.whiskerLeft (E.level r).inverse (PV.derivedAssoc h₁ h₂).hom
    exact NatTrans.congr_app
      (hom_ext_flat J r α β (composition_on_flat PW PV A E h₁ h₂)) P

end Images

/-- The normalized inverse-image tensor comparisons preserve the multiplication unit
and balanced associator of quotient scalar extension.

Source: Zheng, Construction 4.1 and Lemma 5.16, printed pp. 21 and 34--35;
Stacks Tag 0D6D (derived pullback composition).
(blueprint: lem-pur-strict-etale-inverse-tensor-coherence).

Proof: first work on ordinary modules. Transpose under the scalar adjunctions.
The comparison `tensor` is fixed by `tensor_unit`: insertion of `1 tensor x`,
followed by the restriction comparison, is insertion after inverse image.
The ordinary restriction comparisons are fixed on underlying sheaves by the
geometric lift, so their composites are the comparison for the composite quotient
map. For the identity map the same comparison is the restriction multiplication
unit. The normalized ordinary tensor associators take two successive insertions
to the direct insertion. Injectivity of the scalar Hom transposes proves the
ordinary unit and composition squares.

Choose a flat-term K-flat resolution of the input complex. Exact geometric inverse
image preserves flat-term K-flat complexes, as does coefficient extension. Apply
`derivedTensor_rep`, `derivedUnit_rep` and `derivedAssoc_rep` to these complexes.
Naturality moves the scalar computation maps past the inverse-image comparison.
After postcomposing with the inverse-image factorization and the direct scalar
computation map, the proposed composition square becomes the localization of the
ordinary composition square just proved, degree by degree. Those computation maps
are invertible on the chosen complexes, so cancel them. The unit square follows
from the same argument using ordinary multiplication instead of association.
Finally every derived object is isomorphic to its chosen resolution; naturality
transports the two equations across that isomorphism. This uses neither a direct
image projection nor an open extension or a Brown adjoint. Identity quotient maps,
the zero coefficient ring and repeated indices satisfy the same insertion formulas;
no flatness of the quotient homomorphism or boundedness of the input is assumed. -/
theorem strictEtaleInverseTensorCoherence
    {O : Type (u + 1)} [CommRing O] {t : O}
    {V W : Scheme.{u}} (g : V ⟶ W)
    (PW : StrictEtaleEvaluation W O t) (PV : StrictEtaleEvaluation V O t)
    (A : StrictEtaleOrdinaryImage O t g)
    (E : CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
      O t _ _ _ A PW PV) :
    (∀ (n : ℕ) P,
      (E.derivedTensor (Nat.le_refl n)).hom.app P ≫
        (PV.derivedUnit n).hom.app ((E.level n).inverse.obj P) =
      (E.level n).inverse.map ((PW.derivedUnit n).hom.app P)) ∧
    (∀ {r m n : ℕ} (h₁ : m ≤ r) (h₂ : n ≤ m) P,
      (E.level n).inverse.map ((PW.derivedAssoc h₁ h₂).hom.app P) ≫
        (E.derivedTensor (h₂.trans h₁)).hom.app P =
      (E.derivedTensor h₂).hom.app ((PW.scalar h₁).derived.obj P) ≫
        (PV.scalar h₂).derived.map ((E.derivedTensor h₁).hom.app P) ≫
        (PV.derivedAssoc h₁ h₂).hom.app ((E.level r).inverse.obj P)) := by
  let G := MorphismProperty.Over.pullback @Etale ⊤ g
  have hlan : PreservesFiniteLimits
      (G.op.lan : (W.Etaleᵒᵖ ⥤ Type (u + 1)) ⥤ (V.Etaleᵒᵖ ⥤ Type (u + 1))) := by
    apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u + 1}
    intro J _ _
    apply preservesLimitsOfShape_of_evaluation
      (G.op.lan : (W.Etaleᵒᵖ ⥤ Type (u + 1)) ⥤ (V.Etaleᵒᵖ ⥤ Type (u + 1))) J
    intro K
    have : IsFiltered (CostructuredArrow G.op K) :=
      IsFiltered.of_equivalence (structuredArrowOpEquivalence G (Opposite.unop K))
    exact preservesLimitsOfShape_of_natIso (Functor.lanEvaluationIsoColim' G.op K).symm
  let := hlan
  have : PreservesFiniteLimits (Scheme.etaleSetPullback g) :=
    Functor.sheafPullbackConstruction.instPreservesFiniteLimitsSheafSheafPullback
      G (Type (u + 1)) W.smallEtaleTopology V.smallEtaleTopology
  exact generic_coherence PW PV A E

end AlgebraicGeometry

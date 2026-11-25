/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarStages
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTensor
import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarCompletedObjectComplete
import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarCoefficientFiniteFree
import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarRestrictionComplete
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeRestrictionDirectImageMate
import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsComapBiproduct
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategorySquareIsoSymm

/-! # Ambient operation comparisons for finite scalar extension

Existing declarations extracted from `PbcScalarExtension` to bound compilation cost.

## References

* Milne, Section 19
* Stacks Tag 03ER
* Stacks Tags 06YY and 0943
* Stacks Tags 03EK, 06YY, 0D6D and 07A6
* Stacks Tags 03EL, 0D6D, 0D6E and 07A6
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv
namespace AlgebraicGeometry.Scheme
section AmbientOperations

variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarCompletedCoefficientMap_projection {X Y : Scheme.{u}} (g : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    completedCoefficientMap g d ≫ pbcAdicProjection X d n =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map (pbcAdicProjection Y d n) ≫
        completedFiniteCoefficientMap g d n := by
  exact limit.lift_π _ (op n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarFiniteCoefficientMap_naturality {X Y : Scheme.{u}} (g : X ⟶ Y)
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (dA : AdicCoefficientDatum A) (dB : AdicCoefficientDatum B) (n : ℕ)
    (q : (A ⧸ dA.ideal ^ (n + 1)) →+* (B ⧸ dB.ideal ^ (n + 1))) :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (AdicCoefficients.coefficientMap Y q) ≫ completedFiniteCoefficientMap g dB n =
      completedFiniteCoefficientMap g dA n ≫ AdicCoefficients.coefficientMap X q := by
  let L := proEtaleSheafInverseImage g CommRingCat.{u + 1}
  have hinv : AdicCoefficients.coefficientMap Y q ≫
      (pbcLevelConstantComparison Y dB n).inv =
    (pbcLevelConstantComparison Y dA n).inv ≫
      (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map (CommRingCat.ofHom q) := by
    apply (Iso.eq_inv_comp _).2
    rw [← Category.assoc]
    apply (Iso.comp_inv_eq _).2
    exact (scalarLevelConstantComparison_naturality Y dA dB n q).symm
  unfold completedFiniteCoefficientMap
  change L.map _ ≫ L.map _ ≫ _ ≫ _ = _
  rw [← L.map_comp_assoc, hinv, L.map_comp, Category.assoc]
  erw [reassoc_of% (proEtaleConstantInverseImageMap_naturality g (CommRingCat.ofHom q))]
  simp only [Category.assoc]
  rw [scalarLevelConstantComparison_naturality]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual completed coefficient inclusion commutes with the ringed structure map. -/
theorem pbcScalarCoefficientStructureSquare :
    pbcActualCoefficientRingMap Y (pbcScalarCoefficientMap l E F i Y) ≫
        pbcActualStructureMap g (pbcIntegralDatum l F) =
      pbcActualStructureMap g (pbcIntegralDatum l E) ≫
        (proEtaleSheafDirectImage g RingCat.{u + 1}).map
          (pbcActualCoefficientRingMap X (pbcScalarCoefficientMap l E F i X)) := by
  let dE := pbcIntegralDatum l E
  let dF := pbcIntegralDatum l F
  let c (T : Scheme.{u}) := pbcScalarCoefficientMap l E F i T
  let L := proEtaleSheafInverseImage g CommRingCat.{u + 1}
  let R := proEtaleSheafDirectImage g CommRingCat.{u + 1}
  have hc (T : Scheme.{u}) (n : ℕ) :
      c T ≫ pbcAdicProjection T dF n = pbcAdicProjection T dE n ≫
        AdicCoefficients.coefficientMap T (pbcScalarQuotientMap l E F i n) :=
    (pbcScalarCoefficientMap_exists l E F i T).exists.choose_spec n
  have h : L.map (c Y) ≫ completedCoefficientMap g dF =
      completedCoefficientMap g dE ≫ c X := by
    apply limit.hom_ext
    intro n
    change (L.map (c Y) ≫ completedCoefficientMap g dF) ≫
        pbcAdicProjection X dF n.unop =
      (completedCoefficientMap g dE ≫ c X) ≫ pbcAdicProjection X dF n.unop
    simp only [Category.assoc, hc]
    rw [scalarCompletedCoefficientMap_projection]
    rw [← Category.assoc (completedCoefficientMap g dE), scalarCompletedCoefficientMap_projection]
    rw [← L.map_comp_assoc, hc, L.map_comp, Category.assoc]
    simpa only [Category.assoc] using congrArg
      (fun k ↦ L.map (pbcAdicProjection Y dE n.unop) ≫ k)
      (scalarFiniteCoefficientMap_naturality g dE dF n.unop
        (pbcScalarQuotientMap l E F i n.unop))
  have hd : c Y ≫ completedCoefficientDirectImageMap g dF =
      completedCoefficientDirectImageMap g dE ≫ R.map (c X) := by
    unfold completedCoefficientDirectImageMap
    have hn := (proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.naturality (c Y)
    change c Y ≫ (proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app _ =
      (proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app _ ≫ R.map (L.map (c Y)) at hn
    rw [← Category.assoc]
    erw [hn]
    rw [Category.assoc, ← R.map_comp, h, R.map_comp, Category.assoc]
  exact congrArg
    (fun k ↦ (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map k) hd

/-- The ambient ordinary-pullback comparison is the normalized derived tensor comparison. -/
@[irreducible] def pbcScalarOrdinaryPullIso :
    pbcEmbeddingAmbientTensor l E F i Y ⋙
        pbcActualDerivedPull g (pbcIntegralDatum l F) ≅
      pbcActualDerivedPull g (pbcIntegralDatum l E) ⋙
        pbcEmbeddingAmbientTensor l E F i X :=
  pbcActualScalarDerivedPullIso g (pbcIntegralDatum l E) (pbcIntegralDatum l F)
    (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
    (pbcScalarCoefficientStructureSquare l E F i g)

/-- The direct-image comparison is the actual mate, rather than a selected isomorphism. -/
@[irreducible] def pbcScalarDirectImageMap :
    pbcActualDerivedPush g (pbcIntegralDatum l E) ⋙
        pbcEmbeddingAmbientTensor l E F i Y ⟶
      pbcEmbeddingAmbientTensor l E F i X ⋙
        pbcActualDerivedPush g (pbcIntegralDatum l F) :=
  pbcActualScalarDirectImageMap g (pbcIntegralDatum l E) (pbcIntegralDatum l F)
    (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
    (pbcScalarCoefficientStructureSquare l E F i g)

/-- The actual completed coefficient comparison is the canonical profinite comparison. -/
theorem pbcCompletedCoefficientMap_eq {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    completedCoefficientMap g d = (d.integralRingIso g).hom := by
  apply limit.hom_ext
  intro n
  change completedCoefficientMap g d ≫ d.projection X n.unop =
    (d.integralRingIso g).hom ≫ d.projection X n.unop
  calc
    _ = completedCoefficientComponent g d n.unop := limit.lift_π _ n
    _ = _ := by
      rw [d.projection_comm]
      rfl

/-- The completed coefficient comparison as an isomorphism, with the actual forward map. -/
def pbcCompletedCoefficientIso {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (pbcAdicCompletion Y d) ≅
      pbcAdicCompletion X d where
  hom := completedCoefficientMap g d
  inv := (d.integralRingIso g).inv
  hom_inv_id := by
    rw [pbcCompletedCoefficientMap_eq]
    exact (d.integralRingIso g).hom_inv_id
  inv_hom_id := by
    rw [pbcCompletedCoefficientMap_eq]
    exact (d.integralRingIso g).inv_hom_id

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The scalar inclusion commutes with the inverse-image coefficient comparisons. -/
theorem pbcScalarCoefficientInverseSquare :
    (pbcCompletedCoefficientIso g (pbcIntegralDatum l E)).hom ≫
        pbcScalarCoefficientMap l E F i X =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
          (pbcScalarCoefficientMap l E F i Y) ≫
        (pbcCompletedCoefficientIso g (pbcIntegralDatum l F)).hom := by
  let dE := pbcIntegralDatum l E
  let dF := pbcIntegralDatum l F
  let c (T : Scheme.{u}) := pbcScalarCoefficientMap l E F i T
  let L := proEtaleSheafInverseImage g CommRingCat.{u + 1}
  have hc (T : Scheme.{u}) (n : ℕ) :
      c T ≫ pbcAdicProjection T dF n = pbcAdicProjection T dE n ≫
        AdicCoefficients.coefficientMap T (pbcScalarQuotientMap l E F i n) :=
    (pbcScalarCoefficientMap_exists l E F i T).exists.choose_spec n
  change completedCoefficientMap g dE ≫ c X = L.map (c Y) ≫ completedCoefficientMap g dF
  symm
  apply limit.hom_ext
  intro n
  change (L.map (c Y) ≫ completedCoefficientMap g dF) ≫
      pbcAdicProjection X dF n.unop =
    (completedCoefficientMap g dE ≫ c X) ≫ pbcAdicProjection X dF n.unop
  simp only [Category.assoc, hc]
  rw [scalarCompletedCoefficientMap_projection]
  rw [← Category.assoc (completedCoefficientMap g dE), scalarCompletedCoefficientMap_projection]
  rw [← L.map_comp_assoc, hc, L.map_comp, Category.assoc]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ L.map (pbcAdicProjection Y dE n.unop) ≫ k)
    (scalarFiniteCoefficientMap_naturality g dE dF n.unop
      (pbcScalarQuotientMap l E F i n.unop))

/-- The canonical derived restriction/direct-image comparison for the scalar inclusion. -/
abbrev pbcScalarRestrictionDirectImage :=
  proEtaleRingRestrictionDerivedDirectImage g
    (pbcAdicCompletion Y (pbcIntegralDatum l E)) (pbcAdicCompletion Y (pbcIntegralDatum l F))
    (pbcAdicCompletion X (pbcIntegralDatum l E)) (pbcAdicCompletion X (pbcIntegralDatum l F))
    (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
    (pbcCompletedCoefficientIso g (pbcIntegralDatum l E))
    (pbcCompletedCoefficientIso g (pbcIntegralDatum l F))
    (pbcScalarCoefficientInverseSquare l E F i g)

/-- The canonical comparison from termwise pullback to the derived pullback,
obtained by conjugating the identity of the common derived direct image. -/
def pbcPullComparison {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    proEtaleRingDerivedPullback g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
        (pbcCompletedCoefficientIso g d) ⟶ pbcActualDerivedPull g d :=
  (conjugateEquiv (pbcActualDerivedAdjunction g d)
    (proEtaleRingDerivedAdjunction g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
      (pbcCompletedCoefficientIso g d))).symm (𝟙 _)

/-- The canonical termwise restriction/pullback comparison for the scalar inclusion. -/
abbrev pbcScalarRestrictionPullback :=
  proEtaleRingRestrictionDerivedPullback g
    (pbcAdicCompletion Y (pbcIntegralDatum l E)) (pbcAdicCompletion Y (pbcIntegralDatum l F))
    (pbcAdicCompletion X (pbcIntegralDatum l E)) (pbcAdicCompletion X (pbcIntegralDatum l F))
    (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
    (pbcCompletedCoefficientIso g (pbcIntegralDatum l E))
    (pbcCompletedCoefficientIso g (pbcIntegralDatum l F))
    (pbcScalarCoefficientInverseSquare l E F i g)

/-- Flat-term K-flat complexes over the completed coefficients, the resolving class on
which the derived scalar and pullback functors are computed termwise. -/
def PbcFlatKFlat (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := pbcAdicCompletion T d) K ∧
    ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := pbcAdicCompletion T d) (K.X n)

/-- Every complex has a flat-term K-flat resolution. -/
theorem pbcFlatKFlat_resolution (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (K : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :
    ∃ (L : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) (s : L ⟶ K),
      QuasiIso s ∧ PbcFlatKFlat T d L := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_proEtTopology AddCommGrpCat.{u + 1} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
      u + 1, u + 2, u + 1} _
  obtain ⟨L, s, hl, hf, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
      (C := T.ProEt) (J := ProEt.topology T) (R := pbcAdicCompletion T d) K
  refine ⟨L, s, hs, hl, fun n ↦ ?_⟩
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso (pbcAdicCompletion T d) (L.X n)).symm (hf n)

/-- Biproduct powers are exact: they are both `const ⋙ lim` and `const ⋙ colim`. -/
private theorem finBiproductPow_exact {C : Type*} [Category C] [Preadditive C]
    [HasFiniteBiproducts C] (d : ℕ) :
    PreservesFiniteLimits (Functor.finBiproductPow C d) ∧
    PreservesFiniteColimits (Functor.finBiproductPow C d) := by
  let cL (X : C) : Cone ((Functor.const (Discrete (Fin d))).obj X) :=
    ⟨⨁ fun _ : Fin d => X,
      { app := fun j => biproduct.π (fun _ : Fin d => X) j.as
        naturality := by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp }⟩
  let iL (X : C) : (⨁ fun _ : Fin d => X) ≅ limit ((Functor.const (Discrete (Fin d))).obj X) :=
    { hom := limit.lift _ (cL X)
      inv := biproduct.lift fun j => limit.π ((Functor.const (Discrete (Fin d))).obj X) ⟨j⟩
      hom_inv_id := biproduct.hom_ext _ _ fun j => by simp [cL]
      inv_hom_id := limit.hom_ext fun ⟨j⟩ => by simp [cL] }
  let eL : Functor.finBiproductPow C d ≅ (Functor.const (Discrete (Fin d)) : C ⥤ _) ⋙ lim :=
    NatIso.ofComponents iL (by
        intro X Y f
        change (biproduct.map fun _ => f) ≫ limit.lift _ (cL Y) =
          limit.lift _ (cL X) ≫ limMap ((Functor.const (Discrete (Fin d))).map f)
        refine limit.hom_ext fun ⟨j⟩ => ?_
        simp [cL])
  let cC (X : C) : Cocone ((Functor.const (Discrete (Fin d))).obj X) :=
    ⟨⨁ fun _ : Fin d => X,
      { app := fun j => biproduct.ι (fun _ : Fin d => X) j.as
        naturality := by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp }⟩
  let iC (X : C) : (⨁ fun _ : Fin d => X) ≅ colimit ((Functor.const (Discrete (Fin d))).obj X) :=
    { hom := biproduct.desc fun j => colimit.ι ((Functor.const (Discrete (Fin d))).obj X) ⟨j⟩
      inv := colimit.desc _ (cC X)
      hom_inv_id := biproduct.hom_ext' _ _ fun j => by simp [cC]
      inv_hom_id := colimit.hom_ext fun ⟨j⟩ => by simp [cC] }
  let eC : Functor.finBiproductPow C d ≅ (Functor.const (Discrete (Fin d)) : C ⥤ _) ⋙ colim :=
    NatIso.ofComponents iC (by
        intro X Y f
        change (biproduct.map fun _ => f) ≫
            biproduct.desc (fun j => colimit.ι ((Functor.const (Discrete (Fin d))).obj Y) ⟨j⟩) =
          biproduct.desc (fun j => colimit.ι ((Functor.const (Discrete (Fin d))).obj X) ⟨j⟩) ≫
            colimMap ((Functor.const (Discrete (Fin d))).map f)
        refine biproduct.hom_ext' _ _ fun j => ?_
        simp)
  exact ⟨preservesFiniteLimits_of_natIso eL.symm, preservesFiniteColimits_of_natIso eC.symm⟩

open MonoidalCategory in
/-- The completed target integral coefficients are flat over the source ones. -/
theorem pbcScalarCoefficient_flat (T : Scheme.{u}) :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := pbcAdicCompletion T (pbcIntegralDatum l E))
      ((pbcRestrict (pbcScalarCoefficientMap l E F i T)).obj
        (SheafOfModules.unit ((adicLisseForget T).obj
          (pbcAdicCompletion T (pbcIntegralDatum l F))))) := by
  classical
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_proEtTopology AddCommGrpCat.{u + 1} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
      u + 1, u + 2, u + 1} _
  obtain ⟨d, ⟨b⟩⟩ := pbcScalarCoefficient_finiteFree l E F i T
  let R := pbcAdicCompletion T (pbcIntegralDatum l E)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let 𝒜 := SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  have : MonoidalPreadditive 𝒜 := by
    have (M : 𝒜) : (tensorLeft M).Additive := SheafOfModules.tensorLeft_additive_independent R M
    have (M : 𝒜) : (tensorRight M).Additive :=
      Functor.additive_of_iso (F := tensorLeft M) (BraidedCategory.tensorLeftIsoTensorRight M)
    exact
      { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
        zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
        whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
        add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }
  let M : 𝒜 := (pbcRestrict (pbcScalarCoefficientMap l E F i T)).obj
    (SheafOfModules.unit ((adicLisseForget T).obj
      (pbcAdicCompletion T (pbcIntegralDatum l F))))
  have : HasFiniteBiproducts 𝒜 := HasFiniteBiproducts.of_hasFiniteProducts
  let e : M ≅ ⨁ fun _ : Fin d ↦ 𝟙_ 𝒜 := b ≪≫ (biproduct.isoProduct _).symm
  let e₂ : tensorRight M ≅ Functor.finBiproductPow 𝒜 d :=
    (BraidedCategory.tensorLeftIsoTensorRight M).symm ≪≫
      MonoidalCategory.tensorLeftIsoOfIso e ≪≫ MonoidalCategory.tensorLeftBiproductPowUnitIso d
  obtain ⟨h₁, h₂⟩ := finBiproductPow_exact (C := 𝒜) d
  exact (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R M ≪≫ e₂).symm
    ((exactFunctor_iff _).2 ⟨h₁, h₂⟩)

/-- Restriction along the completed scalar inclusion preserves flat-term K-flat complexes. -/
theorem pbcScalarRestrict_flatKFlat (T : Scheme.{u})
    (K : CochainComplex (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l F))) ℤ)
    (hK : PbcFlatKFlat T (pbcIntegralDatum l F) K) :
    PbcFlatKFlat T (pbcIntegralDatum l E)
      (((pbcRestrict (pbcScalarCoefficientMap l E F i T)).mapHomologicalComplex
        (.up ℤ)).obj K) := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  have h := SheafOfModules.isKFlat_restrictScalars_of_flat (pbcScalarCoefficientMap l E F i T)
    (pbcScalarCoefficient_flat l E F i T) K hK.1
  exact ⟨h.1, h.2 hK.2⟩

/-- The termwise pullback is the module pullback. -/
theorem pbcModulePull_eq {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    proEtaleRingModulePullback g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
        (pbcCompletedCoefficientIso g d) = pbcActualModulePull g d := by
  symm
  change completedModulePullback g d = _
  unfold completedModulePullback
  refine CategoryTheory.Functor.ext (fun M ↦
    (completedAdicChangeData X (completedCoefficientMap g d)).choose_spec.choose
      ((proEtaleModuleInverseImage g (pbcAdicCompletion Y d)).obj M)) ?_
  intro M N f
  exact (completedAdicChangeData X (completedCoefficientMap g d)).choose_spec.choose_spec.choose
    ((proEtaleModuleInverseImage g (pbcAdicCompletion Y d)).map f)

/-- The ordinary identification of the two module pullbacks. -/
def pbcModulePullIso {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    proEtaleRingModulePullback g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
        (pbcCompletedCoefficientIso g d) ≅ pbcActualModulePull g d :=
  eqToIso (pbcModulePull_eq g d)

/-- The pullback counit is invertible on K-flat complexes. -/
theorem pbcActualPullComplexCounit_isIso {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (hp : PbcFlatKFlat Y d P) : IsIso (pbcActualPullComplexCounit g d P) := by
  have : IsIso ((pbcActualPullCounit g d).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
    delta pbcActualPullCounit completedOrdinaryPullbackCounit completedOrdinaryPullback
    exact (completedOrdinaryPullback_exists g d).choose_spec.choose_spec.2 P hp.1
  dsimp only [pbcActualPullComplexCounit]
  infer_instance

/-- The ordinary scalar mate of the inverse ordinary pullback comparison. -/
def pbcScalarOrdinaryRestrictionPull :
    pbcRestrict (pbcScalarCoefficientMap l E F i Y) ⋙ pbcActualModulePull g (pbcIntegralDatum l E) ⟶
      pbcActualModulePull g (pbcIntegralDatum l F) ⋙
        pbcRestrict (pbcScalarCoefficientMap l E F i X) :=
  (mateEquiv (pbcScalarAdjunction (pbcScalarCoefficientMap l E F i Y))
    (pbcScalarAdjunction (pbcScalarCoefficientMap l E F i X))
    (TwoSquare.mk _ _ _ _ (pbcActualScalarOrdinaryPullIso g (pbcIntegralDatum l E)
      (pbcIntegralDatum l F) (pbcScalarCoefficientMap l E F i Y)
      (pbcScalarCoefficientMap l E F i X)
      (pbcScalarCoefficientStructureSquare l E F i g)).inv))

/-- Transport of an iterated mate along an equality of left adjoints with compatible units. -/
private theorem iteratedMate_transport {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂]
    [Category D₁] [Category D₂]
    {ExtY : C₁ ⥤ C₂} {ResY : C₂ ⥤ C₁} (aY : ExtY ⊣ ResY)
    {ExtX : D₁ ⥤ D₂} {ResX : D₂ ⥤ D₁} (aX : ExtX ⊣ ResX)
    {LE LE' : C₁ ⥤ D₁} {PE : D₁ ⥤ C₁} (adjE : LE ⊣ PE) (adjE' : LE' ⊣ PE) (hE : LE' = LE)
    (huE : ∀ M, adjE'.unit.app M ≫ PE.map ((eqToHom hE).app M) = adjE.unit.app M)
    {LF LF' : C₂ ⥤ D₂} {PF : D₂ ⥤ C₂} (adjF : LF ⊣ PF) (adjF' : LF' ⊣ PF) (hF : LF' = LF)
    (huF : ∀ M, adjF'.unit.app M ≫ PF.map ((eqToHom hF).app M) = adjF.unit.app M)
    (δ : PF ⋙ ResY ⟶ ResX ⋙ PE) :
    whiskerLeft ResY (eqToHom hE) ≫ (mateEquiv aY aX (TwoSquare.mk _ _ _ _
        ((conjugateEquiv (aY.comp adjF) (adjE.comp aX)).symm δ))) =
      ((mateEquiv adjF' adjE').symm (TwoSquare.mk _ _ _ _ δ)) ≫
        whiskerRight (eqToHom hF) ResX := by
  subst hE hF
  obtain rfl : adjE' = adjE := Adjunction.ext (by ext M; simpa using huE M)
  obtain rfl : adjF' = adjF := Adjunction.ext (by ext M; simpa using huF M)
  simp only [eqToHom_refl, Functor.whiskerLeft_id', Functor.whiskerRight_id', Category.id_comp,
    Category.comp_id]
  have h := iterated_mateEquiv_conjugateEquiv aY aX adjE' adjF'
    (TwoSquare.mk _ _ _ _ ((conjugateEquiv (aY.comp adjF') (adjE'.comp aX)).symm δ))
  have h' : mateEquiv adjF' adjE' (mateEquiv aY aX
      (TwoSquare.mk _ _ _ _ ((conjugateEquiv (aY.comp adjF') (adjE'.comp aX)).symm δ))) =
      TwoSquare.mk _ _ _ _ δ :=
    h.trans (Equiv.apply_symm_apply (conjugateEquiv (aY.comp adjF') (adjE'.comp aX)) δ)
  exact ((Equiv.eq_symm_apply _).2 h')

/-- The ring-module and module adjunctions have compatible units. -/
private theorem pbcModuleAdjunction_unit_compat {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (M : pbcModules Y (pbcAdicCompletion Y d)) :
    (proEtaleRingModuleAdjunction g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
        (pbcCompletedCoefficientIso g d)).unit.app M ≫
      (pbcActualModulePush g d).map ((eqToHom (pbcModulePull_eq g d)).app M) =
      (pbcActualModuleAdjunction g d).unit.app M := by
  obtain ⟨k, hk, he⟩ := (Classical.choose_spec (proEtaleRingModuleAdjunction_existsUnique g
    (pbcAdicCompletion Y d) (pbcAdicCompletion X d) (pbcCompletedCoefficientIso g d))).1 M _ (𝟙 _)
  rw [Adjunction.homEquiv_id] at he
  have h2 := (pbcActualModuleAdjunction_exists g d).exists.choose_spec M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  have h1 := (he U x).trans (hk (Opposite.op (AsSmall.up.obj ((proEtaleBaseChange g).obj U.unop)))
    _)
  change _ = ((pbcActualModuleAdjunction g d).unit.app M).val.app U x
  refine Eq.trans ?_ (h2 U.unop x).symm
  change ((pbcActualModulePush g d).map ((eqToHom (pbcModulePull_eq g d)).app M)).val.app U
    (((proEtaleRingModuleAdjunction g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
        (pbcCompletedCoefficientIso g d)).unit.app M).val.app U x) = _
  refine (congrArg (fun z ↦ ((pbcActualModulePush g d).map
    ((eqToHom (pbcModulePull_eq g d)).app M)).val.app U z) h1).trans ?_
  rw [eqToHom_app]
  rfl

/-- Conjugating the identity between two derived adjunctions whose units are the localized
units of two equal ordinary left adjoints with compatible units gives the localized
termwise identification. -/
private theorem derivedConjugate_transport {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    [Abelian C₁] [Abelian C₂] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    {G G' : C₁ ⥤ C₂} {F : C₂ ⥤ C₁} [G.Additive] [G'.Additive] [F.Additive]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (adj : G ⊣ F) (adj' : G' ⊣ F) (h : G' = G)
    (hu : ∀ M, adj'.unit.app M ≫ F.map ((eqToHom h).app M) = adj.unit.app M)
    {LA : DerivedCategory C₁ ⥤ DerivedCategory C₂} {FD : DerivedCategory C₂ ⥤ DerivedCategory C₁}
    (adjD : LA ⊣ FD) (adjD' : G'.mapDerivedCategory ⊣ FD)
    (αA : DerivedCategory.Qh ⋙ LA ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (β : F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ FD)
    (hη : ∀ X, adjD.unit.app (DerivedCategory.Qh.obj X) ≫ FD.map (αA.app X) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app X) ≫
        β.app ((G.mapHomotopyCategory (.up ℤ)).obj X))
    (hη' : ∀ X, adjD'.unit.app (DerivedCategory.Qh.obj X) ≫
        FD.map (G'.mapDerivedCategoryFactorsh.hom.app X) =
      DerivedCategory.Qh.map ((adj'.mapHomotopyCategory (.up ℤ)).unit.app X) ≫
        β.app ((G'.mapHomotopyCategory (.up ℤ)).obj X))
    (P : CochainComplex C₁ ℤ) :
    ((conjugateEquiv adjD adjD').symm (𝟙 _)).app (DerivedCategory.Q.obj P) ≫
        (LA.map ((DerivedCategory.quotientCompQhIso C₁).inv.app P) ≫
          αA.app ((HomotopyCategory.quotient _ _).obj P) ≫
          DerivedCategory.Qh.map ((G.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
          (DerivedCategory.quotientCompQhIso C₂).hom.app _) =
      G'.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (eqToHom h) (.up ℤ)).app P) := by
  subst h
  obtain rfl : adj' = adj := Adjunction.ext (by ext M; simpa using hu M)
  set cmp := (conjugateEquiv adjD adjD').symm (𝟙 _)
  have hcmp (X : HomotopyCategory C₁ (.up ℤ)) :
      cmp.app (DerivedCategory.Qh.obj X) ≫ αA.app X =
        G'.mapDerivedCategoryFactorsh.hom.app X := by
    apply (adjD'.homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit, Functor.map_comp]
    rw [← Category.assoc, ← unit_conjugateEquiv_symm]
    refine Eq.trans ?_ ((hη X).trans (hη' X).symm)
    exact congrArg (· ≫ FD.map (αA.app X)) (Category.comp_id _)
  rw [← NatTrans.naturality_assoc]
  erw [reassoc_of% hcmp ((HomotopyCategory.quotient _ _).obj P)]
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  simp only [Category.assoc, eqToHom_refl, NatTrans.mapHomologicalComplex_id, NatTrans.id_app,
    CategoryTheory.Functor.map_id]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact congrArg (_ ≫ ·) ((DerivedCategory.quotientCompQhIso C₂).inv_hom_id_app _)

set_option linter.unusedVariables false in
/-- The canonical pullback comparison is the localized termwise identification on
flat-term K-flat complexes. -/
theorem pbcPullComparison_app {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (hp : PbcFlatKFlat Y d P) :
    (pbcPullComparison g d).app (DerivedCategory.Q.obj P) ≫
        pbcActualPullComplexCounit g d P =
      (proEtaleRingModulePullback g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
          (pbcCompletedCoefficientIso g d)).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (pbcModulePullIso g d).hom (.up ℤ)).app P) := by
  dsimp only [pbcPullComparison, pbcActualPullComplexCounit, pbcModulePullIso, eqToIso.hom]
  exact derivedConjugate_transport (pbcActualModuleAdjunction g d)
    (proEtaleRingModuleAdjunction g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
      (pbcCompletedCoefficientIso g d)) (pbcModulePull_eq g d)
    (pbcModuleAdjunction_unit_compat g d) (pbcActualDerivedAdjunction g d)
    (proEtaleRingDerivedAdjunction g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
      (pbcCompletedCoefficientIso g d)) (pbcActualPullCounit g d) (pbcActualPushUnit g d)
    (fun X ↦ Adjunction.derivedη_fac_app _ (HomotopyCategory.quasiIso _ _) _ _ X)
    (fun X ↦ Adjunction.derivedη_fac_app _ (HomotopyCategory.quasiIso _ _) _ _ X) P

/-- The ordinary scalar mate is the identity-on-sections restriction/pullback comparison. -/
theorem pbcScalarOrdinaryRestrictionPull_eq :
    whiskerLeft (pbcRestrict (pbcScalarCoefficientMap l E F i Y))
        (pbcModulePullIso g (pbcIntegralDatum l E)).hom ≫
      pbcScalarOrdinaryRestrictionPull l E F i g =
    proEtaleRingRestrictionPullbackInv g
        (pbcAdicCompletion Y (pbcIntegralDatum l E)) (pbcAdicCompletion Y (pbcIntegralDatum l F))
        (pbcAdicCompletion X (pbcIntegralDatum l E)) (pbcAdicCompletion X (pbcIntegralDatum l F))
        (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
        (pbcCompletedCoefficientIso g (pbcIntegralDatum l E))
        (pbcCompletedCoefficientIso g (pbcIntegralDatum l F))
        (pbcScalarCoefficientInverseSquare l E F i g) ≫
      whiskerRight (pbcModulePullIso g (pbcIntegralDatum l F)).hom
        (pbcRestrict (pbcScalarCoefficientMap l E F i X)) := by
  let φY := pbcScalarCoefficientMap l E F i Y
  let φX := pbcScalarCoefficientMap l E F i X
  let dE := pbcIntegralDatum l E
  let dF := pbcIntegralDatum l F
  let hφ := pbcScalarCoefficientStructureSquare l E F i g
  let δ := pbcActualScalarRightIso g dE dF φY φX hφ
  let adjS := proEtaleRingModuleAdjunction g (pbcAdicCompletion Y dF) (pbcAdicCompletion X dF)
    (pbcCompletedCoefficientIso g dF)
  let adjR := proEtaleRingModuleAdjunction g (pbcAdicCompletion Y dE) (pbcAdicCompletion X dE)
    (pbcCompletedCoefficientIso g dE)
  let dd := proEtaleRingRestrictionDirectImage g
    (pbcAdicCompletion Y dE) (pbcAdicCompletion Y dF)
    (pbcAdicCompletion X dE) (pbcAdicCompletion X dF) φY φX
    (pbcCompletedCoefficientIso g dE) (pbcCompletedCoefficientIso g dF)
    (pbcScalarCoefficientInverseSquare l E F i g)
  have hdd : dd.hom = δ.hom := by
    ext N W n
    exact ((Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique g
      (pbcAdicCompletion Y dE) (pbcAdicCompletion Y dF)
      (pbcAdicCompletion X dE) (pbcAdicCompletion X dF) φY φX
      (pbcCompletedCoefficientIso g dE) (pbcCompletedCoefficientIso g dF)
      (pbcScalarCoefficientInverseSquare l E F i g))).1 N W n).trans
      ((pbcActualScalarRightIso_exists g dE dF φY φX hφ).exists.choose_spec N W n).symm
  have hinv : proEtaleRingRestrictionPullbackInv g
      (pbcAdicCompletion Y dE) (pbcAdicCompletion Y dF)
      (pbcAdicCompletion X dE) (pbcAdicCompletion X dF) φY φX
      (pbcCompletedCoefficientIso g dE) (pbcCompletedCoefficientIso g dF)
      (pbcScalarCoefficientInverseSquare l E F i g) =
      ((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ dd.hom)) := by
    apply NatTrans.ext
    funext M
    let s := (mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ dd.hom)
    change proEtaleRingRestrictionPullbackApp g
      (pbcAdicCompletion Y dE) (pbcAdicCompletion Y dF)
      (pbcAdicCompletion X dE) (pbcAdicCompletion X dF) φY φX
      (pbcCompletedCoefficientIso g dE) (pbcCompletedCoefficientIso g dF)
      (pbcScalarCoefficientInverseSquare l E F i g) M = s.app M
    symm
    simp only [s, mateEquiv_symm_apply, TwoSquare.mk, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
      Category.id_comp]
    dsimp only [Functor.comp_map]
    try simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    unfold proEtaleRingRestrictionPullbackApp
    rfl
  rw [hinv, hdd]
  simp only [pbcModulePullIso, eqToIso.hom]
  exact iteratedMate_transport (pbcScalarAdjunction φY) (pbcScalarAdjunction φX)
    (pbcActualModuleAdjunction g dE) adjR (pbcModulePull_eq g dE)
    (pbcModuleAdjunction_unit_compat g dE)
    (pbcActualModuleAdjunction g dF) adjS (pbcModulePull_eq g dF)
    (pbcModuleAdjunction_unit_compat g dF) δ.hom

-- Counit of a derived adjunction from its unit normalization on a representative.
private theorem counit_of_unit {C₁ C₂ : Type*} [Category C₁] [Category C₂] {L : C₁ ⥤ C₂}
    {R : C₂ ⥤ C₁} (adj : L ⊣ R) {k : C₂} {p : C₁} {q : C₂} {rq : C₁} (f : R.obj k ⟶ p)
    (hf : IsIso f) (c : L.obj p ⟶ q) (fq : R.obj q ⟶ rq) (u : p ⟶ rq) (ε : q ⟶ k) (r : rq ⟶ p)
    (hu : adj.unit.app p ≫ R.map c ≫ fq = u) (hn : R.map ε ≫ f = fq ≫ r) (ht : u ≫ r = 𝟙 _) :
    adj.counit.app k = L.map f ≫ c ≫ ε := by
  have := hf
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.right_triangle_components]
  simp only [Functor.map_comp]
  rw [adj.unit_naturality_assoc]
  have h2 : R.map ε = fq ≫ r ≫ inv f := by
    rw [← reassoc_of% hn]; simp
  rw [h2, reassoc_of% hu, reassoc_of% ht]; simp

-- The diagram chase computing a mate from normalized units, counits and comparisons.
private theorem scalarPullMate_generic {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂]
    [Category D₁] [Category D₂]
    {EY : C₁ ⥤ C₂} {RY : C₂ ⥤ C₁} (adjY : EY ⊣ RY)
    {EX : D₁ ⥤ D₂} {RX : D₂ ⥤ D₁} (adjX : EX ⊣ RX)
    {LA : C₁ ⥤ D₁} {LB : C₂ ⥤ D₂} (e : EY ⋙ LB ≅ LA ⋙ EX)
    {k : C₂} {p : C₁} {q : C₂} {m : D₁} {n : D₂} {s t : D₂} {z rn : D₁}
    (f : RY.obj k ⟶ p) (cY : EY.obj p ⟶ q) (ε : q ⟶ k)
    (hcounit : adjY.counit.app k = EY.map f ≫ cY ≫ ε)
    (cA : LA.obj p ⟶ m) (cBk : LB.obj k ⟶ t) (cBq : LB.obj q ⟶ s) (Pε : s ⟶ t)
    (hnatB : LB.map ε ≫ cBk = cBq ≫ Pε)
    (cX : EX.obj m ⟶ n) (oh : s ⟶ n) (oi : n ⟶ s) (hoi : oh ≫ oi = 𝟙 _)
    (he : e.hom.app p ≫ EX.map cA ≫ cX = LB.map cY ≫ cBq ≫ oh)
    (fXt : RX.obj t ⟶ z) (fXn : RX.obj n ⟶ rn) (ηM : m ⟶ rn)
    (hu : adjX.unit.app m ≫ RX.map cX ≫ fXn = ηM)
    (R' : rn ⟶ z) (hfac : RX.map oi ≫ RX.map Pε ≫ fXt = fXn ≫ R')
    (om : m ⟶ z) (hmate : ηM ≫ R' = om) :
    LA.map f ≫ cA ≫ om =
      (mateEquiv adjY adjX (TwoSquare.mk _ _ _ _ e.inv)).app k ≫ RX.map cBk ≫ fXt := by
  have he' : e.inv.app p ≫ LB.map cY ≫ cBq = EX.map cA ≫ cX ≫ oi := by
    rw [← cancel_epi (e.hom.app p), Iso.hom_inv_id_app_assoc, reassoc_of% he, hoi]
    simp
  have hm : (mateEquiv adjY adjX (TwoSquare.mk _ _ _ _ e.inv)).app k =
      adjX.unit.app _ ≫ RX.map (e.inv.app _) ≫ RX.map (LB.map (adjY.counit.app k)) := by
    simp [mateEquiv]
  have huX {a b : D₁} (g : a ⟶ b) : adjX.unit.app a ≫ RX.map (EX.map g) = g ≫ adjX.unit.app b :=
    (adjX.unit.naturality g).symm
  rw [hm, hcounit]
  simp only [Functor.map_comp, Category.assoc]
  have hn : e.inv.app _ ≫ LB.map (EY.map f) = EX.map (LA.map f) ≫ e.inv.app p :=
    (e.inv.naturality f).symm
  rw [← RX.map_comp_assoc (e.inv.app _), hn, RX.map_comp_assoc, reassoc_of% (huX (LA.map f))]
  rw [← RX.map_comp_assoc, ← RX.map_comp_assoc, ← RX.map_comp_assoc, Category.assoc,
    Category.assoc, hnatB, reassoc_of% he']
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (huX cA), hfac, reassoc_of% hu, hmate]

-- Naturality of a universal derived counit written on cochain representatives.
private theorem complexCounit_naturality {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (LF : DerivedCategory C ⥤ DerivedCategory D)
    (eps : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    {K L : CochainComplex C ℤ} (a : K ⟶ L) :
    LF.map (DerivedCategory.Q.map a) ≫
      (LF.map ((DerivedCategory.quotientCompQhIso C).inv.app L) ≫
        eps.app ((HomotopyCategory.quotient _ _).obj L) ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app L) ≫
        (DerivedCategory.quotientCompQhIso D).hom.app ((F.mapHomologicalComplex (.up ℤ)).obj L)) =
      (LF.map ((DerivedCategory.quotientCompQhIso C).inv.app K) ≫
        eps.app ((HomotopyCategory.quotient _ _).obj K) ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app K) ≫
        (DerivedCategory.quotientCompQhIso D).hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a) :=
  (whiskerRight (DerivedCategory.quotientCompQhIso C).inv LF ≫
    whiskerLeft (HomotopyCategory.quotient C (.up ℤ)) eps ≫
    whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
    whiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso D).hom).naturality a

-- Two naturality squares of the derived-functor factorization.
private theorem mapDerivedCategoryFactors_two {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L N : CochainComplex C ℤ} (a : K ⟶ L) (b : L ⟶ N) :
    F.mapDerivedCategory.map (DerivedCategory.Q.map a) ≫
      F.mapDerivedCategory.map (DerivedCategory.Q.map b) ≫ F.mapDerivedCategoryFactors.hom.app N =
    F.mapDerivedCategoryFactors.hom.app K ≫
      (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a) ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map b)) := by
  rw [F.mapDerivedCategoryFactors_hom_naturality, F.mapDerivedCategoryFactors_hom_naturality_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The pullback preserves flat-term K-flat complexes.
private theorem pbcPull_flatKFlat {A : Type (u + 1)} [CommRing A] (dA : AdicCoefficientDatum A)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y dA)) ℤ) (hp : PbcFlatKFlat Y dA P) :
    PbcFlatKFlat X dA (((pbcActualModulePull g dA).mapHomologicalComplex (.up ℤ)).obj P) := by
  obtain ⟨I, hI⟩ := proEtaleAlgebraicInverseImage_exists g (pbcAdicCompletion Y dA)
  have : PreservesFiniteLimits (proEtaleSheafInverseImage g (Type (u + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage g (𝟙 Y)).2.2.2.1
  have : (I.modules ⋙ reductionChange X (completedCoefficientMap g dA)).Additive := by
    rw [hI]
    exact completedModulePullback_additive g dA
  have ho := (reductionChangeExistence X (completedCoefficientMap g dA)).choose_spec.choose
  have hpres := SheafOfModules.isKFlat_ringedToposPullback
    (proEtaleSheafInverseImage g (Type (u + 1)))
    (proEtaleSheafDirectImage g (Type (u + 1)))
    (proEtaleSheafAdjunction g (Type (u + 1))) I (completedCoefficientMap g dA)
    (I.modules ⋙ reductionChange X (completedCoefficientMap g dA))
    (fun M ↦ ho (I.modules.obj M))
    (fun a ↦
      (reductionChangeExistence X (completedCoefficientMap g dA)).choose_spec.choose_spec.choose
        (I.modules.map a)) P hp.1 hp.2
  simpa only [hI, pbcActualModulePull, completedModulePullback, PbcFlatKFlat] using hpres

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The derived scalar mate is the localized ordinary scalar mate on flat-term K-flat
complexes with flat-term K-flat restriction. -/
theorem pbcScalarPullMate_app
    (K : CochainComplex (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l F))) ℤ)
    (hK : PbcFlatKFlat Y (pbcIntegralDatum l F) K)
    (hR : PbcFlatKFlat Y (pbcIntegralDatum l E)
      (((pbcRestrict (pbcScalarCoefficientMap l E F i Y)).mapHomologicalComplex (.up ℤ)).obj K)) :
    (pbcActualDerivedPull g (pbcIntegralDatum l E)).map
        ((pbcRestrict (pbcScalarCoefficientMap l E F i Y)).mapDerivedCategoryFactors.hom.app K) ≫
      pbcActualPullComplexCounit g (pbcIntegralDatum l E)
        (((pbcRestrict (pbcScalarCoefficientMap l E F i Y)).mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (pbcScalarOrdinaryRestrictionPull l E F i g) (.up ℤ)).app K) =
    (mateEquiv (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y))
        (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X))
        (TwoSquare.mk _ _ _ _ (pbcScalarOrdinaryPullIso l E F i g).inv)).app
          (DerivedCategory.Q.obj K) ≫
      (pbcDerivedRestrict (pbcScalarCoefficientMap l E F i X)).map
        (pbcActualPullComplexCounit g (pbcIntegralDatum l F) K) ≫
      (pbcRestrict (pbcScalarCoefficientMap l E F i X)).mapDerivedCategoryFactors.hom.app
        (((pbcActualModulePull g (pbcIntegralDatum l F)).mapHomologicalComplex (.up ℤ)).obj K) := by
  let φY := pbcScalarCoefficientMap l E F i Y
  let φX := pbcScalarCoefficientMap l E F i X
  let P := ((pbcRestrict φY).mapHomologicalComplex (.up ℤ)).obj K
  let M := ((pbcActualModulePull g (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ)).obj P
  let εK : ((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P ⟶ K :=
    (NatTrans.mapHomologicalComplex (pbcScalarAdjunction φY).counit (.up ℤ)).app K
  let cI := pbcActualScalarOrdinaryPullComplexIso g (pbcIntegralDatum l E) (pbcIntegralDatum l F)
    φY φX (pbcScalarCoefficientStructureSquare l E F i g)
  have hM : PbcFlatKFlat X (pbcIntegralDatum l E) M := pbcPull_flatKFlat g _ P hR
  have ht : (NatTrans.mapHomologicalComplex (pbcScalarAdjunction φY).unit (.up ℤ)).app P ≫
      ((pbcRestrict φY).mapHomologicalComplex (.up ℤ)).map εK = 𝟙 P := by
    apply HomologicalComplex.hom_ext
    intro n
    exact (pbcScalarAdjunction φY).right_triangle_components (K.X n)
  have hcounit := counit_of_unit (pbcDerivedScalarAdjunction φY)
    ((pbcRestrict φY).mapDerivedCategoryFactors.hom.app K)
    ((pbcRestrict φY).mapDerivedCategoryFactors.app K).isIso_hom (pbcComplexCounit φY P)
    ((pbcRestrict φY).mapDerivedCategoryFactors.hom.app
      (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P))
    (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction φY).unit (.up ℤ)).app P))
    (DerivedCategory.Q.map εK)
    (DerivedCategory.Q.map (((pbcRestrict φY).mapHomologicalComplex (.up ℤ)).map εK))
    ((pbcDerivedScalarAdjunction_exists φY).exists.choose_spec P hR.1)
    ((pbcRestrict φY).mapDerivedCategoryFactors_hom_naturality εK)
    ((DerivedCategory.Q.map_comp _ _).symm.trans
      ((congrArg DerivedCategory.Q.map ht).trans (DerivedCategory.Q.map_id _)))
  have he : (pbcScalarOrdinaryPullIso l E F i g).hom.app (DerivedCategory.Q.obj P) ≫
      (pbcDerivedExtend φX).map (pbcActualPullComplexCounit g (pbcIntegralDatum l E) P) ≫
      pbcComplexCounit φX M =
      (pbcActualDerivedPull g (pbcIntegralDatum l F)).map (pbcComplexCounit φY P) ≫
        pbcActualPullComplexCounit g (pbcIntegralDatum l F)
          (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (cI.hom.app P) := by
    unfold pbcScalarOrdinaryPullIso
    exact (pbcActualScalarDerivedPullIso_exists g _ _ φY φX _).exists.choose_spec P hR.1 hR.2
  have hoi : DerivedCategory.Q.map (cI.hom.app P) ≫ DerivedCategory.Q.map (cI.inv.app P) = 𝟙 _ := by
    rw [← DerivedCategory.Q.map_comp, Iso.hom_inv_id_app, DerivedCategory.Q.map_id]
  have hmate : (NatTrans.mapHomologicalComplex (pbcScalarAdjunction φX).unit (.up ℤ)).app M ≫
      ((pbcRestrict φX).mapHomologicalComplex (.up ℤ)).map (cI.inv.app P) ≫
      ((pbcRestrict φX).mapHomologicalComplex (.up ℤ)).map
        (((pbcActualModulePull g (pbcIntegralDatum l F)).mapHomologicalComplex (.up ℤ)).map εK) =
      (NatTrans.mapHomologicalComplex (pbcScalarOrdinaryRestrictionPull l E F i g)
        (.up ℤ)).app K := by
    apply HomologicalComplex.hom_ext
    intro n
    simp only [comp_obj, HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      mapHomologicalComplex_map_f]
    rfl
  exact scalarPullMate_generic (pbcDerivedScalarAdjunction φY) (pbcDerivedScalarAdjunction φX)
    (pbcScalarOrdinaryPullIso l E F i g) _ (pbcComplexCounit φY P) (DerivedCategory.Q.map εK)
    hcounit (pbcActualPullComplexCounit g (pbcIntegralDatum l E) P)
    (pbcActualPullComplexCounit g (pbcIntegralDatum l F) K)
    (pbcActualPullComplexCounit g (pbcIntegralDatum l F) _)
    (DerivedCategory.Q.map
      (((pbcActualModulePull g (pbcIntegralDatum l F)).mapHomologicalComplex (.up ℤ)).map εK))
    (complexCounit_naturality _ _ _ εK) (pbcComplexCounit φX M) _ _ hoi he _ _ _
    ((pbcDerivedScalarAdjunction_exists φX).exists.choose_spec M hM.1) _
    (mapDerivedCategoryFactors_two (pbcRestrict φX) (cI.inv.app P) _) _
    (by rw [← hmate]; exact ((DerivedCategory.Q.map_comp _ _).trans
      (congrArg (_ ≫ ·) (DerivedCategory.Q.map_comp _ _))).symm)

-- The factorization chase for the termwise restriction/pullback comparison.
private theorem scalarRestrictionPullback_chase {C : Type*} [Category C]
    {O1 O2 O3 O4 O5 O6 O7 O8 : C}
    (ci : O1 ⟶ O2) (ch : O2 ⟶ O1) (bi : O2 ⟶ O3) (bh : O3 ⟶ O2) (ah : O3 ⟶ O4)
    (φF : O4 ⟶ O5) (fX : O5 ⟶ O6) (ma : O6 ⟶ O6) (Ffac : O3 ⟶ O6) (fy : O1 ⟶ O7)
    (φE : O7 ⟶ O8) (mc : O8 ⟶ O8) (Gfac : O2 ⟶ O8) (qe : O6 ⟶ O8) (qp : O8 ⟶ O6)
    (hci : ci ≫ ch = 𝟙 _) (hb : bi ≫ bh = 𝟙 _) (hA : ah ≫ φF ≫ fX ≫ ma = Ffac)
    (hma : ma = 𝟙 _) (hC : ch ≫ fy ≫ φE ≫ mc = Gfac) (hmc : mc = 𝟙 _)
    (hB : bh ≫ Gfac = Ffac ≫ qe) (hq : qe ≫ qp = 𝟙 _) :
    ((ci ≫ bi) ≫ ah) ≫ φF ≫ fX = fy ≫ φE ≫ qp := by
  subst hma hmc
  simp only [Category.comp_id] at hA hC
  calc ((ci ≫ bi) ≫ ah) ≫ φF ≫ fX = ci ≫ bi ≫ Ffac := by
        rw [← hA]; simp only [Category.assoc]
    _ = ci ≫ bi ≫ Ffac ≫ qe ≫ qp := by rw [hq, Category.comp_id]
    _ = ci ≫ bi ≫ bh ≫ Gfac ≫ qp := by rw [← Category.assoc Ffac, ← hB, Category.assoc]
    _ = ci ≫ Gfac ≫ qp := by rw [← Category.assoc bi, hb, Category.id_comp]
    _ = ci ≫ ch ≫ fy ≫ φE ≫ qp := by rw [← hC]; simp only [Category.assoc]
    _ = fy ≫ φE ≫ qp := by rw [← Category.assoc ci, hci, Category.id_comp]

/-- The termwise restriction/pullback comparison is the localized ordinary comparison. -/
theorem pbcScalarRestrictionPullback_app
    (K : CochainComplex (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l F))) ℤ) :
    (pbcScalarRestrictionPullback l E F i g).inv.app (DerivedCategory.Q.obj K) ≫
        (pbcDerivedRestrict (pbcScalarCoefficientMap l E F i X)).map
          ((proEtaleRingModulePullback g (pbcAdicCompletion Y (pbcIntegralDatum l F))
            (pbcAdicCompletion X (pbcIntegralDatum l F))
            (pbcCompletedCoefficientIso g (pbcIntegralDatum l F))).mapDerivedCategoryFactors.hom.app
              K) ≫
        (pbcRestrict (pbcScalarCoefficientMap l E F i X)).mapDerivedCategoryFactors.hom.app
          (((proEtaleRingModulePullback g (pbcAdicCompletion Y (pbcIntegralDatum l F))
            (pbcAdicCompletion X (pbcIntegralDatum l F))
            (pbcCompletedCoefficientIso g (pbcIntegralDatum l F))).mapHomologicalComplex
              (.up ℤ)).obj K) =
      (proEtaleRingDerivedPullback g (pbcAdicCompletion Y (pbcIntegralDatum l E))
          (pbcAdicCompletion X (pbcIntegralDatum l E))
          (pbcCompletedCoefficientIso g (pbcIntegralDatum l E))).map
          ((pbcRestrict (pbcScalarCoefficientMap l E F i Y)).mapDerivedCategoryFactors.hom.app K) ≫
        (proEtaleRingModulePullback g (pbcAdicCompletion Y (pbcIntegralDatum l E))
          (pbcAdicCompletion X (pbcIntegralDatum l E))
          (pbcCompletedCoefficientIso g (pbcIntegralDatum l E))).mapDerivedCategoryFactors.hom.app
            (((pbcRestrict (pbcScalarCoefficientMap l E F i Y)).mapHomologicalComplex
              (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (proEtaleRingRestrictionPullbackInv g
            (pbcAdicCompletion Y (pbcIntegralDatum l E))
            (pbcAdicCompletion Y (pbcIntegralDatum l F))
            (pbcAdicCompletion X (pbcIntegralDatum l E))
            (pbcAdicCompletion X (pbcIntegralDatum l F))
            (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
            (pbcCompletedCoefficientIso g (pbcIntegralDatum l E))
            (pbcCompletedCoefficientIso g (pbcIntegralDatum l F))
            (pbcScalarCoefficientInverseSquare l E F i g)) (.up ℤ)).app K) := by
  let dE := pbcIntegralDatum l E
  let dF := pbcIntegralDatum l F
  let pb := proEtaleRingRestrictionPullbackInv g
    (pbcAdicCompletion Y dE) (pbcAdicCompletion Y dF) (pbcAdicCompletion X dE)
    (pbcAdicCompletion X dF) (pbcScalarCoefficientMap l E F i Y)
    (pbcScalarCoefficientMap l E F i X) (pbcCompletedCoefficientIso g dE)
    (pbcCompletedCoefficientIso g dF) (pbcScalarCoefficientInverseSquare l E F i g)
  have := proEtaleRingRestrictionPullbackInv_isIso g
    (pbcAdicCompletion Y dE) (pbcAdicCompletion Y dF) (pbcAdicCompletion X dE)
    (pbcAdicCompletion X dF) (pbcScalarCoefficientMap l E F i Y)
    (pbcScalarCoefficientMap l E F i X) (pbcCompletedCoefficientIso g dE)
    (pbcCompletedCoefficientIso g dF) (pbcScalarCoefficientInverseSquare l E F i g)
  change (Functor.mapDerivedCategorySquareIso (asIso pb).symm).inv.app
    (DerivedCategory.Q.obj K) ≫ _ = _
  rw [Functor.mapDerivedCategorySquareIso_symm]
  exact Functor.exactSquare_fac (asIso pb) K

-- The final diagram chase, over an abstract category.
private theorem scalarPullMate_chase {C : Type*} [Category C]
    {O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 O12 : C}
    (a : O1 ⟶ O2) (t : O2 ⟶ O3) (r : O1 ⟶ O4) (b : O4 ⟶ O3)
    (fy1 : O1 ⟶ O6) (fy2 : O2 ⟶ O7) (eEP : O6 ⟶ O7) (cPE : O7 ⟶ O8)
    (ΦE : O6 ⟶ O9) (ιE : O9 ⟶ O8) (θ0 : O8 ⟶ O5) (pb : O9 ⟶ O10) (rι : O10 ⟶ O5)
    (ΦF : O4 ⟶ O11) (fXh2 : O11 ⟶ O10) (ιF : O11 ⟶ O12) (fXh1 : O12 ⟶ O5)
    (cPF : O3 ⟶ O12) (hZ : Mono (cPF ≫ fXh1))
    (hΘ : fy2 ≫ cPE ≫ θ0 = t ≫ cPF ≫ fXh1)
    (hn : fy1 ≫ eEP = a ≫ fy2)
    (hE : eEP ≫ cPE = ΦE ≫ ιE)
    (hF : b ≫ cPF = ΦF ≫ ιF)
    (hfX : ιF ≫ fXh1 = fXh2 ≫ rι)
    (hρ : r ≫ ΦF ≫ fXh2 = fy1 ≫ ΦE ≫ pb)
    (hord : ιE ≫ θ0 = pb ≫ rι) :
    a ≫ t = r ≫ b := by
  apply (cancel_mono (cPF ≫ fXh1)).1
  calc (a ≫ t) ≫ cPF ≫ fXh1 = a ≫ fy2 ≫ cPE ≫ θ0 := by rw [Category.assoc, hΘ]
    _ = fy1 ≫ eEP ≫ cPE ≫ θ0 := by rw [← Category.assoc a, ← hn, Category.assoc]
    _ = fy1 ≫ ΦE ≫ ιE ≫ θ0 := by rw [← Category.assoc eEP, hE, Category.assoc]
    _ = fy1 ≫ ΦE ≫ pb ≫ rι := by rw [hord]
    _ = r ≫ ΦF ≫ fXh2 ≫ rι := by
      simpa only [Category.assoc] using (congrArg (· ≫ rι) hρ).symm
    _ = r ≫ ΦF ≫ ιF ≫ fXh1 := by rw [hfX]
    _ = (r ≫ b) ≫ cPF ≫ fXh1 := by
      rw [Category.assoc, ← Category.assoc b, hF, Category.assoc]

/-- The restriction/pullback mate identity on a flat-term K-flat representative whose
restriction is again flat-term K-flat. -/
theorem pbcScalarPullMate_restriction_app
    (K : CochainComplex (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l F))) ℤ)
    (hK : PbcFlatKFlat Y (pbcIntegralDatum l F) K)
    (hR : PbcFlatKFlat Y (pbcIntegralDatum l E)
      (((pbcRestrict (pbcScalarCoefficientMap l E F i Y)).mapHomologicalComplex (.up ℤ)).obj K)) :
    (whiskerLeft (pbcDerivedRestrict (pbcScalarCoefficientMap l E F i Y))
        (pbcPullComparison g (pbcIntegralDatum l E)) ≫
      (mateEquiv (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y))
        (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X))
        (TwoSquare.mk _ _ _ _ (pbcScalarOrdinaryPullIso l E F i g).inv))).app
        (DerivedCategory.Q.obj K) =
    ((pbcScalarRestrictionPullback l E F i g).inv ≫
      whiskerRight (pbcPullComparison g (pbcIntegralDatum l F))
        (pbcDerivedRestrict (pbcScalarCoefficientMap l E F i X))).app
        (DerivedCategory.Q.obj K) := by
  let resY := pbcRestrict (pbcScalarCoefficientMap l E F i Y)
  let resX := pbcRestrict (pbcScalarCoefficientMap l E F i X)
  let dE := pbcIntegralDatum l E
  let dF := pbcIntegralDatum l F
  have := pbcActualPullComplexCounit_isIso g dF K hK
  have hΘ := pbcScalarPullMate_app l E F i g K hK hR
  have hE := pbcPullComparison_app g dE _ hR
  have hF := congrArg resX.mapDerivedCategory.map (pbcPullComparison_app g dF K hK)
  rw [Functor.map_comp, Functor.map_comp] at hF
  have hρ := pbcScalarRestrictionPullback_app l E F i g K
  have hn := (pbcPullComparison g dE).naturality (resY.mapDerivedCategoryFactors.hom.app K)
  have hfX := resX.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex (pbcModulePullIso g dF).hom (.up ℤ)).app K)
  have hord : DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (pbcModulePullIso g dE).hom (.up ℤ)).app ((resY.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (pbcScalarOrdinaryRestrictionPull l E F i g) (.up ℤ)).app K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (proEtaleRingRestrictionPullbackInv g
            (pbcAdicCompletion Y dE) (pbcAdicCompletion Y dF)
            (pbcAdicCompletion X dE) (pbcAdicCompletion X dF)
            (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
            (pbcCompletedCoefficientIso g dE) (pbcCompletedCoefficientIso g dF)
            (pbcScalarCoefficientInverseSquare l E F i g)) (.up ℤ)).app K) ≫
        DerivedCategory.Q.map ((resX.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (pbcModulePullIso g dF).hom (.up ℤ)).app K)) := by
    have hc : (NatTrans.mapHomologicalComplex
        (pbcModulePullIso g dE).hom (.up ℤ)).app ((resY.mapHomologicalComplex (.up ℤ)).obj K) ≫
        (NatTrans.mapHomologicalComplex (pbcScalarOrdinaryRestrictionPull l E F i g)
          (.up ℤ)).app K =
        (NatTrans.mapHomologicalComplex (proEtaleRingRestrictionPullbackInv g
            (pbcAdicCompletion Y dE) (pbcAdicCompletion Y dF)
            (pbcAdicCompletion X dE) (pbcAdicCompletion X dF)
            (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
            (pbcCompletedCoefficientIso g dE) (pbcCompletedCoefficientIso g dF)
            (pbcScalarCoefficientInverseSquare l E F i g)) (.up ℤ)).app K ≫
          (resX.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex (pbcModulePullIso g dF).hom (.up ℤ)).app K) := by
      apply HomologicalComplex.hom_ext
      intro n
      exact NatTrans.congr_app (pbcScalarOrdinaryRestrictionPull_eq l E F i g) (K.X n)
    have hq := congrArg DerivedCategory.Q.map hc
    exact (DerivedCategory.Q.map_comp _ _).symm.trans (hq.trans (DerivedCategory.Q.map_comp _ _))
  exact scalarPullMate_chase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by
      have h1 := Functor.map_isIso (pbcDerivedRestrict (pbcScalarCoefficientMap l E F i X))
        (pbcActualPullComplexCounit g (pbcIntegralDatum l F) K)
      let rX := pbcRestrict (pbcScalarCoefficientMap l E F i X)
      let PK := ((pbcActualModulePull g (pbcIntegralDatum l F)).mapHomologicalComplex
        (.up ℤ)).obj K
      have h2 : Mono (rX.mapDerivedCategoryFactors.hom.app PK) :=
        inferInstanceAs (Mono (rX.mapDerivedCategoryFactors.app PK).hom)
      refine @mono_comp _ _ _ _ _ _ ?_ _ ?_
      · infer_instance
      · exact h2) hΘ hn hE hF hfX hρ hord

-- Natural transformations out of a derived category agree once they agree on a
-- resolving class of complexes.
private theorem scalarNatTrans_ext_of_resolutions {C D : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] [Category D]
    {G H : DerivedCategory C ⥤ D} (f f' : G ⟶ H) (P : CochainComplex C ℤ → Prop)
    (hres : ∀ K, ∃ (L : CochainComplex C ℤ) (s : L ⟶ K), QuasiIso s ∧ P L)
    (h : ∀ K, P K → f.app (DerivedCategory.Q.obj K) = f'.app (DerivedCategory.Q.obj K)) :
    f = f' := by
  ext N
  obtain ⟨K, ⟨e⟩⟩ : ∃ K, Nonempty (DerivedCategory.Q.obj K ≅ N) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso N⟩⟩
  obtain ⟨L, s, hs, hL⟩ := hres K
  have hK : f.app (DerivedCategory.Q.obj K) = f'.app (DerivedCategory.Q.obj K) := by
    rw [← cancel_epi (G.map (DerivedCategory.Q.map s)), f.naturality, f'.naturality, h L hL]
  rw [← cancel_epi (G.map e.hom), f.naturality, f'.naturality, hK]

/-- The scalar mate of the inverse normalized pullback comparison is the termwise
restriction/pullback comparison, after the canonical pullback comparisons. -/
theorem pbcScalarPullMate_restriction :
    whiskerLeft (pbcDerivedRestrict (pbcScalarCoefficientMap l E F i Y))
        (pbcPullComparison g (pbcIntegralDatum l E)) ≫
      (mateEquiv (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y))
        (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X))
        (TwoSquare.mk _ _ _ _ (pbcScalarOrdinaryPullIso l E F i g).inv)) =
    (pbcScalarRestrictionPullback l E F i g).inv ≫
      whiskerRight (pbcPullComparison g (pbcIntegralDatum l F))
        (pbcDerivedRestrict (pbcScalarCoefficientMap l E F i X)) := by
  apply scalarNatTrans_ext_of_resolutions _ _
    (fun K ↦ PbcFlatKFlat Y (pbcIntegralDatum l F) K) (pbcFlatKFlat_resolution Y _)
  intro K hK
  exact pbcScalarPullMate_restriction_app l E F i g K hK
    (pbcScalarRestrict_flatKFlat l E F i Y K hK)

-- Mates are unchanged when the left adjoints are replaced through conjugates of identities.
private theorem scalarMate_change_left
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ L₁' : A ⥤ B} {R₁ : B ⥤ A} {L₂ L₂' : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a₁ : L₁ ⊣ R₁) (b₁ : L₁' ⊣ R₁) (a₂ : L₂ ⊣ R₂) (b₂ : L₂' ⊣ R₂)
    (β : TwoSquare G L₁ L₂ H) (γ : TwoSquare G L₁' L₂' H)
    (h : whiskerLeft G ((conjugateEquiv a₂ b₂).symm (𝟙 R₂)) ≫ β =
      γ ≫ whiskerRight ((conjugateEquiv a₁ b₁).symm (𝟙 R₁)) H) :
    (mateEquiv a₁ a₂ β) = (mateEquiv b₁ b₂ γ) := by
  have h₁ := mateEquiv_conjugateEquiv_vcomp a₁ a₂ b₂ β ((conjugateEquiv a₂ b₂).symm (𝟙 R₂))
  have h₂ := conjugateEquiv_mateEquiv_vcomp a₁ b₁ b₂ ((conjugateEquiv a₁ b₁).symm (𝟙 R₁)) γ
  have hw : β.whiskerRight ((conjugateEquiv a₂ b₂).symm (𝟙 R₂)) =
      γ.whiskerLeft ((conjugateEquiv a₁ b₁).symm (𝟙 R₁)) := by
    ext K
    exact NatTrans.congr_app h K
  rw [hw, h₂, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h₁
  ext K
  have hk := NatTrans.congr_app (h₁) K
  simpa [TwoSquare.whiskerTop, TwoSquare.whiskerBottom] using hk.symm

private theorem scalarMate_adjunct
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : TwoSquare G L L' H)
    (M : A) (N : B) (t : L.obj M ⟶ N) :
    adj'.homEquiv _ _ (s.app M ≫ H.map t) =
      G.map (adj.homEquiv M N t) ≫ (mateEquiv adj adj' s).app N := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hu := unit_mateEquiv adj adj' s M
  dsimp only [Functor.id_obj] at hu
  rw [← Category.assoc, ← hu, Category.assoc]
  have hn := (mateEquiv adj adj' s).naturality t
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← G.map_comp]

/-- The canonical restriction/direct-image comparison is the pullback mate of the
inverse termwise restriction/pullback comparison. -/
theorem pbcScalarRestrictionDirectImage_mate :
    (mateEquiv (proEtaleRingDerivedAdjunction g (pbcAdicCompletion Y (pbcIntegralDatum l F))
        (pbcAdicCompletion X (pbcIntegralDatum l F))
        (pbcCompletedCoefficientIso g (pbcIntegralDatum l F)))
      (proEtaleRingDerivedAdjunction g (pbcAdicCompletion Y (pbcIntegralDatum l E))
        (pbcAdicCompletion X (pbcIntegralDatum l E))
        (pbcCompletedCoefficientIso g (pbcIntegralDatum l E)))
      (TwoSquare.mk _ _ _ _ (pbcScalarRestrictionPullback l E F i g).inv)) =
    (pbcScalarRestrictionDirectImage l E F i g).hom := by
  let aS := proEtaleRingDerivedAdjunction g (pbcAdicCompletion Y (pbcIntegralDatum l F))
    (pbcAdicCompletion X (pbcIntegralDatum l F))
    (pbcCompletedCoefficientIso g (pbcIntegralDatum l F))
  let aR := proEtaleRingDerivedAdjunction g (pbcAdicCompletion Y (pbcIntegralDatum l E))
    (pbcAdicCompletion X (pbcIntegralDatum l E))
    (pbcCompletedCoefficientIso g (pbcIntegralDatum l E))
  ext N
  have hcl := (proEtaleRingSheafChangeAdjunction g
    (pbcAdicCompletion Y (pbcIntegralDatum l E)) (pbcAdicCompletion Y (pbcIntegralDatum l F))
    (pbcAdicCompletion X (pbcIntegralDatum l E)) (pbcAdicCompletion X (pbcIntegralDatum l F))
    (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
    (pbcCompletedCoefficientIso g (pbcIntegralDatum l E))
    (pbcCompletedCoefficientIso g (pbcIntegralDatum l F))
    (pbcScalarCoefficientInverseSquare l E F i g)).2.2 _ N (aS.counit.app N)
  have hma := scalarMate_adjunct aS aR
    (TwoSquare.mk _ _ _ _ (pbcScalarRestrictionPullback l E F i g).inv) _ N (aS.counit.app N)
  have h1 : aS.homEquiv _ N (aS.counit.app N) = 𝟙 _ := by
    simp [Adjunction.homEquiv_unit]
  rw [h1, CategoryTheory.Functor.map_id, Category.id_comp] at hma hcl
  exact hma.symm.trans hcl

/-- The normalized derived pullback comparison is the conjugate of the canonical
inverse restriction/direct-image comparison. -/
theorem pbcScalarOrdinaryPullIso_conjugate :
    conjugateEquiv ((pbcActualDerivedAdjunction g (pbcIntegralDatum l E)).comp
        (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X)))
      ((pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y)).comp
        (pbcActualDerivedAdjunction g (pbcIntegralDatum l F)))
      (pbcScalarOrdinaryPullIso l E F i g).hom =
    (pbcScalarRestrictionDirectImage l E F i g).inv := by
  let aPE := pbcActualDerivedAdjunction g (pbcIntegralDatum l E)
  let aPF := pbcActualDerivedAdjunction g (pbcIntegralDatum l F)
  let aY := pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y)
  let aX := pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X)
  let aQE := proEtaleRingDerivedAdjunction g (pbcAdicCompletion Y (pbcIntegralDatum l E))
    (pbcAdicCompletion X (pbcIntegralDatum l E))
    (pbcCompletedCoefficientIso g (pbcIntegralDatum l E))
  let aQF := proEtaleRingDerivedAdjunction g (pbcAdicCompletion Y (pbcIntegralDatum l F))
    (pbcAdicCompletion X (pbcIntegralDatum l F))
    (pbcCompletedCoefficientIso g (pbcIntegralDatum l F))
  let α := pbcScalarOrdinaryPullIso l E F i g
  let δ := pbcScalarRestrictionDirectImage l E F i g
  have hi := iterated_mateEquiv_conjugateEquiv aY aX aPE aPF (TwoSquare.mk _ _ _ _ α.inv)
  have hm := scalarMate_change_left aPF aQF aPE aQE
    (mateEquiv aY aX (TwoSquare.mk _ _ _ _ α.inv))
    (TwoSquare.mk _ _ _ _ (pbcScalarRestrictionPullback l E F i g).inv)
    (pbcScalarPullMate_restriction l E F i g)
  have hc' : conjugateEquiv (aY.comp aPF) (aPE.comp aX) α.inv = δ.hom :=
    hi.symm.trans (hm.trans (pbcScalarRestrictionDirectImage_mate l E F i g))
  have hcomp : conjugateEquiv (aPE.comp aX) (aY.comp aPF) α.hom ≫ δ.hom = 𝟙 _ := by
    rw [← hc']
    refine (conjugateEquiv_comp (aPE.comp aX) (aY.comp aPF) (aPE.comp aX) α.hom α.inv).trans ?_
    rw [α.inv_hom_id]
    exact conjugateEquiv_id (aPE.comp aX)
  apply (cancel_mono δ.hom).1
  exact hcomp.trans δ.inv_hom_id.symm

/-- The scalar mate of the direct-image comparison is the canonical inverse
restriction/direct-image comparison. -/
theorem pbcScalarDirectImageMap_scalarMate :
    (mateEquiv (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X))
        (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y))
        (TwoSquare.mk _ _ _ _ (pbcScalarDirectImageMap l E F i g))) =
      (pbcScalarRestrictionDirectImage l E F i g).inv := by
  have h := iterated_mateEquiv_conjugateEquiv
    (pbcActualDerivedAdjunction g (pbcIntegralDatum l E))
    (pbcActualDerivedAdjunction g (pbcIntegralDatum l F))
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y))
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X))
    (TwoSquare.mk _ _ _ _ (pbcScalarOrdinaryPullIso l E F i g).hom)
  rw [← pbcScalarOrdinaryPullIso_conjugate]
  refine Eq.trans ?_ (h)
  simp only [pbcScalarDirectImageMap, pbcActualScalarDirectImageMap, pbcScalarOrdinaryPullIso]

/-- The canonical scalar/direct-image mate is invertible for finite coefficient extensions. -/
@[instance] theorem pbcScalarDirectImageMap_isIso :
    IsIso (pbcScalarDirectImageMap l E F i g) := by
  obtain ⟨d, hfree⟩ := pbcScalarCoefficient_finiteFree l E F i Y
  have hiso := FiniteFreeDirectImage.restrictionDirectImageMate_isIso g _ _ _ _ _ _ _ _
    (pbcScalarCoefficientInverseSquare l E F i g) d hfree
  let δ := pbcScalarRestrictionDirectImage l E F i g
  have hs : mateEquiv (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X))
      (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y))
      (TwoSquare.mk _ _ _ _ (pbcScalarDirectImageMap l E F i g)) =
        TwoSquare.mk _ _ _ _ δ.inv := by
    ext K
    exact NatTrans.congr_app (pbcScalarDirectImageMap_scalarMate l E F i g) K
  have hμ := (((mateEquiv
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X))
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y))).eq_symm_apply).2 hs)
  change IsIso (TwoSquare.mk _ _ _ _ (pbcScalarDirectImageMap l E F i g))
  rw [hμ]
  exact hiso

/-- The canonical invertible direct-image comparison, with its mate definition retained. -/
@[irreducible] def pbcScalarDirectImageIso :
    pbcActualDerivedPush g (pbcIntegralDatum l E) ⋙
        pbcEmbeddingAmbientTensor l E F i Y ≅
      pbcEmbeddingAmbientTensor l E F i X ⋙
        pbcActualDerivedPush g (pbcIntegralDatum l F) :=
  asIso (pbcScalarDirectImageMap l E F i g)

private theorem pbcScalarDirectImageIso_hom :
    (pbcScalarDirectImageIso l E F i g).hom = pbcScalarDirectImageMap l E F i g := by
  unfold pbcScalarDirectImageIso
  rfl

-- Construct both arrows from the two reflection Hom bijections. Scalar restriction
-- lets the source reflection compute maps into complete target-coefficient objects.
private theorem scalar_reflector_transport
    {V Z : Type*} [Category V] [Category Z]
    (F : V ⥤ Z) (U : Z ⥤ V) (adj : F ⊣ U)
    (L : V ⥤ V) (M : Z ⥤ Z) (η : 𝟭 V ⟶ L) (ε : 𝟭 Z ⟶ M)
    (P : V → Prop) (Q : Z → Prop)
    (hd : ∀ X, Q (M.obj X))
    (hb : ∀ X Y, P Y → Function.Bijective (fun f : L.obj X ⟶ Y ↦ η.app X ≫ f))
    (he : ∀ X Y, Q Y → Function.Bijective (fun f : M.obj X ⟶ Y ↦ ε.app X ≫ f))
    (hF : ∀ X, Q (F.obj (L.obj X))) (hU : ∀ Y, Q Y → P (U.obj Y)) :
    ∃! e : F ⋙ M ≅ L ⋙ F,
      ∀ X, ε.app (F.obj X) ≫ e.hom.app X = F.map (η.app X) := by
  classical
  have hj (X : V) (Y : Z) (hY : Q Y) :
      Function.Bijective (fun f : F.obj (L.obj X) ⟶ Y ↦ F.map (η.app X) ≫ f) := by
    constructor
    · intro f g h
      apply (adj.homEquiv _ _).injective
      apply (hb X (U.obj Y) (hU Y hY)).1
      simpa only [← adj.homEquiv_naturality_left, Functor.id_obj] using
        congrArg (adj.homEquiv X Y) h
    · intro f
      obtain ⟨g, hg⟩ := (hb X (U.obj Y) (hU Y hY)).2 ((adj.homEquiv X Y) f)
      refine ⟨(adj.homEquiv (L.obj X) Y).symm g, ?_⟩
      apply (adj.homEquiv X Y).injective
      rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply]
      exact hg
  let f (X : V) := (he (F.obj X) (F.obj (L.obj X)) (hF X)).2
    (F.map (η.app X)) |>.choose
  have hf (X : V) : ε.app (F.obj X) ≫ f X = F.map (η.app X) :=
    (he (F.obj X) (F.obj (L.obj X)) (hF X)).2 (F.map (η.app X)) |>.choose_spec
  let g (X : V) := (hj X (M.obj (F.obj X)) (hd _)).2 (ε.app (F.obj X)) |>.choose
  have hg (X : V) : F.map (η.app X) ≫ g X = ε.app (F.obj X) :=
    (hj X (M.obj (F.obj X)) (hd _)).2 (ε.app (F.obj X)) |>.choose_spec
  let eX (X : V) : M.obj (F.obj X) ≅ F.obj (L.obj X) :=
    { hom := f X
      inv := g X
      hom_inv_id := by
        apply (he _ _ (hd (F.obj X))).1
        change ε.app (F.obj X) ≫ (f X ≫ g X) = ε.app (F.obj X) ≫ 𝟙 _
        rw [← Category.assoc, hf, hg, Category.comp_id]
      inv_hom_id := by
        apply (hj X _ (hF X)).1
        change F.map (η.app X) ≫ (g X ≫ f X) = F.map (η.app X) ≫ 𝟙 _
        rw [← Category.assoc, hg, hf, Category.comp_id] }
  let e : F ⋙ M ≅ L ⋙ F := NatIso.ofComponents eX (fun {X Y} h ↦ by
    apply (he _ _ (hF Y)).1
    change ε.app (F.obj X) ≫ (M.map (F.map h) ≫ f Y) =
      ε.app (F.obj X) ≫ (f X ≫ F.map (L.map h))
    rw [← Category.assoc, ← ε.naturality, Category.assoc, hf]
    rw [← Category.assoc, hf]
    simp only [Functor.id_map]
    rw [← F.map_comp, ← F.map_comp]
    simpa only [Functor.id_map] using congrArg F.map (η.naturality h))
  refine ⟨e, hf, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply (he _ _ (hF X)).1
  exact (he' X).trans (hf X).symm

private theorem scalar_completion_reflection
    (W : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K L : PbcCompletedDerived W d) (hL : PbcIsIntrinsicallyComplete W d L) :
    Function.Bijective (fun f : (pbcActualCompletion d W).obj K ⟶ L ↦
      (pbcActualCompletionUnit d W).app K ≫ f) := by
  let P : ObjectProperty (PbcCompletedDerived W d) := PbcIsIntrinsicallyComplete W d
  let adj := Adjunction.ofIsRightAdjoint P.ι
  exact ((ObjectProperty.fullyFaithfulι P).homEquiv.symm.trans
    (adj.homEquiv K ⟨L, hL⟩)).bijective

/-- Scalar extension commutes with completion through the actual quotient augmentation. -/
theorem pbcScalarCompletionIso_exists (W : Scheme.{u}) :
    ∃! e : pbcEmbeddingAmbientTensor l E F i W ⋙
        pbcActualCompletion (pbcIntegralDatum l F) W ≅
      pbcActualCompletion (pbcIntegralDatum l E) W ⋙
        pbcEmbeddingAmbientTensor l E F i W,
      ∀ K : PbcCompletedDerived W (pbcIntegralDatum l E),
        (pbcActualCompletionUnit (pbcIntegralDatum l F) W).app
            ((pbcEmbeddingAmbientTensor l E F i W).obj K) ≫ e.hom.app K =
          (pbcEmbeddingAmbientTensor l E F i W).map
            ((pbcActualCompletionUnit (pbcIntegralDatum l E) W).app K) := by
  exact scalar_reflector_transport
    (pbcEmbeddingAmbientTensor l E F i W)
    (pbcDerivedRestrict (pbcScalarCoefficientMap l E F i W))
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i W))
    (pbcActualCompletion (pbcIntegralDatum l E) W)
    (pbcActualCompletion (pbcIntegralDatum l F) W)
    (pbcActualCompletionUnit (pbcIntegralDatum l E) W)
    (pbcActualCompletionUnit (pbcIntegralDatum l F) W)
    (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E))
    (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l F))
    (fun K ↦ ((ObjectProperty.ι
      (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l F))).leftAdjoint.obj K).property)
    (scalar_completion_reflection W (pbcIntegralDatum l E))
    (scalar_completion_reflection W (pbcIntegralDatum l F))
    (pbcScalarCompletedObjectComplete l E F i W)
    (pbcScalarRestrictionComplete l E F i W)

/-- The unique completion comparison preserving the specified quotient unit. -/
@[irreducible] def pbcScalarCompletionIso (W : Scheme.{u}) :
    pbcEmbeddingAmbientTensor l E F i W ⋙
        pbcActualCompletion (pbcIntegralDatum l F) W ≅
      pbcActualCompletion (pbcIntegralDatum l E) W ⋙
        pbcEmbeddingAmbientTensor l E F i W :=
  (pbcScalarCompletionIso_exists l E F i W).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcComplete_iso (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    ObjectProperty.IsClosedUnderIsomorphisms (PbcIsIntrinsicallyComplete W d) := by
  constructor
  intro K L e hK
  obtain ⟨r, f, hf, C, eC, hC⟩ := hK
  refine ⟨r, f, hf, C,
    eC ≪≫ (pbcDerivedExtend (pbcCompletedComparison W d).inv).mapIso e, ?_⟩
  change IsIso (eC.inv ≫ _) at hC
  have hu := (isIso_comp_left_iff eC.inv _).mp hC
  change IsIso ((_ ≫ eC.inv) ≫ _)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite-free coefficient extension preserves ambient intrinsic completeness. -/
theorem pbcScalarPreservesComplete (W : Scheme.{u})
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E))) :
    PbcIsIntrinsicallyComplete W (pbcIntegralDatum l F)
      ((pbcEmbeddingAmbientTensor l E F i W).obj K.obj) := by
  let dE := pbcIntegralDatum l E
  let dF := pbcIntegralDatum l F
  let I := ObjectProperty.ι (PbcIsIntrinsicallyComplete W dE)
  let adj := Adjunction.ofIsRightAdjoint I
  have hη : IsIso ((pbcActualCompletionUnit dE W).app K.obj) := by
    change IsIso (adj.unit.app (I.obj K))
    infer_instance
  obtain ⟨e, he, _⟩ := pbcScalarCompletionIso_exists l E F i W
  have hmap : IsIso ((pbcEmbeddingAmbientTensor l E F i W).map
      ((pbcActualCompletionUnit dE W).app K.obj)) := inferInstance
  have hcomp : IsIso ((pbcActualCompletionUnit dF W).app
      ((pbcEmbeddingAmbientTensor l E F i W).obj K.obj) ≫ e.hom.app K.obj) := by
    rw [he K.obj]
    exact hmap
  have hunit : IsIso ((pbcActualCompletionUnit dF W).app
      ((pbcEmbeddingAmbientTensor l E F i W).obj K.obj)) :=
    (isIso_comp_right_iff _ (e.hom.app K.obj)).mp hcomp
  have := pbcComplete_iso W dF
  exact ObjectProperty.prop_of_iso (PbcIsIntrinsicallyComplete W dF)
    (asIso ((pbcActualCompletionUnit dF W).app
      ((pbcEmbeddingAmbientTensor l E F i W).obj K.obj))).symm
    ((ObjectProperty.ι (PbcIsIntrinsicallyComplete W dF)).leftAdjoint.obj
      ((pbcEmbeddingAmbientTensor l E F i W).obj K.obj)).property

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Completed scalar/pullback is the ordinary comparison followed by the canonical
completion comparisons. -/
@[irreducible] def pbcScalarCompletedPullIso :
    pbcEmbeddingAmbientTensor l E F i Y ⋙
        pbcActualCompletedPull g (pbcIntegralDatum l F) ≅
      pbcActualCompletedPull g (pbcIntegralDatum l E) ⋙
        pbcEmbeddingAmbientTensor l E F i X :=
  NatIso.ofComponents
    (F := pbcEmbeddingAmbientTensor l E F i Y ⋙
      pbcActualCompletedPull g (pbcIntegralDatum l F))
    (G := pbcActualCompletedPull g (pbcIntegralDatum l E) ⋙
      pbcEmbeddingAmbientTensor l E F i X) (fun K ↦
    (pbcActualCompletion (pbcIntegralDatum l F) X).mapIso
        ((pbcScalarOrdinaryPullIso l E F i g).app K) ≪≫
      (pbcScalarCompletionIso l E F i X).app
        ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K)) (fun {K L} f ↦ by
    have he := (pbcScalarOrdinaryPullIso l E F i g).hom.naturality f
    have hc := (pbcScalarCompletionIso l E F i X).hom.naturality
      ((pbcActualDerivedPull g (pbcIntegralDatum l E)).map f)
    dsimp only [CategoryTheory.Functor.comp_map] at he hc
    dsimp only [pbcActualCompletedPull, CategoryTheory.Functor.comp_map, Iso.trans_hom,
      CategoryTheory.Functor.mapIso_hom, Iso.app_hom]
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, he,
      CategoryTheory.Functor.map_comp, Category.assoc, hc, Category.assoc])

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcScalarCompletedPullIso_hom
    (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) :
    (pbcScalarCompletedPullIso l E F i g).hom.app K =
      (pbcActualCompletion (pbcIntegralDatum l F) X).map
          ((pbcScalarOrdinaryPullIso l E F i g).hom.app K) ≫
        (pbcScalarCompletionIso l E F i X).hom.app
          ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K) := by
  unfold pbcScalarCompletedPullIso
  rfl

variable {X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {a : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcCompletion_hom_ext (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K L : PbcCompletedDerived W d) (hL : PbcIsIntrinsicallyComplete W d L)
    (f g : (pbcActualCompletion d W).obj K ⟶ L)
    (h : (pbcActualCompletionUnit d W).app K ≫ f =
      (pbcActualCompletionUnit d W).app K ≫ g) : f = g := by
  let I := ObjectProperty.ι (PbcIsIntrinsicallyComplete W d)
  let adj := Adjunction.ofIsRightAdjoint I
  let N : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete W d) := ⟨L, hL⟩
  let a : I.leftAdjoint.obj K ⟶ N := ObjectProperty.homMk f
  let b : I.leftAdjoint.obj K ⟶ N := ObjectProperty.homMk g
  have hab : adj.homEquiv K N a = adj.homEquiv K N b := by
    change adj.unit.app K ≫ I.map a = adj.unit.app K ≫ I.map b at h
    simpa only [Adjunction.homEquiv_unit] using h
  exact congrArg (fun z ↦ z.hom) ((adj.homEquiv K N).injective hab)

end AmbientOperations
end AlgebraicGeometry.Scheme

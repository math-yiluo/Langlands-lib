/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedForgetTwoInjective.RingedForgetTwoInjectiveHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement

/-! # Data for normalized ringed tensor transposition

These are the existing comparison data, factored out so that tensor descent and
normalized uncurrying can be proved independently.
Source: Stacks 06YU, 08J9, 0FPT
(blueprint: def-sf-ringed-forget-tensor-transposition-data).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe b vb a va c v r d vd s wb wa

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures

namespace CategoryTheory.RingedForgetTensorTransposition

section Coherence

variable {B : Type b} [Category.{vb} B] {A : Type a} [Category.{va} A]

/-- Unit, associativity and symmetry coherence for the specified comparison, oriented
from the image of a tensor to the tensor of the images. These are equations on existing
monoidal structures, not a new tensor construction.
Source: Stacks 0FPT (blueprint: lem-sf-ringed-forget-tensor-transposition). -/
structure TensorCoherence (mB : MonoidalCategory B) (mA : MonoidalCategory A)
    (βB : @SymmetricCategory B _ mB) (βA : @SymmetricCategory A _ mA)
    (F : B ⥤ A)
    (μ : @MonoidalCategory.tensor B _ mB ⋙ F ≅
      (F.prod F) ⋙ @MonoidalCategory.tensor A _ mA) where
  /-- The specified unit comparison. -/
  unit : F.obj mB.tensorUnit ≅ mA.tensorUnit
  /-- The associativity square. -/
  associativity (X Y Z : B) :
    F.map (mB.associator X Y Z).hom ≫
        μ.hom.app (X, mB.tensorObj Y Z) ≫
        (@MonoidalCategory.tensor A _ mA).map
          (X := (F.obj X, F.obj (mB.tensorObj Y Z)))
          (Y := (F.obj X, mA.tensorObj (F.obj Y) (F.obj Z)))
          (𝟙 _, μ.hom.app (Y, Z)) =
      μ.hom.app (mB.tensorObj X Y, Z) ≫
        (@MonoidalCategory.tensor A _ mA).map
          (X := (F.obj (mB.tensorObj X Y), F.obj Z))
          (Y := (mA.tensorObj (F.obj X) (F.obj Y), F.obj Z))
          (μ.hom.app (X, Y), 𝟙 _) ≫
        (mA.associator (F.obj X) (F.obj Y) (F.obj Z)).hom
  /-- Left unit coherence. -/
  left_unit (X : B) :
    μ.hom.app (mB.tensorUnit, X) ≫
        (@MonoidalCategory.tensor A _ mA).map
          (X := (F.obj mB.tensorUnit, F.obj X)) (Y := (mA.tensorUnit, F.obj X))
          (unit.hom, 𝟙 _) ≫
        (mA.leftUnitor (F.obj X)).hom = F.map (mB.leftUnitor X).hom
  /-- Right unit coherence. -/
  right_unit (X : B) :
    μ.hom.app (X, mB.tensorUnit) ≫
        (@MonoidalCategory.tensor A _ mA).map
          (X := (F.obj X, F.obj mB.tensorUnit)) (Y := (F.obj X, mA.tensorUnit))
          (𝟙 _, unit.hom) ≫
        (mA.rightUnitor (F.obj X)).hom = F.map (mB.rightUnitor X).hom
  /-- Symmetry coherence, including the Koszul sign on complexes. -/
  symmetry (X Y : B) :
    F.map (βB.toBraidedCategory.braiding X Y).hom ≫ μ.hom.app (Y, X) =
      μ.hom.app (X, Y) ≫ (βA.toBraidedCategory.braiding (F.obj X) (F.obj Y)).hom

/-- The actual double-dual arrow, defined by the fixed adjunction and symmetry.
Source: Stacks 08J9, 0FPT and the blueprint transposition paragraph
(blueprint: lem-sf-ringed-forget-tensor-transposition). -/
def delta {H : Bᵒᵖ × B ⥤ B} (S : CoefficientClosedStructure H)
    (β : @SymmetricCategory B _ S.monoidal) (W K : B) :
    K ⟶ H.obj (op (H.obj (op K, W)), W) :=
  S.transpose K (H.obj (op K, W)) W
    ((β.toBraidedCategory.braiding K (H.obj (op K, W))).hom ≫ S.evaluation K W)

/-- The normalized uncurrying, evaluation and double-dual equations for fixed comparisons.
Source: Stacks 08J9 and the blueprint transposition paragraph
(blueprint: lem-sf-ringed-forget-tensor-transposition). -/
structure TranspositionLaws
    (HB : Bᵒᵖ × B ⥤ B) (HA : Aᵒᵖ × A ⥤ A)
    (SB : CoefficientClosedStructure HB) (SA : CoefficientClosedStructure HA)
    (βB : @SymmetricCategory B _ SB.monoidal)
    (βA : @SymmetricCategory A _ SA.monoidal) (F : B ⥤ A)
    (χ : HB ⋙ F ≅ (F.op.prod F) ⋙ HA)
    (μ : SB.tensor ⋙ F ≅ (F.prod F) ⋙ SA.tensor) : Prop where
  /-- The uncurrying equality for every derived arrow. -/
  uncurry (M K L : B) (f : M ⟶ HB.obj (op K, L)) :
    (SA.transpose (F.obj M) (F.obj K) (F.obj L)).symm
        (F.map f ≫ χ.hom.app (op K, L)) =
      μ.inv.app (M, K) ≫ F.map ((SB.transpose M K L).symm f)
  /-- The displayed evaluation square. -/
  evaluation (K L : B) :
    μ.hom.app (HB.obj (op K, L), K) ≫
        SA.tensor.map
          (X := (F.obj (HB.obj (op K, L)), F.obj K))
          (Y := (HA.obj (op (F.obj K), F.obj L), F.obj K))
          (χ.hom.app (op K, L), 𝟙 _) ≫
        SA.evaluation (F.obj K) (F.obj L) = F.map (SB.evaluation K L)
  /-- Naturality of the source double-dual arrow. -/
  delta_source (W K K' : B) (f : K ⟶ K') :
    delta SB βB W K ≫
        HB.map (X := (op (HB.obj (op K, W)), W))
          (Y := (op (HB.obj (op K', W)), W))
          ((HB.map (X := (op K', W)) (Y := (op K, W)) (f.op, 𝟙 W)).op, 𝟙 W) =
      f ≫ delta SB βB W K'
  /-- Naturality on the target site, for every target derived object and arrow. -/
  delta_target (W K K' : A) (f : K ⟶ K') :
    delta SA βA W K ≫
        HA.map (X := (op (HA.obj (op K, W)), W))
          (Y := (op (HA.obj (op K', W)), W))
          ((HA.map (X := (op K', W)) (Y := (op K, W)) (f.op, 𝟙 W)).op, 𝟙 W) =
      f ≫ delta SA βA W K'
  /-- The iterated comparison uses the inverse in the contravariant Hom variable. -/
  delta_forget (W K : B) :
    F.map (delta SB βB W K) ≫ χ.hom.app (op (HB.obj (op K, W)), W) ≫
        HA.map (X := (op (F.obj (HB.obj (op K, W))), F.obj W))
          (Y := (op (HA.obj (op (F.obj K), F.obj W)), F.obj W))
          ((χ.inv.app (op K, W)).op, 𝟙 _) =
      delta SA βA (F.obj W) (F.obj K)

end Coherence

section Sites

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

/-- The actual sheafified pure tensor, using the sheafification unit.
Source: Stacks 03EK (blueprint: lem-sf-ringed-forget-tensor-transposition). -/
def sheafTensorGenerator (K L : RingedTensorModules.{c, v, r} J R)
    (V : Cᵒᵖ) (x : K.val.obj V) (y : L.val.obj V) :
    ((SheafOfModules.monoidalCategory R).tensorObj K L).val.obj V :=
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  ((SheafOfModules.tensorObjIsoSheafification K L).inv.val.app V)
    (((PresheafOfModules.sheafificationAdjunction.{max c v r}
      (𝟙 ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).obj)).unit.app
        (K.val ⊗ L.val)).app V (x ⊗ₜ[R.obj.obj V] y))

/-- The full componentwise characterization of ordinary sheaf-Hom evaluation.
Pure tensors generate locally after sheafification, so this characterizes the existing
canonical evaluation uniquely. It does not select an arbitrary pairing.
Source: Stacks 03EK, 08J9 (blueprint: lem-sf-ringed-forget-tensor-transposition). -/
def IsSheafEvaluation (K L : RingedTensorModules.{c, v, r} J R)
    (e : (SheafOfModules.monoidalCategory R).tensorObj
      (SheafOfModules.homObj (R := R) K L) K ⟶ L) : Prop :=
  ∀ (V : Cᵒᵖ) (φ : (SheafOfModules.homObj (R := R) K L).val.obj V)
    (x : K.val.obj V),
    e.val.app V
        (sheafTensorGenerator.{c, v, r} J R (SheafOfModules.homObj (R := R) K L) K V φ x) =
      (φ.app (op (Over.mk (𝟙 V.unop)))).hom x

/-- The actual summand inclusion in the direct-sum total tensor.
The total functor has differential d_P tensor 1 + (-1)^p 1 tensor d_Q.
Source: Stacks 06YN (blueprint: lem-sf-ringed-forget-tensor-transposition). -/
def tensorSummand (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    (SheafOfModules.monoidalCategory R).tensorObj (P.X p) (Q.X q) ⟶
      ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X n :=
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  CochainComplex.ιMapBifunctor P Q (MonoidalCategory.curriedTensor _) p q n hpq

variable {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
  [HasSheafify J' AddCommGrpCat.{max d vd s}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
  (R' : Sheaf J' CommRingCat.{max d vd s})
  (U : RingedTensorModules.{c, v, r} J R ⥤ RingedTensorModules.{d, vd, s} J' R')
  [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]

/-- The specified coherent underlying-module comparisons, including evaluation.
Source: blueprint internal-Hom paragraph; Stacks 08J9, 0FPT
(blueprint: lem-sf-ringed-forget-tensor-transposition). -/
structure Underived where
  /-- The specified underived tensor comparison. -/
  tensor : @MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory R) ⋙ U ≅
    (U.prod U) ⋙ @MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory R')
  /-- Unit, associativity and symmetry coherence for that comparison. -/
  coherence : TensorCoherence (SheafOfModules.monoidalCategory R)
    (SheafOfModules.monoidalCategory R') (SheafOfModules.symmetricCategory R)
    (SheafOfModules.symmetricCategory R') U tensor
  /-- The specified sheaf-Hom comparison, used by the recorded two-injective theorem. -/
  hom : Functor.uncurry.obj (SheafOfModules.homFunctor (R := R)) ⋙ U ≅
    (U.op.prod U) ⋙ Functor.uncurry.obj (SheafOfModules.homFunctor (R := R'))
  /-- Preservation of precisely the canonical evaluations characterized on pure tensors.
  Quantifying over their complete characterization keeps site universes independent. -/
  evaluation (K L : RingedTensorModules.{c, v, r} J R)
      (eB : (SheafOfModules.monoidalCategory R).tensorObj
        (SheafOfModules.homObj (R := R) K L) K ⟶ L)
      (eA : (SheafOfModules.monoidalCategory R').tensorObj
        (SheafOfModules.homObj (R := R') (U.obj K) (U.obj L)) (U.obj K) ⟶ U.obj L)
      (_hB : IsSheafEvaluation.{c, v, r} J R K L eB)
      (_hA : IsSheafEvaluation.{d, vd, s} J' R' (U.obj K) (U.obj L) eA) :
    tensor.hom.app (SheafOfModules.homObj (R := R) K L, K) ≫
        (@MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory R')).map
          (X := (U.obj (SheafOfModules.homObj (R := R) K L), U.obj K))
          (Y := (SheafOfModules.homObj (R := R') (U.obj K) (U.obj L), U.obj K))
          (hom.hom.app (op K, L), 𝟙 _) ≫ eA = U.map eB

variable [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{wa} (RingedTensorModules.{d, vd, s} J' R')]
  [∀ I : Type (max c v r), PreservesLimitsOfShape (Discrete I) U]
  [U.PreservesKInjectiveComplexes]
  (u : Underived.{c, v, r, d, vd, s} J R J' R' U)
  (SB : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wb} J R))
  (TB : CoefficientTensorModels.{r, c, v, wb} J R SB)
  (βB : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
    _ SB.monoidal)
  (cB : RingedDerivedTensorCoherence.{c, v, r, wb} J R SB TB βB)
  (SA : CoefficientClosedStructure (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R'))
  (TA : CoefficientTensorModels.{s, d, vd, wa} J' R' SA)
  (βA : @SymmetricCategory (DerivedCategory (RingedTensorModules.{d, vd, s} J' R'))
    _ SA.monoidal)
  (cA : RingedDerivedTensorCoherence.{d, vd, s, wa} J' R' SA TA βA)
  (χ : RingedForgetTwoInjective.Comparison.{wb, wa, c, v, r, d, vd, s}
    J R J' R' U u.hom)

/-- The prescribed representative square for an arbitrary natural transformation.
Source: Stacks 06YU, 0G7D (blueprint: lem-sf-ringed-forget-tensor-transposition). -/
def RepresentativeModel
    (chain : coefficientTotalTensor.{r, c, v} J R ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      ((U.mapHomologicalComplex (.up ℤ)).prod (U.mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{s, d, vd} J' R')
    (μ : SB.tensor ⋙ U.mapDerivedCategory ⟶
      (U.mapDerivedCategory.prod U.mapDerivedCategory) ⋙ SA.tensor) : Prop :=
  ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
      (hUP : CochainComplex.IsKFlatIndependentCoefficients (R := R')
        ((U.mapHomologicalComplex (.up ℤ)).obj P))
      (hUQ : CochainComplex.IsKFlatIndependentCoefficients (R := R')
        ((U.mapHomologicalComplex (.up ℤ)).obj Q))
      (_hPf : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r} (R := R) (P.X p))
      (_hQf : ∀ q : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r} (R := R) (Q.X q)),
    U.mapDerivedCategory.map (TB.iso.{r, c, v, wb} J R SB P Q hP hQ).hom ≫
        μ.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        SA.tensor.map
          (X := (U.mapDerivedCategory.obj (DerivedCategory.Q.obj P),
            U.mapDerivedCategory.obj (DerivedCategory.Q.obj Q)))
          (Y := (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj P),
            DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj Q)))
          (U.mapDerivedCategoryFactors.hom.app P,
          U.mapDerivedCategoryFactors.hom.app Q) =
      U.mapDerivedCategoryFactors.hom.app ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
        DerivedCategory.Q.map (chain.hom.app (P, Q)) ≫
        (TA.iso.{s, d, vd, wa} J' R' SA ((U.mapHomologicalComplex (.up ℤ)).obj P)
          ((U.mapHomologicalComplex (.up ℤ)).obj Q) hUP hUQ).hom

/-- The total-tensor comparison and its unique, coherent derived extension, for the fixed χ.
Source: Stacks 06YU, 0G7D, 08J9 and blueprint transposition paragraph
(blueprint: lem-sf-ringed-forget-tensor-transposition). -/
structure Comparison where
  /-- The sum of the specified underived comparisons, on actual total tensor complexes. -/
  chain : coefficientTotalTensor.{r, c, v} J R ⋙ U.mapHomologicalComplex (.up ℤ) ≅
    ((U.mapHomologicalComplex (.up ℤ)).prod (U.mapHomologicalComplex (.up ℤ))) ⋙
      coefficientTotalTensor.{s, d, vd} J' R'
  /-- Every summand is the specified underived tensor comparison. -/
  summand (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (p q n : ℤ) (hpq : p + q = n) :
    U.map (tensorSummand.{c, v, r} J R P Q p q n hpq) ≫ (chain.hom.app (P, Q)).f n =
      u.tensor.hom.app (P.X p, Q.X q) ≫
        tensorSummand.{d, vd, s} J' R' ((U.mapHomologicalComplex (.up ℤ)).obj P)
          ((U.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq
  /-- The natural derived isomorphism μ, in the orientation of the node. -/
  derived : SB.tensor ⋙ U.mapDerivedCategory ≅
    (U.mapDerivedCategory.prod U.mapDerivedCategory) ⋙ SA.tensor
  /-- The extension agrees with the total comparison on all flat-term K-flat models. -/
  representative : RepresentativeModel.{c, v, r, d, vd, s, wb, wa}
    J R J' R' U SB TB SA TA chain derived.hom
  /-- μ preserves units, associators and the specified signed symmetry. -/
  coherence : TensorCoherence SB.monoidal SA.monoidal βB βA U.mapDerivedCategory derived
  /-- Its unit is the localization of the given underived unit comparison. -/
  unit_normalization :
    coherence.unit.hom ≫ cA.unitIso.hom =
      U.mapDerivedCategory.map cB.unitIso.hom ≫
        U.mapDerivedCategoryFactors.hom.app (ringedTensorUnitComplex.{c, v, r} J R) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app
            (SheafOfModules.unit
              ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).map (u.coherence.unit).hom)
  /-- These are the specified, evaluation-normalized adjunction equations. -/
  transposition : TranspositionLaws
    (derivedInternalHomOfUniverses.{c, v, r, wb} J R)
    (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R')
    SB SA βB βA U.mapDerivedCategory χ.derived derived

end Sites
end CategoryTheory.RingedForgetTensorTransposition

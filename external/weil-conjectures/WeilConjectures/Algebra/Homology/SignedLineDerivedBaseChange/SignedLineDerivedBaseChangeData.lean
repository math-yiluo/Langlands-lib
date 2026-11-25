/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarPullbackSquare
public import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Pullback

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement

public import WeilConjectures.CategoryTheory.RingedSiteModules

/-! # Signed line comparisons on unbounded derived categories

Source: Stacks Project, Tags 03EL, 0GMX, 0FNY and 07A4; the current blueprint,
Powers and duals in lemma-inverse-image-coefficient-sheaves--2.
(blueprint: def-pur-signed-line-derived-action-data)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option Elab.async false
set_option genInjectivity false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
  CategoryTheory.Functor.preservesZeroMorphisms_of_additive
universe u v w z

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace SheafOfModules.SignedLineDerivedBaseChange

attribute [local irreducible] siteDerivedTensorIndependentCoefficients
  KFlatFixedTensor.representativeIso siteSheafTensorRight
  siteSheafTensorSecondMap siteSheafTensorTmul
  monoidalCategory

set_option allowUnsafeReducibility true in
attribute [local irreducible] KFlatFixedTensor.derivedTensor
  KFlatFixedTensor.selectedTensorPresentation
  KFlatFixedTensor.selectedResolvingTensorPresentation

attribute [local instance 2000] KFlatFixedTensor.tensorAdditive
  KFlatFixedTensor.tensorObjAdditive KFlatFixedTensor.tensorHasMapBifunctor

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}]
  {R : Sheaf J CommRingCat.{max u v w}}
  {S : Sheaf K CommRingCat.{max u v w}}

/-- The existing module pullback; its unit is insertion into the sheafified relative tensor.
Source: Stacks 03D7 and 03EL (blueprint: def-pur-signed-line-derived-action-data). -/
abbrev pull
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)) :=
  ringedSitePullbackFunctor a (module_pushforward_isRightAdjoint_of_universes a)

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint

/-- Signed functoriality in a line isomorphism, using the recorded powers and internal Hom.
The negative map is precomposition with the inverse positive map.
Source: Stacks 03EL, 0GMX (blueprint: def-pur-signed-line-derived-action-data). -/
def signedIsoHom {A : Sheaf J CommRingCat.{max u v w}}
    {P Q : KFlatFixedTensor.Modules A} (b : P ≅ Q) :
    ∀ d : ℤ, signedLinePower.{u, v, w} P d ⟶ signedLinePower.{u, v, w} Q d
  | .ofNat n => scalarTensorPowerMap A b.hom n
  | .negSucc n => homObjMap (scalarTensorPowerMap A b.inv (n + 1)) (𝟙 (unit _))

/-- The published derived tensor with the line in degree zero.
Source: Stacks 06YU (blueprint: def-pur-signed-line-derived-action-data). -/
def derivedLine (A : Sheaf J CommRingCat.{max u v w})
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules A)]
    (L : KFlatFixedTensor.Modules A) :
    DerivedCategory (KFlatFixedTensor.Modules A) ⥤ DerivedCategory (KFlatFixedTensor.Modules A) :=
  (KFlatFixedTensor.derivedTensor.{u, v, max u v w, z} A).flip.obj
    (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules A) 0).obj L))

attribute [local irreducible] derivedLine Functor.mapDerivedCategory

/-- Termwise tensor with a fixed sheaf, with its zero-preservation instance fixed once.
Source: Stacks 03EK and 06YU
(blueprint: def-pur-signed-line-derived-action-data). -/
def complexLine (A : Sheaf J CommRingCat.{max u v w})
    (L : KFlatFixedTensor.Modules A) :
    CochainComplex (KFlatFixedTensor.Modules A) ℤ ⥤
      CochainComplex (KFlatFixedTensor.Modules A) ℤ :=
  (siteSheafTensorRight L).mapHomologicalComplex (.up ℤ)

/-- The actual total-complex collapse, followed by the existing comparison with site tensor.
Source: Stacks 06YU (blueprint: def-pur-signed-line-derived-action-data). -/
def collapse (A : Sheaf J CommRingCat.{max u v w})
    (L : KFlatFixedTensor.Modules A) :
    (KFlatFixedTensor.totalTensor A).flip.obj
        ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules A) 0).obj L) ≅
      (siteSheafTensorRight (A := A) L).mapHomologicalComplex (.up ℤ) :=
  CochainComplex.map₂HomologicalComplexFlipObjSingleIso
      (KFlatFixedTensor.ordinaryTensor A) L ≪≫
    NatIso.mapHomologicalComplex ((siteSheafTensorRightIso A L).symm) (.up ℤ)

attribute [local irreducible] collapse

/-- Agreement with the actual K-flat total-tensor comparison on resolving complexes.
Source: Stacks 06YU (blueprint: def-pur-signed-line-derived-action-data). -/
def ResolvingNormalization (A : Sheaf J CommRingCat.{max u v w})
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules A)]
    (L : KFlatFixedTensor.Modules A)
    (hL : CochainComplex.IsKFlatIndependentCoefficients
      ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules A) 0).obj L))
    (hLf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := A)
      (((CochainComplex.singleFunctor (KFlatFixedTensor.Modules A) 0).obj L).X i))
    (c : DerivedCategory.Q ⋙ derivedLine.{u, v, w, z} A L ≅
      (siteSheafTensorRight L).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) : Prop :=
  ∀ (E : CochainComplex (KFlatFixedTensor.Modules A) ℤ)
    (hE : CochainComplex.IsKFlatIndependentCoefficients E)
    (hf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := A) (E.X i)),
    HEq (c.hom.app E ≫ DerivedCategory.Q.map ((collapse A L).inv.app E))
      (KFlatFixedTensor.representativeIso A E
        ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules A) 0).obj L)
          hE hL hf hLf).inv

attribute [local irreducible] ResolvingNormalization

/-- The two localization comparisons and the derived action isomorphism, as ordinary
product data. Their canonicity is specified by DerivedAction, never chosen from existence.
Source: Stacks 06YU, 07A4 (blueprint: def-pur-signed-line-derived-action-data). -/
structure DerivedActionData
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules R)]
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules S)]
    (F : KFlatFixedTensor.Modules R ⥤ KFlatFixedTensor.Modules S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : KFlatFixedTensor.Modules R) (M : KFlatFixedTensor.Modules S) where
  fst : DerivedCategory.Q ⋙ derivedLine.{u, v, w, z} R L ≅
    (siteSheafTensorRight L).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  snd : (DerivedCategory.Q ⋙ derivedLine.{u, v, w, z} S M ≅
    (siteSheafTensorRight M).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ×
    (derivedLine.{u, v, w, z} R L ⋙ F.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ derivedLine.{u, v, w, z} S M)

/-- The termwise square required of a derived action.
Source: Stacks 07A4 (blueprint: def-pur-signed-line-derived-action-data). -/
def DerivedActionSquare
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules R)]
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules S)]
    (F : KFlatFixedTensor.Modules R ⥤ KFlatFixedTensor.Modules S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : KFlatFixedTensor.Modules R) (M : KFlatFixedTensor.Modules S)
    (γ : siteSheafTensorRight L ⋙ F ≅ F ⋙ siteSheafTensorRight M)
    (b : DerivedActionData.{u, v, w, z} F L M) : Prop :=
  ∀ E : CochainComplex (KFlatFixedTensor.Modules R) ℤ,
    HEq (b.2.2.hom.app (DerivedCategory.Q.obj E) ≫
      (derivedLine.{u, v, w, z} S M).map (F.mapDerivedCategoryFactors.hom.app E) ≫
      b.2.1.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj E))
      (F.mapDerivedCategory.map (b.1.hom.app E) ≫
        F.mapDerivedCategoryFactors.hom.app
          (((siteSheafTensorRight L).mapHomologicalComplex (.up ℤ)).obj E) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex γ (.up ℤ)).hom.app E))

/-- The uniqueness clause for a derived action, with the same displayed type.
Source: Stacks 07A4 (blueprint: def-pur-signed-line-derived-action-data). -/
def DerivedActionUnique
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules R)]
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules S)]
    (F : KFlatFixedTensor.Modules R ⥤ KFlatFixedTensor.Modules S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : KFlatFixedTensor.Modules R) (M : KFlatFixedTensor.Modules S)
    (γ : siteSheafTensorRight L ⋙ F ≅ F ⋙ siteSheafTensorRight M)
    (b : DerivedActionData.{u, v, w, z} F L M) : Prop :=
  ∀ η : derivedLine.{u, v, w, z} R L ⋙ F.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ derivedLine.{u, v, w, z} S M,
    (∀ E : CochainComplex (KFlatFixedTensor.Modules R) ℤ,
      HEq (η.hom.app (DerivedCategory.Q.obj E) ≫
          (derivedLine.{u, v, w, z} S M).map (F.mapDerivedCategoryFactors.hom.app E) ≫
          b.2.1.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj E))
        (F.mapDerivedCategory.map (b.1.hom.app E) ≫
          F.mapDerivedCategoryFactors.hom.app
            (((siteSheafTensorRight L).mapHomologicalComplex (.up ℤ)).obj E) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex γ (.up ℤ)).hom.app E))) →
        η = b.2.2

/-- A derived action pinned on every complex by the ordinary tensor comparison.
The resolving comparisons are the published ones, including their collapse to one-term
line factors. Source: Stacks 06YU, 07A4 and 015F
(blueprint: def-pur-signed-line-derived-action-data). -/
def DerivedAction
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules R)]
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules S)]
    (F : KFlatFixedTensor.Modules R ⥤ KFlatFixedTensor.Modules S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : KFlatFixedTensor.Modules R) (M : KFlatFixedTensor.Modules S)
    (γ : siteSheafTensorRight L ⋙ F ≅ F ⋙ siteSheafTensorRight M)
    (b : DerivedActionData F L M) : Prop :=
  ∃ hL : CochainComplex.IsKFlatIndependentCoefficients
    ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules R) 0).obj L),
  ∃ hM : CochainComplex.IsKFlatIndependentCoefficients
    ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules S) 0).obj M),
  ∃ hLf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R)
    (((CochainComplex.singleFunctor (KFlatFixedTensor.Modules R) 0).obj L).X i),
  ∃ hMf : ∀ i : ℤ, IsFlatOnSite (J := K) (R := S)
    (((CochainComplex.singleFunctor (KFlatFixedTensor.Modules S) 0).obj M).X i),
    ResolvingNormalization R L hL hLf b.1 ∧
    ResolvingNormalization S M hM hMf b.2.1 ∧
    DerivedActionSquare F L M γ b ∧
    DerivedActionUnique F L M γ b

attribute [local irreducible] DerivedAction

/-- Canonical ordinary unit, positive associators and evaluations of signed powers.
Source: Stacks 03EL and 0FNY.
(blueprint: def-pur-signed-line-ordinary-constraint-data). -/
def OrdinaryLineConstraints (A : Sheaf J CommRingCat.{max u v w})
    (P : KFlatFixedTensor.Modules A)
    (ordinaryUnit : siteSheafTensorRight (signedLinePower.{u, v, w} P 0) ≅ 𝟭 _)
    (ordinaryProduct : ∀ n : ℕ,
      siteSheafTensorRight (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⋙
        siteSheafTensorRight (signedLinePower.{u, v, w} P 1) ≅
      siteSheafTensorRight (signedLinePower.{u, v, w} P (.ofNat (n + 2))))
    (ordinaryEvaluation : ∀ n : ℕ,
      siteSheafTensorRight (signedLinePower.{u, v, w} P (.negSucc n)) ⋙
        siteSheafTensorRight (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⟶ 𝟭 _) : Prop :=
    (∀ (N : KFlatFixedTensor.Modules A) (V : Cᵒᵖ)
      (x : N.val.obj V) (r : A.obj.obj V),
      (ordinaryUnit.hom.app N).val.app V
        (siteSheafTensorTmul N (signedLinePower.{u, v, w} P 0) V x r) =
          @SMul.smul (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj.obj V)
            (N.val.obj V) inferInstance r x) ∧
    (∀ (n : ℕ) (N : KFlatFixedTensor.Modules A) (V : Cᵒᵖ)
      (x : N.val.obj V) (y : (scalarTensorPower A P (n + 1)).val.obj V)
      (q : P.val.obj V),
      ((ordinaryProduct n).hom.app N).val.app V
        (siteSheafTensorTmul _ P V
          (siteSheafTensorTmul N (scalarTensorPower A P (n + 1)) V x y) q) =
        siteSheafTensorTmul N (scalarTensorPower A P (n + 2)) V x
          (siteSheafTensorTmul (scalarTensorPower A P (n + 1)) P V y q)) ∧
    (∀ (n : ℕ) (N : KFlatFixedTensor.Modules A) (V : Cᵒᵖ)
      (x : N.val.obj V) (φ : (signedLinePower.{u, v, w} P (.negSucc n)).val.obj V)
      (y : (scalarTensorPower A P (n + 1)).val.obj V),
      ((ordinaryEvaluation n).app N).val.app V
        (siteSheafTensorTmul _ (scalarTensorPower A P (n + 1)) V
          (siteSheafTensorTmul N (signedLinePower.{u, v, w} P (.negSucc n)) V x φ) y) =
        @SMul.smul (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj.obj V)
          (N.val.obj V) inferInstance (φ.app (op (Over.mk (𝟙 V.unop))) y) x)

section GenericLineConstraints
universe ga gha gd ghd ge ghe
variable {A₀ : Type ga} [Category.{gha} A₀] [HasZeroMorphisms A₀]
  {D₀ : Type gd} [Category.{ghd} D₀]

/-- Localization-normalized constraints, with the ordinary predicate as a parameter.
Source: Stacks 07A4 (blueprint: def-pur-signed-line-derived-action-data). -/
inductive LocalizedLineConstraints
    (Q : CochainComplex A₀ ℤ ⥤ D₀)
    (r : ℤ → A₀ ⥤ A₀) [∀ i, (r i).PreservesZeroMorphisms]
    (d : ℤ → D₀ ⥤ D₀)
    (ordinary : (r 0 ≅ 𝟭 _) →
      (∀ n : ℕ, r (.ofNat (n + 1)) ⋙ r 1 ≅ r (.ofNat (n + 2))) →
      (∀ n : ℕ, r (.negSucc n) ⋙ r (.ofNat (n + 1)) ⟶ 𝟭 _) → Prop)
    (c : ∀ i, Q ⋙ d i ≅ (r i).mapHomologicalComplex (.up ℤ) ⋙ Q)
    (u : d 0 ≅ 𝟭 _)
    (p : ∀ n : ℕ, d (.ofNat (n + 1)) ⋙ d 1 ≅ d (.ofNat (n + 2)))
    (e : ∀ n : ℕ, d (.negSucc n) ⋙ d (.ofNat (n + 1)) ⟶ 𝟭 _) : Prop
  | mk
    (ou : r 0 ≅ 𝟭 _)
    (op : ∀ n : ℕ, r (.ofNat (n + 1)) ⋙ r 1 ≅ r (.ofNat (n + 2)))
    (oe : ∀ n : ℕ, r (.negSucc n) ⋙ r (.ofNat (n + 1)) ⟶ 𝟭 _)
    (ho : ordinary ou op oe)
    (hu : ∀ E, HEq (u.hom.app (Q.obj E))
      ((c 0).hom.app E ≫ Q.map ((NatIso.mapHomologicalComplex ou (.up ℤ)).hom.app E)))
    (hp : ∀ n E, HEq ((p n).hom.app (Q.obj E) ≫ (c (.ofNat (n + 2))).hom.app E)
      ((d 1).map ((c (.ofNat (n + 1))).hom.app E) ≫
        (c 1).hom.app (((r (.ofNat (n + 1))).mapHomologicalComplex (.up ℤ)).obj E) ≫
        Q.map ((NatIso.mapHomologicalComplex (op n) (.up ℤ)).hom.app E)))
    (he : ∀ n E, HEq ((e n).app (Q.obj E))
      ((d (.ofNat (n + 1))).map ((c (.negSucc n)).hom.app E) ≫
        (c (.ofNat (n + 1))).hom.app
          (((r (.negSucc n)).mapHomologicalComplex (.up ℤ)).obj E) ≫
        Q.map ((NatTrans.mapHomologicalComplex (oe n) (.up ℤ)).app E))) :
    LocalizedLineConstraints Q r d ordinary c u p e

variable {E₀ : Type ge} [Category.{ghe} E₀]

/-- The three comparison equations, with the two constraint predicates as parameters.
Source: Stacks 07A4 (blueprint: def-pur-signed-line-derived-action-data). -/
inductive LocalizedLineFamily
    (d : ℤ → D₀ ⥤ D₀) (e : ℤ → E₀ ⥤ E₀) (F : D₀ ⥤ E₀)
    (eta : ∀ i, d i ⋙ F ≅ F ⋙ e i)
    (cr : (d 0 ≅ 𝟭 _) →
      (∀ n : ℕ, d (.ofNat (n + 1)) ⋙ d 1 ≅ d (.ofNat (n + 2))) →
      (∀ n : ℕ, d (.negSucc n) ⋙ d (.ofNat (n + 1)) ⟶ 𝟭 _) → Prop)
    (cs : (e 0 ≅ 𝟭 _) →
      (∀ n : ℕ, e (.ofNat (n + 1)) ⋙ e 1 ≅ e (.ofNat (n + 2))) →
      (∀ n : ℕ, e (.negSucc n) ⋙ e (.ofNat (n + 1)) ⟶ 𝟭 _) → Prop) : Prop
  | mk
    (uR : d 0 ≅ 𝟭 _) (uS : e 0 ≅ 𝟭 _)
    (pR : ∀ n : ℕ, d (.ofNat (n + 1)) ⋙ d 1 ≅ d (.ofNat (n + 2)))
    (pS : ∀ n : ℕ, e (.ofNat (n + 1)) ⋙ e 1 ≅ e (.ofNat (n + 2)))
    (eR : ∀ n : ℕ, d (.negSucc n) ⋙ d (.ofNat (n + 1)) ⟶ 𝟭 _)
    (eS : ∀ n : ℕ, e (.negSucc n) ⋙ e (.ofNat (n + 1)) ⟶ 𝟭 _)
    (hR : cr uR pR eR) (hS : cs uS pS eS)
    (hu : ∀ X, (eta 0).hom.app X ≫ uS.hom.app (F.obj X) = F.map (uR.hom.app X))
    (hp : ∀ n X, F.map ((pR n).hom.app X) ≫ (eta (.ofNat (n + 2))).hom.app X =
      (eta 1).hom.app ((d (.ofNat (n + 1))).obj X) ≫
        (e 1).map ((eta (.ofNat (n + 1))).hom.app X) ≫ (pS n).hom.app (F.obj X))
    (he : ∀ n X, F.map ((eR n).app X) =
      (eta (.ofNat (n + 1))).hom.app ((d (.negSucc n)).obj X) ≫
        (e (.ofNat (n + 1))).map ((eta (.negSucc n)).hom.app X) ≫ (eS n).app (F.obj X)) :
    LocalizedLineFamily d e F eta cr cs

end GenericLineConstraints

/-- Right unit, positive-power associator and negative-positive evaluation constraints.
The ordinary constraints are specified on all local pure tensors. The derived constraints
are specified after localization using c; c itself is fixed by representativeIso and
collapse in DerivedAction. Thus these are the canonical constraints, with no arbitrary
monoidal structure or map selected. The positive constraint is the associator followed
by the one-term identification of the next power, and evaluation contracts the last two
factors. Source: Stacks 03EK, 04TT, 06YU and 07A4
(blueprint: def-pur-signed-line-derived-action-data). -/
def DerivedLineConstraints (A : Sheaf J CommRingCat.{max u v w})
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules A)]
    (P : KFlatFixedTensor.Modules A)
    (c : ∀ d : ℤ, DerivedCategory.Q ⋙ derivedLine.{u, v, w, z} A (signedLinePower.{u, v, w} P d) ≅
      complexLine A (signedLinePower.{u, v, w} P d) ⋙
        DerivedCategory.Q)
    (rightUnitor : derivedLine.{u, v, w, z} A (signedLinePower.{u, v, w} P 0) ≅ 𝟭 _)
    (product : ∀ n : ℕ,
      derivedLine.{u, v, w, z} A (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⋙
          derivedLine.{u, v, w, z} A (signedLinePower.{u, v, w} P 1) ≅
        derivedLine.{u, v, w, z} A (signedLinePower.{u, v, w} P (.ofNat (n + 2))))
    (evaluation : ∀ n : ℕ,
      derivedLine.{u, v, w, z} A (signedLinePower.{u, v, w} P (.negSucc n)) ⋙
        derivedLine.{u, v, w, z} A (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⟶ 𝟭 _) : Prop :=
  LocalizedLineConstraints DerivedCategory.Q
    (fun i ↦ siteSheafTensorRight (signedLinePower.{u, v, w} P i))
    (fun i ↦ derivedLine.{u, v, w, z} A (signedLinePower.{u, v, w} P i))
    (OrdinaryLineConstraints A P) c rightUnitor product evaluation

/-- The simultaneous unit, positive-power and evaluation equations for the same eta family
whose components are fixed in DerivedAction. Source: Stacks 07A4; blueprint Powers and duals
(blueprint: def-pur-signed-line-derived-action-data). -/
def DerivedFamilyCoherence
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules R)]
    [HasDerivedCategory.{z} (KFlatFixedTensor.Modules S)]
    (F : KFlatFixedTensor.Modules R ⥤ KFlatFixedTensor.Modules S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : KFlatFixedTensor.Modules R) (Q : KFlatFixedTensor.Modules S)
    (b : ∀ d : ℤ, DerivedActionData F (signedLinePower.{u, v, w} P d)
      (signedLinePower.{u, v, w} Q d)) : Prop :=
  LocalizedLineFamily
    (fun i ↦ derivedLine.{u, v, w, z} R (signedLinePower.{u, v, w} P i))
    (fun i ↦ derivedLine.{u, v, w, z} S (signedLinePower.{u, v, w} Q i))
    F.mapDerivedCategory (fun i ↦ (b i).2.2)
    (DerivedLineConstraints R P (fun i ↦ (b i).1))
    (DerivedLineConstraints S Q (fun i ↦ (b i).2.1))

variable
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
  (P : KFlatFixedTensor.Modules R) (Q : KFlatFixedTensor.Modules S)
  (t : (pull a).obj P ≅ Q)

/-- Naturality in isomorphisms of the two line data. Negative powers use inverse dual maps.
Source: Stacks 03EL, 0GMX (blueprint: def-pur-signed-line-derived-action-data). -/
def IsoNaturality
    (T : ∀ d : ℤ, (pull a).obj (signedLinePower.{u, v, w} P d) ≅
      signedLinePower.{u, v, w} Q d) : Prop :=
  ∀ (P' : KFlatFixedTensor.Modules R) (Q' : KFlatFixedTensor.Modules S)
    (b : P ≅ P') (c : Q ≅ Q') (t' : (pull a).obj P' ≅ Q')
    (T' : ∀ d : ℤ, (pull a).obj (signedLinePower.{u, v, w} P' d) ≅
      signedLinePower.{u, v, w} Q' d),
    (pull a).map b.hom ≫ t'.hom = t.hom ≫ c.hom →
    SignedLinePullbackNormalized a P' Q' t' T' →
    ∀ d : ℤ, (pull a).map (signedIsoHom b d) ≫ (T' d).hom =
      (T d).hom ≫ signedIsoHom c d

attribute [local irreducible] IsoNaturality

/-- Naturality in arbitrary coefficient extensions compatible with the structural isomorphism.
The existing scalar-power identifications and scalar/pullback square specify the canonical
balanced-tensor comparison; no arbitrary comparison is assumed. Degree-one compatibility
is exactly the assertion that t' is induced from t. No flatness of either ring map occurs.
Source: Stacks 03EL, 0GMX, 0FNY
(blueprint: def-pur-signed-line-derived-action-data). -/
def ScalarNaturality
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [∀ V : D, (K.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (rInv : Sheaf J RingCat.{max u v w} ⥤ Sheaf K RingCat.{max u v w})
    (rAdj : rInv ⊣ U.sheafPushforwardContinuous RingCat J K)
    (T : ∀ d : ℤ, (pull a).obj (signedLinePower.{u, v, w} P d) ≅
      signedLinePower.{u, v, w} Q d) : Prop :=
  ∀ (R' : Sheaf J CommRingCat.{max u v w})
    (S' : Sheaf K CommRingCat.{max u v w}) (α : R ⟶ R') (β : S ⟶ S')
    (a' : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R' ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S')),
    IsIso ((rAdj.homEquiv _ _).symm a') →
    (sheafCompose J (forget₂ CommRingCat RingCat)).map α ≫ a' =
      a ≫ (U.sheafPushforwardContinuous RingCat J K).map
        ((sheafCompose K (forget₂ CommRingCat RingCat)).map β) →
    ∀ (t' : (pull a').obj (changeOfRingsOfUniverses α P) ≅ changeOfRingsOfUniverses β Q)
      (T' : ∀ d : ℤ,
        (pull a').obj (signedLinePower.{u, v, w} (changeOfRingsOfUniverses α P) d) ≅
          signedLinePower.{u, v, w} (changeOfRingsOfUniverses β Q) d)
      (B : ∀ d : ℤ, changeOfRingsOfUniverses α (signedLinePower.{u, v, w} P d) ≅
        signedLinePower.{u, v, w} (changeOfRingsOfUniverses α P) d)
      (E : ∀ d : ℤ, changeOfRingsOfUniverses β (signedLinePower.{u, v, w} Q d) ≅
        signedLinePower.{u, v, w} (changeOfRingsOfUniverses β Q) d),
      SignedLinePullbackNormalized a' _ _ t' T' →
      SignedLineComparisonNormalized α P _ (Iso.refl _) B →
      SignedLineComparisonNormalized β Q _ (Iso.refl _) E →
      SignedLineScalarPullbackSquare α β a a' P _ Q _
        (Iso.refl _) (Iso.refl _) t t' →
      ∀ d : ℤ, SignedLineScalarPullbackSquare α β a a'
        (signedLinePower.{u, v, w} P d)
        (signedLinePower.{u, v, w} (changeOfRingsOfUniverses α P) d)
        (signedLinePower.{u, v, w} Q d)
        (signedLinePower.{u, v, w} (changeOfRingsOfUniverses β Q) d)
        (B d) (E d) (T d) (T' d)

attribute [local irreducible] ScalarNaturality

end SheafOfModules.SignedLineDerivedBaseChange

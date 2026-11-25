/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import Mathlib.CategoryTheory.Sites.Point.IsMonoidalW
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.CategoryTheory.Ringed.RingedProEtaleTorAmplitudeOfUniverses
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal

import WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars
import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionProjectionIso
import WeilConjectures.AlgebraicGeometry.SupportedConstructibleOriginComparison.SupportedConstructibleOriginComparison
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormulaBounded
import all WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor

/-! # Bounded etale origin of an open-supported coefficient tensor

Source: blueprint main-20261015, `sk-lem-sp-reduction-direct-image.proof.md`, Step 1;
Stacks Tags 09AK, 09AL, 09AF, 07A4, 08FZ, 0GL1, 099T
(blueprint: lem-sp-supported-etale-tensor-origin).

The small-site fixed-module presentation uses ULift of the finite coefficient ring.
The Tor hypothesis and the scalar-extension target use the recorded intrinsic realization.
All displayed identifications below are actual composites of canonical comparisons,
including the section-normalized realization square and adjunction mates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u c₁ c₂ c₃ c₄ h₁ h₂ h₃ h₄ d₁ d₂ d₃ d₄
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale
namespace SupportedEtaleTensorOrigin

attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints

/-- A reduction boundary for the published exact square descent. Its data is exactly
that descent; the boundary prevents repeated unfolding of derived localizations.
Source: Stacks 010N (blueprint: lem-sp-supported-etale-tensor-origin). -/
@[irreducible] def exactSquare
    {C₁ : Type c₁} {C₂ : Type c₂} {C₃ : Type c₃} {C₄ : Type c₄}
    [Category.{h₁} C₁] [Category.{h₂} C₂] [Category.{h₃} C₃] [Category.{h₄} C₄]
    [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
    [HasDerivedCategory.{d₁} C₁] [HasDerivedCategory.{d₂} C₂]
    [HasDerivedCategory.{d₃} C₃] [HasDerivedCategory.{d₄} C₄]
    {F₁ : C₁ ⥤ C₂} {F₂ : C₂ ⥤ C₄} {G₁ : C₁ ⥤ C₃} {G₂ : C₃ ⥤ C₄}
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) :
    F₁.mapDerivedCategory ⋙ F₂.mapDerivedCategory ≅
      G₁.mapDerivedCategory ⋙ G₂.mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso e

/-- The prescribed coefficient-universe lift.
Source: Stacks 00YV (blueprint: lem-sp-supported-etale-tensor-origin). -/
abbrev liftedHom {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    ULift.{u + 1, u} A →+* ULift.{u + 1, u} B := f.ulift

/-- Exact scalar restriction on the actual small pro-etale site.
Source: Stacks 03DA (blueprint: lem-sp-supported-etale-tensor-origin). -/
abbrev fixedRestriction {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) :=
  @Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology T)
    (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance (liftedHom f)

/-- The fixed-module presentation of the recorded scalar extension.
Source: Stacks 06YY (blueprint: lem-sp-supported-etale-tensor-origin). -/
abbrev fixedScalar {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) :=
  @pbcFixedScalarExtension.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology T)
    (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance (liftedHom f)

/-- The derived realization square for restriction of scalars, with its prescribed
identity on scalar-unit sections. Source: Stacks 00YV and 03DA
(blueprint: lem-sp-supported-etale-tensor-origin). -/
@[irreducible] def restrictionPresentation
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) :
    (sfIntrinsicDerivedEquivalence T B).functor ⋙ scalarRestriction f T ≅
      fixedRestriction f T ⋙
        (sfIntrinsicDerivedEquivalence T A).functor :=
  exactSquare (sfRealizationRestriction T f)

/-- The scalar presentation is the left-adjoint uniqueness comparison determined by
restrictionPresentation, hence by identity on the scalar-unit sections. No arbitrary
isomorphism of scalar functors is chosen. Source: Stacks 00YV and 06YY
(blueprint: lem-sp-supported-etale-tensor-origin). -/
@[irreducible] def scalarPresentation {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) :
    (sfIntrinsicDerivedEquivalence T A).functor ⋙ scalarExtensionFunctor f T ≅
      fixedScalar f T ⋙ (sfIntrinsicDerivedEquivalence T B).functor :=
  let e := restrictionPresentation f T
  let rightIso :=
    isoWhiskerRight (sfIntrinsicDerivedEquivalence T B).counitIso.symm
      (scalarRestriction f T ⋙ (sfIntrinsicDerivedEquivalence T A).inverse) ≪≫
    isoWhiskerLeft (sfIntrinsicDerivedEquivalence T B).inverse
      (isoWhiskerRight e (sfIntrinsicDerivedEquivalence T A).inverse) ≪≫
    isoWhiskerLeft
      ((sfIntrinsicDerivedEquivalence T B).inverse ⋙
        fixedRestriction f T)
      (sfIntrinsicDerivedEquivalence T A).unitIso.symm
  (((sfIntrinsicDerivedEquivalence T A).toAdjunction.comp
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) f))).ofNatIsoRight
      rightIso).leftAdjointUniq
    ((Adjunction.ofIsRightAdjoint
      (fixedRestriction f T)).comp
        (sfIntrinsicDerivedEquivalence T B).toAdjunction)

/-- Cancel the realization unit in extension by zero, then descend the exact sheaf
square termwise. Source: Stacks 00YV and 03DI
(blueprint: lem-sp-supported-etale-tensor-origin). -/
@[irreducible] def openPresentation (A : Type u) [CommRing A] [Finite A]
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :
    (sfIntrinsicDerivedEquivalence U A).functor ⋙
        (sfIntrinsicExtensionByZero j A).mapDerivedCategory ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence Z A).functor :=
  mapDerivedCategoryCompIso _ _ ≪≫
    mapDerivedCategoryNatIso
      ((sfIntrinsicModuleEquivalence U A).funInvIdAssoc
        (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
          (sfIntrinsicModuleEquivalence Z A).functor)) ≪≫
    (mapDerivedCategoryCompIso _ _).symm

/-- The exact, uncompleted comparison in fixed coefficients.
Source: Stacks 099T (blueprint: lem-sp-supported-etale-tensor-origin). -/
abbrev comparison (A : Type u) [CommRing A] (T : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).mapDerivedCategory

/-- The open-supported etale complex K.
Source: Stacks 03DI (blueprint: lem-sp-supported-etale-tensor-origin). -/
abbrev etaleOpen (A : Type u) [CommRing A]
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :=
  (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory

/-- The fixed-module coordinates of the recorded pro-etale extension by zero N.
Source: Stacks 03DI and 00YV (blueprint: lem-sp-supported-etale-tensor-origin). -/
abbrev proOpen (A : Type u) [CommRing A]
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory

/-- The natural open comparison, descended termwise before taking a component.
Source: Stacks 09AF (blueprint: lem-sp-supported-etale-tensor-origin). -/
@[irreducible] def openComparison (A : Type u) [CommRing A]
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :
    etaleOpen A j ⋙ comparison A Z ≅ comparison A U ⋙ proOpen A j :=
  exactSquare
    (openImmersionLowerShriekComparisonUpperStarIso
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)

/-- The canonical identification nu K with N relative to the chosen origin e.
Source: Stacks 09AF (blueprint: lem-sp-supported-etale-tensor-origin). -/
@[irreducible] def supportedComparison (A : Type u) [CommRing A]
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (L : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) U)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology U)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (e : (comparison A U).obj L ≅ M) :
    (comparison A Z).obj ((etaleOpen A j).obj L) ≅ (proOpen A j).obj M :=
  (openComparison A j).app L ≪≫ (proOpen A j).mapIso e

/-- Scalar extension with the actual small-site universes specified.
Source: Stacks 06YY (blueprint: lem-sp-supported-etale-tensor-origin). -/
abbrev proFixedScalar {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) :=
  @pbcFixedScalarExtension.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology T) A B
    inferInstance inferInstance f

/-- Derived restriction with the actual small-site universes specified.
Source: Stacks 03DA (blueprint: lem-sp-supported-etale-tensor-origin). -/
abbrev proFixedRestriction {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) :=
  @Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology T) A B
    inferInstance inferInstance f

/-- B as an A-module sheaf, using actual exact restriction of scalars.
Source: Stacks 03EK (blueprint: lem-sp-supported-etale-tensor-origin). -/
def proScalarCoefficientSheaf
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) :=
  (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).obj
    (𝟙_ (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} B)))

/-- The ordinary balancing map M tensor_A B to the restricted scalar extension.
It is scalar unit, followed by the lax tensorator of restriction and the right unitor.
Source: Stacks 03EK (blueprint: lem-sp-supported-etale-tensor-origin). -/
def proScalarSheafTensorMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) :
    M ⊗ proScalarCoefficientSheaf φ T ⟶
      (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).obj
        ((ProEtale.sheafExtendScalars φ T).obj M) :=
  (ProEtale.sheafExtendScalarsAdjunction φ T).unit.app M ▷
      proScalarCoefficientSheaf φ T ≫
    Functor.LaxMonoidal.μ (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ)
      ((ProEtale.sheafExtendScalars φ T).obj M) (𝟙_ _) ≫
    (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).map (ρ_ _).hom

/-- Naturality of the balancing map.
Source: Stacks 03EK (blueprint: lem-sp-supported-etale-tensor-origin).
Proof: apply naturality of the scalar unit, the lax tensorator, and the right unitor.
On sections this is (m tensor b) maps to b tensor a(m). -/
theorem proScalarSheafTensorMap_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    {M N : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)} (a : M ⟶ N) :
    a ▷ proScalarCoefficientSheaf φ T ≫ proScalarSheafTensorMap φ T N =
      proScalarSheafTensorMap φ T M ≫
        (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).map
          ((ProEtale.sheafExtendScalars φ T).map a) := by
  exact AlgebraicGeometry.Etale.balancing_naturality (ProEtale.sheafExtendScalarsAdjunction φ T) a

/-- The ordinary balancing map, as a natural transformation.
Source: Stacks 03EK (blueprint: lem-sp-supported-etale-tensor-origin). -/
def proScalarSheafTensorTransformation
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    tensorRight (proScalarCoefficientSheaf φ T) ⟶
      ProEtale.sheafExtendScalars φ T ⋙ Sheaf.restrictScalars (Scheme.ProEt.topology T) φ where
  app := proScalarSheafTensorMap φ T
  naturality _ _ a := proScalarSheafTensorMap_naturality φ T a

/-- The derived-extension counit on a cochain representative, including the quotient factor.
Source: Stacks 06YY (blueprint: lem-sp-supported-etale-tensor-origin). -/
def proScalarExtensionRepresentative
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ) :
    (proFixedScalar φ T).obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj
        (((ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P) :=
  ((Adjunction.ofIsRightAdjoint
      (proFixedRestriction φ T)).homEquiv _ _).symm
    (_root_.DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
          (NatTrans.mapHomologicalComplex
            (ProEtale.sheafExtendScalarsAdjunction φ T).unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (ProEtale.sheafExtendScalars φ T ⋙
              Sheaf.restrictScalars (Scheme.ProEt.topology T) φ)) (.up ℤ)).inv.app P) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).mapDerivedCategoryFactors.inv.app
        (((ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P))

attribute [local irreducible] Functor.leftAdjoint Adjunction.ofIsRightAdjoint
  proScalarCoefficientSheaf proScalarSheafTensorTransformation

set_option backward.isDefEq.respectTransparency.types false in
/-- H is the tensor in the ordinary uncompleted etale derived category; B has its
specified A-action. Source: Stacks 07A4
(blueprint: lem-sp-supported-etale-tensor-origin). -/
abbrev etaleTensor {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (L : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) U) :=
  ((Etale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Z).obj
    ((etaleOpen A j).obj L)).obj (Etale.scalarCoefficient (liftedHom f) Z)

end SupportedEtaleTensorOrigin
end AlgebraicGeometry.ProEtale

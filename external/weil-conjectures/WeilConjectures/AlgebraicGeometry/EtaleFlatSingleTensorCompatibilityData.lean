/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-! # Data for tensor compatibility of degree-zero etale sheaves

Source: Stacks Project, Cohomology, Tags 06YQ and 06YU.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u uB
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local instance] SymmetricCategory.toBraidedCategory
attribute [local instance] sheafMonoidalCategory sheafBraidedCategory sheafMonoidalClosed

variable {B : Type uB} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  {X X' : AlgebraicGeometry.Scheme.{u}}

/-- The canonical degree-zero derived pairing computed on a flat left factor.
Source: Stacks Tag 06YQ; (auxiliary; not a blueprint node).
This explicit result type uses the same derived tensor bifunctor as its consumers. -/
@[irreducible]
noncomputable def singleFunctorFlatPairing
    (L M N : Sheaf X.smallEtaleTopology B) (hL : ObjectProperty.flat L)
    (f : L ⊗ M ⟶ N) :
    ((derivedTensor B X).obj ((DerivedCategory.singleFunctor _ 0).obj L)).obj
      ((DerivedCategory.singleFunctor _ 0).obj M) ⟶
        (DerivedCategory.singleFunctor _ 0).obj N :=
  (singleFunctorObjTensorIso (A := B) (X := X) L M hL).hom ≫
    (DerivedCategory.singleFunctor _ 0).map f

/-- Apply an ordinary pullback arrow after the canonical single/pullback comparison.
Source: Stacks Tag 06YQ;
(auxiliary; not a blueprint node).
No resolution or inverse-image comparison is chosen here. -/
noncomputable def singleFunctorPullbackMap (v : X' ⟶ X)
    {L : Sheaf X.smallEtaleTopology B} {L' : Sheaf X'.smallEtaleTopology B}
    (f : (upperStar B v).obj L ⟶ L') :
    (upperStar B v).leftDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj L) ⟶
      (DerivedCategory.singleFunctor _ 0).obj L' :=
  (singleFunctorCompLeftDerivedUpperStarIso B v).hom.app L ≫
    (DerivedCategory.singleFunctor _ 0).map f

/-- The equations expressing the tensor compatibility of flat degree-zero models.
Source: Stacks Tags 06YQ and 06YU;
(auxiliary; not a blueprint node).
The support sheaves and all ordinary multiplication or support maps are arbitrary inputs. -/
structure EtaleFlatSingleTensorCompatibility (v : X' ⟶ X)
    [(upperStar B v).PreservesFlat] : Prop where
  associativity {L M N P Q R T : Sheaf X.smallEtaleTopology B}
      (hL : ObjectProperty.flat L) (hM : ObjectProperty.flat M)
      (hP : ObjectProperty.flat P)
      (f : L ⊗ M ⟶ P) (g : P ⊗ N ⟶ R) (h : M ⊗ N ⟶ Q)
      (k : L ⊗ Q ⟶ T) (a : R ⟶ T)
      (w : f ▷ N ≫ g ≫ a = (α_ L M N).hom ≫ L ◁ h ≫ k) :
      ((derivedTensor B X).map (singleFunctorFlatPairing L M P hL f)).app
          ((DerivedCategory.singleFunctor _ 0).obj N) ≫
        singleFunctorFlatPairing P N R hP g ≫ (DerivedCategory.singleFunctor _ 0).map a =
      (derivedTensorAssociator B X _ _ _).hom ≫
        ((derivedTensor B X).obj ((DerivedCategory.singleFunctor _ 0).obj L)).map
          (singleFunctorFlatPairing M N Q hM h) ≫ singleFunctorFlatPairing L Q T hL k
  symmetry {L M P Q : Sheaf X.smallEtaleTopology B}
      (hL : ObjectProperty.flat L) (hM : ObjectProperty.flat M)
      (f : L ⊗ M ⟶ P) (g : M ⊗ L ⟶ Q) (a : Q ⟶ P)
      (w : (β_ L M).hom ≫ g ≫ a = f) :
      (((derivedTensorSymmetry B X).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj L)).app
          ((DerivedCategory.singleFunctor _ 0).obj M)) ≫
        singleFunctorFlatPairing M L Q hM g ≫ (DerivedCategory.singleFunctor _ 0).map a =
          singleFunctorFlatPairing L M P hL f
  pullback {L M N : Sheaf X.smallEtaleTopology B}
      {L' M' N' : Sheaf X'.smallEtaleTopology B}
      (hL : ObjectProperty.flat L) (hL' : ObjectProperty.flat L')
      (f : L ⊗ M ⟶ N) (g : L' ⊗ M' ⟶ N')
      (b : (upperStar B v).obj L ⟶ L') (c : (upperStar B v).obj M ⟶ M')
      (d : (upperStar B v).obj N ⟶ N')
      (w : (upperStar B v).map f ≫ d =
        Functor.OplaxMonoidal.δ (upperStar B v) L M ≫ (b ⊗ₘ c) ≫ g) :
      (upperStar B v).leftDerivedFunctor.map (singleFunctorFlatPairing L M N hL f) ≫
          (singleFunctorCompLeftDerivedUpperStarIso B v).hom.app N ≫
            (DerivedCategory.singleFunctor _ 0).map d =
        ((leftDerivedUpperStarTensorComparison B v).app
            ((DerivedCategory.singleFunctor _ 0).obj L)).app
            ((DerivedCategory.singleFunctor _ 0).obj M) ≫
          ((derivedTensor B X').map
            ((singleFunctorCompLeftDerivedUpperStarIso B v).hom.app L ≫
              (DerivedCategory.singleFunctor _ 0).map b)).app _ ≫
          ((derivedTensor B X').obj _).map
            ((singleFunctorCompLeftDerivedUpperStarIso B v).hom.app M ≫
              (DerivedCategory.singleFunctor _ 0).map c) ≫
          singleFunctorFlatPairing L' M' N' hL' g

end AlgebraicGeometry.Etale

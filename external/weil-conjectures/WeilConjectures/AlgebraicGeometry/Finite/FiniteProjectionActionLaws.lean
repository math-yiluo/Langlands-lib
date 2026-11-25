/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal

/-!
# Tensor-action and open-counit identities for finite-level projection maps

Source: blueprint chap-Smooth-purity, prose-09-16, expanded Step 6;
Stacks Project Tags 0B56, 0E8I and 0GL1
(blueprint: lem-pur-finite-projection-action-laws).

The eight statements give the proper, open, open-counit and chosen-compactification
identities on each of the pro-etale and ordinary etale sites. All projection maps are
actual canonical maps, with no invertibility, boundedness or constructibility assumption.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

private theorem projection_counit
    {C D : Type*} [Category C] [Category D]
    {J : C ⥤ D} {Q : D ⥤ C} (adj : J ⊣ Q)
    (S : D ⥤ C) (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
    (δ : (((Functor.whiskeringLeft₂ C).obj Q).obj S).obj T ⟶
      (Functor.postcompose₂.obj Q).obj T') (F N : D) :
    J.map ((δ.app F).app N) ≫ adj.counit.app ((T'.obj F).obj N) =
      ((adj.projectionMap S T T' δ).app (Q.obj F)).app N ≫
        (T'.map (adj.counit.app F)).app N := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  have hp := adj.unit_app_comp_map_projectionMap_app_app S T T' δ (Q.obj F) N
  dsimp [Adjunction.projectionMapTranspose] at hp
  rw [adj.homEquiv_unit, adj.homEquiv_unit]
  change (δ.app F).app N ≫ adj.unit.app (Q.obj ((T'.obj F).obj N)) ≫
      Q.map (adj.counit.app _) =
    (adj.unit.app ((T.obj (Q.obj F)).obj (S.obj N)) ≫
      Q.map (((adj.projectionMap S T T' δ).app (Q.obj F)).app N)) ≫
        Q.map ((T'.map (adj.counit.app F)).app N)
  rw [hp]
  have hn := congr_app (δ.naturality (adj.counit.app F)) N
  dsimp at hn
  rw [Category.assoc, ← hn, ← NatTrans.comp_app_assoc, ← T.map_comp]
  simp

namespace CategoryTheory.Functor
open _root_.DerivedCategory LaxMonoidal OplaxMonoidal
variable {C : Type*} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [BraidedCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type*} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [BraidedCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
end CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

/-- Finiteness of the lifted positive-level quotient used in the projection identities.
Source: the finite coefficient convention and coefficient-extension finiteness
(blueprint: lem-pur-finite-projection-action-laws). -/
noncomputable instance projectionAction_coefficientFinite (P : PurityFiniteSetting.{u}) :
    Finite P.Coefficient :=
  @Finite.of_equiv P.Coefficient P.Ring
    (Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos)
    Equiv.ulift.symm

end WeilConjectures.PurityFiniteSetting

namespace AlgebraicGeometry.ProEtale

/-- The canonical reassociation of the derived tensor bifunctor, exposed before
specializing the coefficient category to avoid comparing two monoidal instance terms.
Source: Stacks Tag 0FPT, reassociation on total tensors
(blueprint: lem-pur-finite-projection-action-laws). -/
noncomputable def projectionActionAssociator
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u}) (K M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B)) :
    ((derivedTensor B X).obj (((derivedTensor B X).obj K).obj M)).obj N ≅
      ((derivedTensor B X).obj K).obj (((derivedTensor B X).obj M).obj N) :=
  α_ K M N

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
  AlgebraicGeometry.Etale.sheafBraidedCategory

section ActionTensor

variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A] {Z Y : Scheme.{u}} (g : Z ⟶ Y)

open DerivedCategory Functor.LaxMonoidal Functor.OplaxMonoidal

attribute [local instance] isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar
  isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor

end ActionTensor

section ActionComposition

variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A] {T S R : Scheme.{u}} (i : T ⟶ S) (g : S ⟶ R)

end ActionComposition

section ActionOpen

variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

open Functor.LaxMonoidal

end ActionOpen

section ComparisonComponents
variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A] {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

end ComparisonComponents

section ActionCertificates
variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A]

end ActionCertificates

attribute [local instance high] SymmetricCategory.toBraidedCategory

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Etale

attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

section ComparisonComponents
variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A] {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

end ComparisonComponents

section ActionCertificates
variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A]

end ActionCertificates

attribute [local instance high] SymmetricCategory.toBraidedCategory

end AlgebraicGeometry.Etale

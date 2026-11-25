/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.RationalP1.Canonical.CanonicalSectionProjectionCore

/-! # Supported-unit transport for section/projection coherence -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] firstProjection secondProjection square
attribute [local irreducible] projectionMap singleUnitIso
attribute [local irreducible] supportedUnitIso pushSectionIso

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem compose_three_squares
    {C : Type*} [Category C] {A A' B B' E E' D D' : C}
    {a : A ⟶ A'} {b : B ⟶ B'} {c : E ⟶ E'} {d : D ⟶ D'}
    {f : A ⟶ B} {f' : A' ⟶ B'} {g : B ⟶ E} {g' : B' ⟶ E'}
    {h : E ⟶ D} {h' : E' ⟶ D'}
    (h₁ : a ≫ f' = f ≫ b) (h₂ : b ≫ g' = g ≫ c)
    (h₃ : c ≫ h' = h ≫ d) :
    a ≫ (f' ≫ g' ≫ h') = (f ≫ g ≫ h) ≫ d := by
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]

private theorem map_square
    {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {A A' B B' : C} {a : A ⟶ A'} {b : B ⟶ B'}
    {f : A ⟶ B} {f' : A' ⟶ B'} (h : a ≫ f' = f ≫ b) :
    R.map a ≫ R.map f' = R.map f ≫ R.map b := by
  rw [← R.map_comp, h, R.map_comp]

private theorem replace_square
    {C : Type*} [Category C] {A B D E : C}
    {a : A ⟶ B} {b : D ⟶ E} {f F : B ⟶ E} {g G : A ⟶ D}
    (hf : f = F) (hg : g = G) (h : a ≫ F = G ≫ b) : a ≫ f = g ≫ b := by
  rw [hf, hg]
  exact h

section NativeBraiding
universe v w
variable {C : Type v} [Category.{w} C] [Abelian C]
  [IsGrothendieckAbelian.{w} C] [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

local instance instHasColimitsOfSize_canonicalSectionProjectionTransport
    : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C

private theorem native_braiding_naturality_right
    (A : DerivedCategory C) {B B' : DerivedCategory C} (b : B ⟶ B') :
    (A ◁ b) ≫ (traceDerivedBraiding A B').hom =
      (traceDerivedBraiding A B).hom ≫ (b ▷ A) := by
  unfold traceDerivedBraiding
  exact DerivedMonoidal.braiding_naturality_right (DerivedCategory.Qh (C := C))
      (HomotopyCategory.quasiIso C (.up ℤ)) A b

private theorem native_braiding_naturality_left
    {A A' : DerivedCategory C} (a : A ⟶ A') (B : DerivedCategory C) :
    (a ▷ B) ≫ (traceDerivedBraiding A' B).hom =
      (traceDerivedBraiding A B).hom ≫ (B ◁ a) := by
  unfold traceDerivedBraiding
  exact DerivedMonoidal.braiding_naturality_left (DerivedCategory.Qh (C := C))
      (HomotopyCategory.quasiIso C (.up ℤ)) a B
end NativeBraiding

section NativeProjection
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
-- These wrappers present the same sheaf braiding to the module tensor instances.
attribute [local implicit_reducible] ProEtale.sheafMonoidalCategory
  ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  Sheaf.symmetricCategory Sheaf.braidedCategory

attribute [local instance 3000] projectionDerivedMonoidal
attribute [local instance 4000] projectionModuleAbelian projectionModuleMonoidal
  projectionModuleHasDerived
attribute [local instance 5000] projectionSheafMonoidal projectionCoefficientMonObj
  projectionModuleCategory

@[instance_reducible]
private def native_sheaf_symmetric (Z : Scheme.{u}) :
    SymmetricCategory (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :=
  { sheafSymmetricCategory Z with toBraidedCategory := sheafBraidedCategory Ab Z }
attribute [local instance 20001] native_sheaf_symmetric

-- The native braidings compare the fixed module-site instances.
attribute [-instance] internalMonoidal in
private theorem trace_projection_coefficient_naturality
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (g : X ⟶ S)
    (K : DerivedCategory (Modules Λ S))
    {N N' : DerivedCategory (Modules Λ X)} (n : N ⟶ N') :
    (K ◁ (moduleObjectDerivedPushforward Λ g).map n) ≫ traceProjection Λ g K N' =
      traceProjection Λ g K N ≫
        (moduleObjectDerivedPushforward Λ g).map
          (((moduleObjectDerivedPullback Λ g).obj K) ◁ n) := by
  have hbS : (K ◁ (moduleObjectDerivedPushforward Λ g).map n) ≫
      (traceBraiding Λ S K ((moduleObjectDerivedPushforward Λ g).obj N')).hom =
      (traceBraiding Λ S K ((moduleObjectDerivedPushforward Λ g).obj N)).hom ≫
        ((moduleObjectDerivedPushforward Λ g).map n ▷ K) := by
    unfold traceBraiding
    exact native_braiding_naturality_right K
        ((moduleObjectDerivedPushforward Λ g).map n)
  have hbX : (n ▷ ((moduleObjectDerivedPullback Λ g).obj K)) ≫
      (traceBraiding Λ X N' ((moduleObjectDerivedPullback Λ g).obj K)).hom =
      (traceBraiding Λ X N ((moduleObjectDerivedPullback Λ g).obj K)).hom ≫
        (((moduleObjectDerivedPullback Λ g).obj K) ◁ n) := by
    unfold traceBraiding
    exact native_braiding_naturality_left n ((moduleObjectDerivedPullback Λ g).obj K)
  have hm := NatTrans.congr_app
    (((CondensedRing.derivedUpperStarLowerStarAdjunction Λ g).rightAdjointProjectionMap
      (moduleObjectDerivedTensorComparison Λ g)).naturality n) K
  change ((moduleObjectDerivedPushforward Λ g).map n ▷ K) ≫
      moduleObjectProjectionMate Λ g N' K =
    moduleObjectProjectionMate Λ g N K ≫
      (moduleObjectDerivedPushforward Λ g).map
        (n ▷ ((moduleObjectDerivedPullback Λ g).obj K)) at hm
  unfold traceProjection tracePush tracePull
  exact compose_three_squares hbS hm
    (map_square (moduleObjectDerivedPushforward Λ g) hbX)
end NativeProjection

private theorem normalized_projection_coefficient_naturality
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (a : ProjectionFamily Λ) (ha : ProjectionNormalized Λ a) :
    ∀ {X S : Scheme.{u}} (g : X ⟶ S) (K : DerivedCategory (Modules Λ S))
      {N N' : DerivedCategory (Modules Λ X)} (n : N ⟶ N'),
      (K ◁ (moduleObjectDerivedPushforward Λ g).map n) ≫ a g K N' =
        a g K N ≫ (moduleObjectDerivedPushforward Λ g).map
          (((moduleObjectDerivedPullback Λ g).obj K) ◁ n) := by
  unfold ProjectionFamily ProjectionNormalized internalMonoidal internalTensorBundle
    nativeTensorBundle at *
  intro X S g K N N' n
  exact replace_square (eq_of_heq (ha g K N')) (eq_of_heq (ha g K N))
    (trace_projection_coefficient_naturality Λ g K n)

private theorem projection_coefficient_naturality
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (g : X ⟶ S)
    (K : DerivedCategory (Modules Λ S))
    {N N' : DerivedCategory (Modules Λ X)} (n : N ⟶ N') :
    (K ◁ (moduleObjectDerivedPushforward Λ g).map n) ≫ projectionMap Λ g K N' =
      projectionMap Λ g K N ≫
        (moduleObjectDerivedPushforward Λ g).map
          (((moduleObjectDerivedPullback Λ g).obj K) ◁ n) := by
  unfold projectionMap
  exact normalized_projection_coefficient_naturality Λ
    (projection_existsUnique Λ).exists.choose
    (projection_existsUnique Λ).exists.choose_spec g K n

private theorem projection_coefficient_transport
    {X S : Scheme.{u}} (g : X ⟶ S)
    (K : DerivedCategory (Modules Λ S))
    {N N' L : DerivedCategory (Modules Λ X)} (e : N ≅ N')
    (b : (moduleObjectDerivedPullback Λ g).obj K ⊗ N ⟶ L) :
    (K ◁ (moduleObjectDerivedPushforward Λ g).map e.hom) ≫ projectionMap Λ g K N' ≫
        (moduleObjectDerivedPushforward Λ g).map
          (((moduleObjectDerivedPullback Λ g).obj K ◁ e.inv) ≫ b) =
      projectionMap Λ g K N ≫ (moduleObjectDerivedPushforward Λ g).map b := by
  rw [reassoc_of% (projection_coefficient_naturality Λ g K e.hom),
    ← Functor.map_comp, ← whiskerLeft_comp_assoc, e.hom_inv_id,
    whiskerLeft_id, Category.id_comp]

/-- The supported-unit transport equality for section/projection coherence.
-/
theorem canonical_section_projection_transport
    (Y : Scheme.{u})
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (ρ_ M).inv ≫
      (M ◁ ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫
        (pushSectionIso Λ Y).hom.app (unit Λ (ProjectiveLine Y)) ≫
        (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
          (supportedUnitIso Λ Y).hom)) ≫
      projectionMap Λ (secondProjection Y) M
        ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
          (source Λ Y)) ≫
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
        ((((moduleObjectDerivedPullback Λ (secondProjection Y)).obj M) ◁
          (supportedUnitIso Λ Y).inv) ≫
          sectionTensorMap Λ (diagonalImmersion Y) (secondProjection Y)
            (pullSectionIso Λ Y (secondProjection Y)
              (by unfold secondProjection; exact pullback.diagonal_snd _))
            (unit Λ (ProjectiveLine Y)) (singleUnitIso Λ (ProjectiveLine Y)) M) =
    (ρ_ M).inv ≫
      (M ◁ ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫
        (pushSectionIso Λ Y).hom.app (unit Λ (ProjectiveLine Y)))) ≫
      projectionMap Λ (secondProjection Y) M
        ((moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).obj
          (unit Λ (ProjectiveLine Y))) ≫
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
        (sectionTensorMap Λ (diagonalImmersion Y) (secondProjection Y)
          (pullSectionIso Λ Y (secondProjection Y)
            (by unfold secondProjection; exact pullback.diagonal_snd _))
          (unit Λ (ProjectiveLine Y)) (singleUnitIso Λ (ProjectiveLine Y)) M) := by
  simp only [whiskerLeft_comp, Category.assoc]
  rw [projection_coefficient_transport Λ (secondProjection Y) M
    (supportedUnitIso Λ Y)
    (sectionTensorMap Λ (diagonalImmersion Y) (secondProjection Y)
      (pullSectionIso Λ Y (secondProjection Y)
        (by unfold secondProjection; exact pullback.diagonal_snd _))
      (unit Λ (ProjectiveLine Y)) (singleUnitIso Λ (ProjectiveLine Y)) M)]

end AlgebraicGeometry.ProEtale.RationalP1

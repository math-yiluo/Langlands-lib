/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
public import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
public import Mathlib.Topology.Algebra.Order.Field
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-! # Point scalar actions commute with geometric pullback

The finite scalar calculation from `StrictIntegralScalarPullback`, independent
of the legacy completion-presentation interface.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.ProEtale.PullbackScalar
attribute [local irreducible] CondensedRing.monoidal_upperStar
  Mod.monoidal_extendScalars Functor.monoidal_mapMod
universe u a b c d
private theorem monoidal_scalar {A : Type a} [Category.{b} A] [MonoidalCategory A]
    {B : Type c} [Category.{d} B] [MonoidalCategory B] (F : A ⥤ B) [F.Monoidal]
    (r : End (𝟙_ A)) (s : End (𝟙_ B))
    (h : F.map r.asHom ≫ Functor.OplaxMonoidal.η F =
      Functor.OplaxMonoidal.η F ≫ s.asHom)
    (M : A) :
    F.map ((λ_ M).inv ≫ r.asHom ▷ M ≫ (λ_ M).hom) =
      (λ_ (F.obj M)).inv ≫ s.asHom ▷ F.obj M ≫ (λ_ (F.obj M)).hom := by
  simp only [Functor.map_comp, Functor.Monoidal.map_leftUnitor_inv,
    Functor.Monoidal.map_leftUnitor, Functor.Monoidal.map_whiskerRight, Category.assoc,
    Functor.Monoidal.μ_δ_assoc]
  rw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, Category.assoc, h]
  simp only [Functor.Monoidal.ε_η_assoc]

private theorem scalar_square_under_unit {C : Type*} [Category C]
    {A B M : C} (q : A ⟶ B) (r : A ⟶ A) (t : B ⟶ B)
    (η : B ⟶ M) (α : A ⟶ M) (s : M ⟶ M)
    (hn : r ≫ q = q ≫ t) (hη : q ≫ η = α) (hs : r ≫ α = α ≫ s) :
    q ≫ t ≫ η = q ≫ η ≫ s := by
  calc
    q ≫ t ≫ η = r ≫ α := by rw [← Category.assoc, ← hn, Category.assoc, hη]
    _ = α ≫ s := hs
    _ = q ≫ η ≫ s := by rw [← Category.assoc, hη]

private theorem extendUnitHom_hom_ext
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [HasCoequalizers C] [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
    [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R]
    (φ : R ⟶ S) [IsMonHom φ] (M : Mod C R) (N : Mod C S)
    (f g : (Mod.extendScalars φ).obj M ⟶ N)
    (h : Mod.extendUnitHom φ M ≫ f.hom = Mod.extendUnitHom φ M ≫ g.hom) : f = g := by
  apply ((Mod.extendRestrictAdjunction φ).homEquiv M N).injective
  apply Mod.hom_ext
  simp only [Mod.extendRestrictAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  change (Mod.extendUnit φ M ≫ (Mod.comap φ).map f).hom =
    (Mod.extendUnit φ M ≫ (Mod.comap φ).map g).hom
  simpa only [Mod.comp_hom', Mod.comap_map_hom, Mod.extendUnit_hom] using h

private theorem scalar_extension_square
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [HasCoequalizers C] [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
    [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R]
    (φ : R ⟶ S) [IsMonHom φ] (M : Mod C R) (N : Mod C S)
    (t : End M) (s : End N) (η : (Mod.extendScalars φ).obj M ⟶ N)
    (α : M.X ⟶ N.X) (hη : Mod.extendUnitHom φ M ≫ η.hom = α)
    (hs : t.asHom.hom ≫ α = α ≫ s.asHom.hom) :
    (Mod.extendScalars φ).map t.asHom ≫ η = η ≫ s.asHom := by
  apply extendUnitHom_hom_ext φ M N
  simpa only [Mod.comp_hom', Category.assoc] using
    scalar_square_under_unit (Mod.extendUnitHom φ M) t.asHom.hom
      ((Mod.extendScalars φ).map t.asHom).hom η.hom α s.asHom.hom
      (Mod.extendUnitHom_extendScalarsMap φ t.asHom).symm hη hs

private theorem naturality_square
    {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) (η : F ⟶ G) {M N : C} (f : M ⟶ N)
    (a : F.obj M ⟶ F.obj N) (b : G.obj M ⟶ G.obj N)
    (α : F.obj M ⟶ G.obj M) (β : F.obj N ⟶ G.obj N)
    (ha : a = F.map f) (hb : b = G.map f)
    (hα : α = η.app M) (hβ : β = η.app N) : a ≫ β = α ≫ b := by
  rw [ha, hb, hα, hβ]
  exact η.naturality f

private theorem mapMod_hom
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal] {R : C} [MonObj R]
    {M N : Mod C R} (t : M ⟶ N) :
    ((F.mapMod R).map t).hom = F.map t.hom := rfl

section Coefficients
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

omit [IsCommMonObj Λ] in
private def scalarHom (d : End (Mod.regular Λ)) : End Λ := .of d.asHom.hom

attribute [local irreducible] scalarHom

private def pointScalar (X : Scheme.{u}) (d : End (Mod.regular Λ)) :
    End (Mod.regular (condensedRingObj Λ X)) :=
  .of (Mod.Hom.mk' ((upperStarFromPoint X).map (scalarHom Λ d).asHom)
    (by
      unfold scalarHom
      exact IsModHom.smul_hom
        (f := (((upperStarFromPoint X).mapMod Λ).map d.asHom).hom)))

omit [IsCommMonObj Λ] in
private theorem pointScalar_hom (X : Scheme.{u}) (d : End (Mod.regular Λ)) :
    (pointScalar Λ X d).asHom.hom =
      (upperStarFromPoint X).map (scalarHom Λ d).asHom := rfl

private def pullbackUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar Λ f).obj
      (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) ⟶
      𝟙_ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  Functor.OplaxMonoidal.η (CondensedRing.upperStar Λ f)

attribute [local irreducible] pointScalar pullbackUnit

-- Kernel conversion compares the sheaf monoidal instances at the coefficient square.
omit [IsCommMonObj Λ] in
private theorem coefficient_scalar_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d : End (Mod.regular Λ)) :
    (((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)).map
      (pointScalar Λ Y d).asHom).hom ≫ condensedPullbackHom Λ f =
      condensedPullbackHom Λ f ≫ (pointScalar Λ X d).asHom.hom := by
  apply naturality_square (upperStarFromPoint Y ⋙ ProEtale.upperStar Ab.{u + 1} f)
    (upperStarFromPoint X) (upperStarFromPointComp f).hom (scalarHom Λ d).asHom
  · rw [mapMod_hom, pointScalar_hom]
    rfl
  · exact pointScalar_hom Λ X d
  · rfl
  · rfl

private theorem pullback_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
    (t : M ⟶ N) :
    (CondensedRing.upperStar Λ f).map t =
      (Mod.extendScalars (condensedPullbackHom Λ f)).map
        (((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)).map t) := rfl

private theorem pullback_unit_scalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d : End (Mod.regular Λ)) :
    (CondensedRing.upperStar Λ f).map (pointScalar Λ Y d).asHom ≫ pullbackUnit Λ f =
      pullbackUnit Λ f ≫ (pointScalar Λ X d).asHom := by
  let α := condensedPullbackHom Λ f
  let G := (ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)
  let M := 𝟙_ (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
  have hη : Mod.extendUnitHom α (G.obj M) ≫ (pullbackUnit Λ f).hom = α := by
    unfold pullbackUnit
    exact CondensedRing.extendUnitHom_η_upperStar Λ f
  rw [pullback_map]
  exact scalar_extension_square α (G.obj M)
    (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (.of (G.map (pointScalar Λ Y d).asHom)) (pointScalar Λ X d) (pullbackUnit Λ f) α hη
    (coefficient_scalar_naturality Λ f d)
end Coefficients

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem regular_scalar_eq (X : Scheme.{u})
    (d : End (Mod.regular (DerivedNakayama.integerRing l E))) :
    (DerivedNakayama.regularPullbackIso l E X).inv ≫
      (DerivedNakayama.pullback l E X).map d.asHom ≫
      (DerivedNakayama.regularPullbackIso l E X).hom =
    (pointScalar (DerivedNakayama.integerRing l E) X d).asHom := by
  simp only [DerivedNakayama.regularPullbackIso, eqToIso_refl,
    Iso.refl_inv, Iso.refl_hom, Category.comp_id]
  apply Mod.hom_ext
  simp only [Mod.comp_hom', Mod.id_hom', pointScalar_hom]
  rfl

/-- Exact geometric module pullback preserves the action of every point scalar. -/
theorem scalarOnModules {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d : End (Mod.regular (DerivedNakayama.integerRing l E)))
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (DerivedNakayama.integerRing l E) Y)) :
    (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).map
      ((DerivedNakayama.scalarOnModules l E Y d).app M) =
      (DerivedNakayama.scalarOnModules l E X d).app
        ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).obj M) := by
  apply monoidal_scalar
  rw [regular_scalar_eq, regular_scalar_eq]
  exact pullback_unit_scalar (DerivedNakayama.integerRing l E) f d

end AlgebraicGeometry.ProEtale.PullbackScalar

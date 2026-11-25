/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassTensorPullback
public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricOrdinaryTensor
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

/-! # Transport of ordinary tensor comparisons to explicit site tensors

Source: Stacks 03EK and 03EL; blueprint tower-operations proof, clause (2).
(blueprint: def-sfb-tower-class-tensor-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local implicit_reducible] PresheafOfModules.toPresheaf CategoryTheory.sheafCompose
attribute [local implicit_reducible] PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj PresheafOfModules.presheaf ModuleCat.restrictScalars
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe c v r u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses.TensorCoordinates

section Site
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{max c v r})

/-- The explicit site tensor and the monoidal tensor use the same sheafification.
Source: Stacks 03EK (blueprint: def-sfb-tower-class-tensor-comparison). -/
abbrev siteTensorIso (N : SemilinearSections.Mod.{c, v, max c v r} J R) :
    let := SemilinearSections.abelianSheafify.{c, v, max c v r} J
    let := SemilinearSections.locallyBijective.{c, v, max c v r} J
    let := SheafOfModules.isMonoidal_W_independentCoefficients R
    let := SheafOfModules.monoidalCategory R
    SheafOfModules.siteSheafTensorRight (A := R) N ≅
      CategoryTheory.MonoidalCategory.tensorRight N :=
  let := SemilinearSections.abelianSheafify.{c, v, max c v r} J
  let := SemilinearSections.locallyBijective.{c, v, max c v r} J
  SheafOfModules.siteSheafTensorRightIso R N

private theorem siteTensorIso_component (M N : SemilinearSections.Mod.{c, v, max c v r} J R) :
    let := SemilinearSections.abelianSheafify.{c, v, max c v r} J
    let := SemilinearSections.locallyBijective.{c, v, max c v r} J
    let := SheafOfModules.isMonoidal_W_independentCoefficients R
    let := SheafOfModules.monoidalCategory R
    (siteTensorIso.{c, v, r} J R N).hom.app M =
      (PresheafOfModules.sheafification (𝟙 (SemilinearSections.ring J R).obj)).map
          ((SheafOfModules.siteTensorRightIso R N.val).hom.app M.val) ≫
        (SheafOfModules.tensorObjIsoSheafification M N).inv := by
  let := SemilinearSections.abelianSheafify.{c, v, max c v r} J
  let := SemilinearSections.locallyBijective.{c, v, max c v r} J
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  dsimp only [siteTensorIso, SheafOfModules.siteSheafTensorRightIso,
    SheafOfModules.tensorRightPresentation, SheafOfModules.tensorObjIsoSheafification,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.mapIso_hom,
    Functor.mapIso_inv, NatTrans.comp_app, MonoidalCategory.tensorIso_hom,
    MonoidalCategory.tensorIso_inv,
    Functor.comp_obj, Functor.comp_map, Functor.Monoidal.μIso_inv]
  dsimp only [Functor.Monoidal.commTensorRight, NatIso.ofComponents,
    Functor.Monoidal.μIso, asIso, curriedTensor, Functor.flip]
  dsimp only [MonoidalCategory.tensorIso, Iso.app_hom,
    CategoryTheory.MonoidalCategory.tensorRight, Functor.flip, curriedTensor]
  simp only [Category.assoc, MonoidalCategory.tensorHom_def]
  rfl

/-- The bridge preserves the sheafification-unit pairing.
Source: Stacks 03EK (blueprint: def-sfb-tower-class-tensor-comparison). -/
theorem siteTensorIso_pure (M N : SemilinearSections.Mod.{c, v, max c v r} J R)
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    let := SemilinearSections.abelianSheafify.{c, v, max c v r} J
    let := SemilinearSections.locallyBijective.{c, v, max c v r} J
    ((siteTensorIso.{c, v, r} J R N).hom.app M).val.app U
      (SheafOfModules.siteSheafTensorTmul (A := R) M N U x y) =
      SemilinearSections.tensorSection.{c, v, r} J R M N U x y := by
  let := SemilinearSections.abelianSheafify.{c, v, max c v r} J
  let := SemilinearSections.locallyBijective.{c, v, max c v r} J
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (SemilinearSections.ring J R).obj)
  let i := (SheafOfModules.siteTensorRightIso R N.val).hom.app M.val
  rw [siteTensorIso_component.{c, v, r} J R M N]
  change (SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U
      (((PresheafOfModules.sheafification
        (𝟙 (SemilinearSections.ring J R).obj)).map i).val.app U
        ((adj.unit.app (SheafOfModules.siteTensorPresheaf M.val N.val)).app U
          (x ⊗ₜ[R.obj.obj U] y))) = _
  have h := congrArg (fun k ↦ k.app U (x ⊗ₜ[R.obj.obj U] y)) (adj.unit.naturality i)
  exact congrArg ((SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U) h.symm

end Site

section Geometry
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{max c v r})
    (τ : ∀ n, B (n + 1) ⟶ B n) (A : SemilinearSections.Data.{c, v, r} J B τ)
    {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
    (J' : GrothendieckTopology C')
    (L : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (P : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r))) (adj : L ⊣ P)

/-- Retain the ordinary fields of a geometric calculus on arbitrary sites.
Source: Zheng 4.1 (blueprint: def-sfb-tower-class-tensor-comparison). -/
def ordinaryOfGeometry (G : SemilinearSections.Geometry.{c, v, r} J B τ A J' L P adj) :
    SemilinearSections.GeometryOrdinary.{c, v, r} J B τ J' L P adj :=
  { G with }

end Geometry

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Forget the derived fields while retaining every ordinary normalization.
Source: Zheng Construction 4.1 (blueprint: def-sfb-tower-class-tensor-comparison). -/
def ordinaryGeometry {b : SpTowerShriek.Base l E}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : SpTowerShriek.Geometry l E b f) :
    SemilinearSections.GeometryOrdinary.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y)
      (Scheme.ProEt.topology X)
      (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
      (Scheme.proEtaleSheafDirectImage f (Type (u + 1)))
      (Scheme.proEtaleSheafAdjunction f (Type (u + 1))) :=
  ordinaryOfGeometry.{u + 1, u, u + 1} (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y)
    (SpTowerShriek.tau l E Y) (b.calculus Y) (Scheme.ProEt.topology X)
    (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
    (Scheme.proEtaleSheafDirectImage f (Type (u + 1)))
    (Scheme.proEtaleSheafAdjunction f (Type (u + 1))) g.generic

/-- Transport a monoidal system tensor comparison along the specified coordinates.
Source: Stacks 03EL (blueprint: def-sfb-tower-class-tensor-comparison). -/
def comparisonOfCoordinates {b : SpTowerShriek.Base l E}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : SpTowerShriek.Geometry l E b f)
    (B' : ℕ → Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (τ' : ∀ n, B' (n + 1) ⟶ B' n)
    (hB : B' = SpTowerShriek.B l E X) (hτ : HEq τ' (SpTowerShriek.tau l E X))
    (F : SpTowerShriek.S l E Y ⥤ SemilinearSections.Systems.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) B' τ') (hF : HEq g.pull F)
    (μ : ∀ N : SpTowerShriek.S l E Y,
      let := SheafOfModules.isMonoidal_W_independentCoefficients
        (SemilinearSections.systemRing (Scheme.ProEt.topology Y)
          (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y))
      let := SheafOfModules.monoidalCategory
        (SemilinearSections.systemRing (Scheme.ProEt.topology Y)
          (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y))
      let := SheafOfModules.isMonoidal_W_independentCoefficients
        (SemilinearSections.systemRing (Scheme.ProEt.topology X) B' τ')
      let := SheafOfModules.monoidalCategory
        (SemilinearSections.systemRing (Scheme.ProEt.topology X) B' τ')
      CategoryTheory.MonoidalCategory.tensorRight N ⋙ F ≅
        F ⋙ CategoryTheory.MonoidalCategory.tensorRight (F.obj N)) :
    ∀ N : Systems Y (Arings l E Y),
      SpTowerClasses.tensorRight l E Y N ⋙ g.pull ≅
        g.pull ⋙ SpTowerClasses.tensorRight l E X (g.pull.obj N) := by
  subst B'
  cases eq_of_heq hτ
  cases eq_of_heq hF
  intro N
  exact Functor.isoWhiskerRight
      (siteTensorIso.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (systemRing l E Y) N) g.pull ≪≫ μ N ≪≫
    Functor.isoWhiskerLeft g.pull
      (siteTensorIso.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (systemRing l E X) (g.pull.obj N)).symm

/-- The system comparison constructed from a normalized ordinary geometric tensor.
Source: Stacks 03EL (blueprint: def-sfb-tower-class-tensor-comparison). -/
def comparison {b : SpTowerShriek.Base l E}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : SpTowerShriek.Geometry l E b f)
    (T : SemilinearSections.GeometryOrdinaryTensor.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y)
      (Scheme.ProEt.topology X)
      (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
      (Scheme.proEtaleSheafDirectImage f (Type (u + 1)))
      (Scheme.proEtaleSheafAdjunction f (Type (u + 1))) (ordinaryGeometry l E g)) :
    ∀ N : Systems Y (Arings l E Y),
      SpTowerClasses.tensorRight l E Y N ⋙ g.pull ≅
        g.pull ⋙ SpTowerClasses.tensorRight l E X (g.pull.obj N) := by
  let O := ordinaryGeometry l E g
  let := SheafOfModules.isMonoidal_W_independentCoefficients
    (SemilinearSections.systemRing (Scheme.ProEt.topology Y)
      (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y))
  let := SheafOfModules.monoidalCategory
    (SemilinearSections.systemRing (Scheme.ProEt.topology Y)
      (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y))
  let := SheafOfModules.isMonoidal_W_independentCoefficients
    (SemilinearSections.systemRing (Scheme.ProEt.topology X)
      O.coefficients O.coefficientTransition)
  let := SheafOfModules.monoidalCategory
    (SemilinearSections.systemRing (Scheme.ProEt.topology X)
      O.coefficients O.coefficientTransition)
  let μ (N : SpTowerShriek.S l E Y) :
      CategoryTheory.MonoidalCategory.tensorRight N ⋙ O.pull ≅
        O.pull ⋙ CategoryTheory.MonoidalCategory.tensorRight (O.pull.obj N) :=
    NatIso.ofComponents (fun M ↦ T.system M N) (by
      intro M M' a
      change O.pull.map (a ▷ N) ≫ (T.system M' N).hom =
        (T.system M N).hom ≫ (O.pull.map a ▷ O.pull.obj N)
      have h := T.system_natural a (𝟙 N)
      change O.pull.map (a ⊗ₘ 𝟙 N) ≫ (T.system M' N).hom =
        (T.system M N).hom ≫ (O.pull.map a ⊗ₘ O.pull.map (𝟙 N)) at h
      rw [O.pull.map_id, MonoidalCategory.tensorHom_id,
        MonoidalCategory.tensorHom_id] at h
      exact h)
  exact comparisonOfCoordinates l E g O.coefficients O.coefficientTransition
    g.coefficients g.transitions O.pull g.pull_eq μ

end AlgebraicGeometry.ProEtale.SpTowerClasses.TensorCoordinates

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Etale.Coefficient.EtaleCoefficientTransportInterfaces
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.Algebra.Homology.System.SystemScalarModel
import WeilConjectures.CategoryTheory.Derived.DerivedSquareIndependentUniverses
/-! # Exact scalar transport on strict etale systems -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false
@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local irreducible] CategoryTheory.constantSheaf
  SheafOfModules.siteCoefficientTensor SheafOfModules.siteCoefficientTensorAdj
private theorem scalarSystemHom_ext
    {T : Scheme.{u}} {O : Type (u + 1)} [CommRing O] {ell : O}
    {M N : strictEtaleCoefficientSystem T O ell} (f g : M ⟶ N)
    (h : f.app = g.app) : f = g := by
  cases f
  cases g
  cases h
  rfl

private def restrictionSquare {C : Type*} [Category C]
    {J : GrothendieckTopology C} {A B D E : Sheaf J RingCat.{u + 1}}
    (f : A ⟶ B) (g : D ⟶ E) (p : D ⟶ A) (q : E ⟶ B) (h : p ≫ f = g ≫ q) :
    restrictScalars.{u + 1} f ⋙ restrictScalars p ≅
      restrictScalars q ⋙ restrictScalars g :=
  pushforwardComp (F := 𝟭 C) (G := 𝟭 C) p f ≪≫ pushforwardCongr h ≪≫
    (pushforwardComp (F := 𝟭 C) (G := 𝟭 C) g q).symm

section ScalarOrdinary
variable {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
  {phi : O →+* O'} {index : ℕ →o ℕ}
  (a : StrictEtaleCoefficientChange O O' ell mu phi index)
  {T : Scheme.{u}}
  (PA : StrictEtaleEvaluation T O ell)

private theorem scalarStageSquare {m n : ℕ} (h : n ≤ m) :
    coefficientQuotientMap (J := T.smallEtaleTopology) O ell (index.monotone h) ≫
        a.sheaf T n =
      a.sheaf T m ≫ coefficientQuotientMap (J := T.smallEtaleTopology) O' mu h := by
  change (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).map _ ≫
    (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).map _ =
    (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).map _ ≫
    (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change a.ring n (Ideal.Quotient.mk _ x) =
    Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)) (a.ring m (Ideal.Quotient.mk _ x))
  rw [a.generators, a.generators]
  rfl

private abbrev scalarStageExtension (n : ℕ) :=
  siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)
private abbrev scalarStageRestriction (n : ℕ) :=
  restrictScalars.{u + 1}
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.sheaf T n))
private abbrev scalarStageAdj (n : ℕ) :=
  siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf T n)

private def scalarRestrictionSquare {m n : ℕ} (h : n ≤ m) :
    scalarStageRestriction a (T := T) n ⋙
        coefficientRestriction (J := T.smallEtaleTopology) O ell (index.monotone h) ≅
      coefficientRestriction (J := T.smallEtaleTopology) O' mu h ⋙
        scalarStageRestriction a (T := T) m :=
  restrictionSquare
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.sheaf T n))
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.sheaf T m))
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (coefficientQuotientMap O ell (index.monotone h)))
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (coefficientQuotientMap O' mu h))
    (by
      simpa only [Functor.map_comp] using congrArg
        (sheafCompose T.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (scalarStageSquare a (T := T) h))

private def scalarSuccessor {m n : ℕ} (h : n ≤ m) :
    coefficientRestriction (J := T.smallEtaleTopology) O ell (index.monotone h) ⋙
        scalarStageExtension a (T := T) m ⟶
      scalarStageExtension a (T := T) n ⋙
        coefficientRestriction (J := T.smallEtaleTopology) O' mu h :=
  ((mateEquiv (scalarStageAdj a (T := T) n) (scalarStageAdj a (T := T) m)).symm
    (.mk _ _ _ _ (scalarRestrictionSquare a (T := T) h).hom))

private def scalarOrdinary :
    strictEtaleCoefficientSystem T O ell ⥤ strictEtaleCoefficientSystem T O' mu where
  obj M := {
    level := fun n ↦ (scalarStageExtension a (T := T) n).obj (M.level (index n))
    transition := fun n ↦
      (scalarStageExtension a (T := T) (n + 1)).map
        ((PA.strictTransition (index.monotone (Nat.le_succ n))).app M) ≫
          (scalarSuccessor a (T := T) (Nat.le_succ n)).app (M.level (index n)) }
  map f := {
    app := fun n ↦ (scalarStageExtension a (T := T) n).map (f.app (index n))
    comm := by
      intro n
      let h := index.monotone (Nat.le_succ n)
      let Em := scalarStageExtension a (T := T) (n + 1)
      let En := scalarStageExtension a (T := T) n
      let RA := coefficientRestriction (J := T.smallEtaleTopology) O ell h
      let RB := coefficientRestriction (J := T.smallEtaleTopology) O' mu (Nat.le_succ n)
      let θ := scalarSuccessor a (T := T) (Nat.le_succ n)
      have h₁ := (PA.strictTransition h).naturality f
      have h₂ := θ.naturality (f.app (index n))
      change Em.map _ ≫ (Em.map _ ≫ θ.app _) = (Em.map _ ≫ θ.app _) ≫ RB.map _
      calc
        _ = Em.map (f.app (index (n + 1)) ≫ (PA.strictTransition h).app _) ≫
            θ.app _ := by rw [Em.map_comp, Category.assoc]
        _ = Em.map ((PA.strictTransition h).app _ ≫ RA.map (f.app (index n))) ≫
            θ.app _ := congrArg (fun k ↦ Em.map k ≫ θ.app _) h₁
        _ = Em.map ((PA.strictTransition h).app _) ≫
            (Em.map (RA.map (f.app (index n))) ≫ θ.app _) := by
          rw [Em.map_comp, Category.assoc]
        _ = Em.map ((PA.strictTransition h).app _) ≫
            (θ.app _ ≫ RB.map (En.map (f.app (index n)))) :=
          congrArg (fun k ↦ Em.map ((PA.strictTransition h).app _) ≫ k) h₂
        _ = _ := (Category.assoc _ _ _).symm }
  map_id M := by
    apply scalarSystemHom_ext
    funext n
    exact (scalarStageExtension a (T := T) n).map_id _
  map_comp f g := by
    apply scalarSystemHom_ext
    funext n
    exact (scalarStageExtension a (T := T) n).map_comp _ _

private def scalarUnit (n : ℕ) :
    coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) (index n) ⋙
        SheafOfModules.toSheaf.{u + 1} _ ⟶
      scalarOrdinary a PA ⋙ coefficientEvaluation
        (J := T.smallEtaleTopology) (O := O') (ell := mu) n ⋙
          SheafOfModules.toSheaf.{u + 1} _ where
  app M := siteTensorUnitUnderlying (a.sheaf T n) (M.level (index n))
  naturality {M N} f := by
    change (SheafOfModules.toSheaf _).map (f.app (index n)) ≫
      siteTensorUnitUnderlying (a.sheaf T n) (N.level (index n)) =
        siteTensorUnitUnderlying (a.sheaf T n) (M.level (index n)) ≫
          (SheafOfModules.toSheaf _).map
            ((scalarStageExtension a (T := T) n).map (f.app (index n)))
    have h := (scalarStageAdj a (T := T) n).unit.naturality (f.app (index n))
    ext V x
    exact congrArg (fun k ↦ k.val.app V x) h

end ScalarOrdinary

end AlgebraicGeometry

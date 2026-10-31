import Langlands.CategoryTheory.Renard.RegularModuleSmallProgeneratorStatements
import Langlands.CategoryTheory.Renard.HomExactnessComparison
import Langlands.CategoryTheory.Renard.HomGeneratorCriteria
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Renard A.VIII.2: proof that the regular unital module is a small progenerator

For a unital ring `R`, the lifted regular module `ModuleCat.of R (ULift.{v} R)` is a small
progenerator of `ModuleCat.{max u v} R` at every coproduct index size. Projectivity and
generation go through the published comparisons with Mathlib's `Projective` and
`IsSeparator`. Coproduct preservation uses that the integer-module Hom functor out of the
regular module is isomorphic to restriction of scalars along `ℤ → R`, a left adjoint.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Langlands.Renard

variable (R : Type u) [Ring R]

/-- The `R`-linear map from the lifted regular module sending `ULift.up r` to `r • x`. -/
def regularModuleSpanSingleton {X : ModuleCat.{max u v} R} (x : X) :
    ModuleCat.of R (ULift.{v} R) ⟶ X :=
  ModuleCat.ofHom ((LinearMap.toSpanSingleton R X x).comp ULift.moduleEquiv.toLinearMap)

@[simp] theorem regularModuleSpanSingleton_apply {X : ModuleCat.{max u v} R} (x : X) (r : R) :
    (regularModuleSpanSingleton R x).hom (ULift.up r) = r • x := rfl

/-- A morphism out of the lifted regular module is determined by its value at `ULift.up 1`. -/
theorem regularModuleSpanSingleton_apply_one {X : ModuleCat.{max u v} R}
    (f : ModuleCat.of R (ULift.{v} R) ⟶ X) :
    regularModuleSpanSingleton R (f.hom (ULift.up 1)) = f := by
  ext ⟨r⟩
  change r • f.hom (ULift.up 1) = f.hom (ULift.up r)
  rw [← map_smul]
  change f.hom (ULift.up (r * 1)) = f.hom (ULift.up r)
  rw [mul_one]

/-- The lifted regular module is a separator of `ModuleCat.{max u v} R`. -/
theorem regularModule_isSeparator : IsSeparator (ModuleCat.of R (ULift.{v} R)) := by
  intro X Y f g h
  ext x
  have := congrArg (fun k : ModuleCat.of R (ULift.{v} R) ⟶ Y => k.hom (ULift.up (1 : R)))
    (h _ ((ObjectProperty.singleton_iff _ _).mpr rfl) (regularModuleSpanSingleton R x))
  change f.hom ((1 : R) • x) = g.hom ((1 : R) • x) at this
  rwa [one_smul] at this

/-- Evaluation at `ULift.up 1` as an additive equivalence from `Hom(R, X)` to `X`. -/
def regularModuleHomAddEquiv (X : ModuleCat.{max u v} R) :
    (Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt
        (ModuleCat.of R (ULift.{v} R))).obj X ≃+
      (ModuleCat.restrictScalars.{max u v} (Int.castRingHom R)).obj X where
  toFun f := (f : ModuleCat.of R (ULift.{v} R) ⟶ X).hom (ULift.up 1)
  invFun x := regularModuleSpanSingleton R (X := X) x
  left_inv f := regularModuleSpanSingleton_apply_one R f
  right_inv x := one_smul R (x : X)
  map_add' _ _ := rfl

/-- The value at `ULift.up 1` identifies `Hom(R, X)`, with its restricted integer action, with
`X` with scalars restricted along `ℤ → R`. -/
def regularModuleHomIso (X : ModuleCat.{max u v} R) :
    (Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt
        (ModuleCat.of R (ULift.{v} R))).obj X ≅
      (ModuleCat.restrictScalars.{max u v} (Int.castRingHom R)).obj X :=
  ((regularModuleHomAddEquiv R X).toIntLinearEquiv
    (modM := ((Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt
        (ModuleCat.of R (ULift.{v} R))).obj X).isModule)
    (modM₂ := ((ModuleCat.restrictScalars.{max u v} (Int.castRingHom R)).obj X).isModule)
    ).toModuleIso

@[simp] theorem regularModuleHomIso_hom_apply (X : ModuleCat.{max u v} R)
    (f : ModuleCat.of R (ULift.{v} R) ⟶ X) :
    (regularModuleHomIso R X).hom f = f.hom (ULift.up 1) := rfl

/-- The integer-module Hom functor out of the lifted regular module is restriction of scalars
along `ℤ → R`. -/
def regularModuleHomFunctorIso :
    Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt (ModuleCat.of R (ULift.{v} R)) ≅
      ModuleCat.restrictScalars.{max u v} (Int.castRingHom R) :=
  NatIso.ofComponents (regularModuleHomIso R) (fun _ => by ext; rfl)

/-- Renard projectivity of the lifted regular module. -/
theorem regularModule_homProjective : HomProjective (ModuleCat.of R (ULift.{v} R)) :=
  (homProjectiveComparison _).mpr inferInstance

/-- Renard generation of the lifted regular module. -/
theorem regularModule_homGenerator : HomGenerator (ModuleCat.of R (ULift.{v} R)) :=
  (homGeneratorComparison _).mpr (regularModule_isSeparator R)

/-- The Hom functor out of the lifted regular module preserves coproducts of every index size;
no relation between `w` and the module universe is used. -/
theorem regularModule_homPreservesCoproducts [HasCoproducts.{w} (ModuleCat.{max u v} R)] :
    HomPreservesCoproducts.{w} (ModuleCat.of R (ULift.{v} R)) := by
  intro I
  have : PreservesColimitsOfSize.{w, w}
      (ModuleCat.restrictScalars.{max u v} (Int.castRingHom R)) :=
    (ModuleCat.restrictCoextendScalarsAdj.{max u v}
      (Int.castRingHom R)).leftAdjoint_preservesColimits
  exact preservesColimitsOfShape_of_natIso (regularModuleHomFunctorIso R).symm

/-- Renard A.VIII.2: a unital ring is a small progenerator of its unital left modules. -/
theorem regularModuleSmallProgenerator [HasCoproducts.{w} (ModuleCat.{max u v} R)] :
    RegularModuleSmallProgeneratorStatement.{w, v, u} R :=
  ⟨⟨regularModule_homProjective R, regularModule_homPreservesCoproducts R⟩,
    regularModule_homGenerator R⟩

end Langlands.Renard

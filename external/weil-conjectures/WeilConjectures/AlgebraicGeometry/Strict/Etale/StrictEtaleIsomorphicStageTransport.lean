/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Coefficient.EtaleCoefficientTransportInterfaces
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
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

/-!
# Strict étale transport at isomorphic coefficient stages

Source: Zheng, Construction 4.1 and Proposition 2.29(2)
(blueprint: lem-pur-strict-etale-isomorphic-stage-projection).

This is the coefficient-system part of the projection theorem.  It isolates the
construction of the exact transport and its finite-level equivalences from the
compact-support projection assembly.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

private theorem systemHom_ext
    {T : Scheme.{u}} {O : Type (u + 1)} [CommRing O] {ell : O}
    {M N : strictEtaleCoefficientSystem T O ell} (f g : M ⟶ N)
    (h : f.app = g.app) : f = g := by
  cases f
  cases g
  cases h
  rfl

private def scalarRoundTrip {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    restrictScalars.{u + 1} c.hom ⋙ restrictScalars c.inv ≅ 𝟭 _ :=
  pushforwardComp (F := 𝟭 C) (G := 𝟭 C) c.inv c.hom ≪≫
    pushforwardCongr c.inv_hom_id ≪≫ pushforwardId S

private def scalarEquivalence {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R where
  functor := restrictScalars c.hom
  inverse := restrictScalars c.inv
  unitIso := (scalarRoundTrip c).symm
  counitIso := scalarRoundTrip c.symm
  functor_unitIso_comp M := by ext U x; rfl

private def restrictionSquare {C : Type*} [Category C]
    {J : GrothendieckTopology C} {A B D E : Sheaf J RingCat.{u + 1}}
    (f : A ⟶ B) (g : D ⟶ E) (p : D ⟶ A) (q : E ⟶ B) (h : p ≫ f = g ≫ q) :
    restrictScalars.{u + 1} f ⋙ restrictScalars p ≅
      restrictScalars q ⋙ restrictScalars g :=
  pushforwardComp (F := 𝟭 C) (G := 𝟭 C) p f ≪≫ pushforwardCongr h ≪≫
    (pushforwardComp (F := 𝟭 C) (G := 𝟭 C) g q).symm

section Construction
variable {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
  {phi : O →+* O'} {index : ℕ →o ℕ}
  (a : StrictEtaleCoefficientChange O O' ell mu phi index)
  (ha : ∀ n, Function.Bijective (a.ring n))
  {T : Scheme.{u}}
  (PA : StrictEtaleEvaluation T O ell) (PB : StrictEtaleEvaluation T O' mu)

private theorem stageSquare {m n : ℕ} (h : n ≤ m) :
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

end Construction

section DerivedSquare
universe a b c d av bv cv dv w
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{w} B]
  {C : Type c} [Category.{cv} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type d} [Category.{dv} D] [Abelian D] [HasDerivedCategory.{w} D]
  (F : A ⥤ B) (eA : A ⥤ C) (eB : B ⥤ D) (L : C ⥤ D)
  [F.Additive] [eA.Additive] [eB.Additive] [L.Additive]
  (FD : DerivedCategory A ⥤ DerivedCategory B)
  (EA : DerivedCategory A ⥤ DerivedCategory C)
  (EB : DerivedCategory B ⥤ DerivedCategory D)
  (LD : DerivedCategory C ⥤ DerivedCategory D)
  (φF : DerivedCategory.Q ⋙ FD ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φA : DerivedCategory.Q ⋙ EA ≅ eA.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φB : DerivedCategory.Q ⋙ EB ≅ eB.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φL : DerivedCategory.Q ⋙ LD ≅ L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (α : F ⋙ eB ≅ eA ⋙ L)

end DerivedSquare

end AlgebraicGeometry

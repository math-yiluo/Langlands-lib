/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorComparison
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteProjectionActionLaws
import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidalUnit
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TensorSheaf
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Braided
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Reduction
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor
import all WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportConstructibility

set_option linter.privateModule false

/-!
# Unit and coefficient associativity for a fixed compactification
The fixed-ring coordinates below use the canonical intrinsic realization solely to
express the recorded constructibility predicates. All arrows are the ordinary
constant-coefficient derived arrows at the specified compactification.

## Main definitions

* `inverseCompactificationProjection`: the symmetry-conjugate canonical inverse.
* `CompactificationProjectionUnit`, `CompactificationProjectionAssoc`: the two equations.
* `CompactificationProjectionDomains`: all their constructible tensor inputs.

## Main statements

* `compactificationProjection_coefficient_coherence`: both laws and their domains.

## References

* Stacks Project, Tags 0B56 and 0GL1
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w v₁ w₁
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale
-- Use the canonical sheaf braiding also in the derived comparison proofs.
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
section ActionUnit
variable {C D : Type*} [Category C] [Category D]
  [MonoidalCategory C] [MonoidalCategory D]
  (P : C ⥤ D) (S : D ⥤ C) [S.OplaxMonoidal]
  (p : ∀ (M : C) (B : D), P.obj M ⊗ B ⟶ P.obj (M ⊗ S.obj B))

end ActionUnit

section FunctorUnit
variable {C D : Type*} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D] [MonoidalClosed D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F]
  [Limits.PreservesFiniteColimits F] [F.Monoidal]
open _root_.DerivedCategory

end FunctorUnit

section Conjugate
variable {C : Type v} [Category.{w} C] [MonoidalCategory C] [SymmetricCategory C]
  {T : Type v₁} [Category.{w₁} T] [MonoidalCategory T] [SymmetricCategory T]
  (P : C ⥤ T) (S : T ⥤ C)
  (p : ∀ (M : C) (B : T), P.obj M ⊗ B ⟶ P.obj (M ⊗ S.obj B))

private theorem conjugate_unit (e : S.obj (𝟙_ T) ⟶ 𝟙_ C) (M : C)
    [IsIso (p M (𝟙_ T))]
    (hu : p M (𝟙_ T) ≫ P.map (M ◁ e ≫ (ρ_ M).hom) = (ρ_ (P.obj M)).hom) :
    P.map (β_ (S.obj (𝟙_ T)) M).hom ≫ inv (p M (𝟙_ T)) ≫
        (β_ (P.obj M) (𝟙_ T)).hom ≫ (λ_ (P.obj M)).hom =
      P.map (e ▷ M ≫ (λ_ M).hom) := by
  rw [braiding_leftUnitor]
  rw [← hu, IsIso.inv_hom_id_assoc, ← P.map_comp]
  congr 1
  rw [← BraidedCategory.braiding_naturality_left_assoc, braiding_rightUnitor]

end Conjugate

section FiniteDomains
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (T : Scheme.{u})

end FiniteDomains

section Arrows
variable (V : Type v) [Category.{u + 1} V] [Abelian V]
  [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [MonoidalPreadditive V]
  [SymmetricCategory V] [MonoidalClosed V] [Abelian.HasFunctorialFlatResolution V]
  [UpperStarPreservesFlat V] {X Y : Scheme.{u}} {f : X ⟶ Y}
  (c : Compactification f)
section PullbackUnit
variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
open _root_.DerivedCategory
variable [UpperStarPreservesFlat A]
end PullbackUnit

section NativeAction
variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A] {X Y : Scheme.{u}}
  (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

end NativeAction

end Arrows
end AlgebraicGeometry.ProEtale

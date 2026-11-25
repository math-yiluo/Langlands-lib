/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
public import WeilConjectures.AlgebraicGeometry.IntegralReductionTensor

/-! # Integral reduction as a derived tensor functor

Source: Bhatt--Scholze, Lemma 6.5.9(3), and the definition of derived extension
of scalars (blueprint: lem-weil-pbc-integral-reduction-tensor).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ] (M : Mod C R)








end CategoryTheory.Mod

local instance instEssentiallySmallProfinite_properBaseChangeIntegralReductionTensor
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- Derived reduction followed by restriction is a left derived functor of tensor
with the residue regular module regarded as an integral module.
Source: Bhatt--Scholze, Lemma 6.5.9(3), and derived extension of scalars
(blueprint: lem-weil-pbc-integral-reduction-tensor).

Proof in words. The coequalizer defining extension of scalars, after restriction,
is the coequalizer defining relative tensor with the restricted regular residue
module. The existing underlying-sheaf comparison respects the integral action:
precompose its linearity equation with the epimorphism from the free tensor
presentation and use the defining balancing equations. Naturality is detected by
the faithful forgetful functor. Thus the component isomorphisms lift to a natural
isomorphism of integral modules. Compose the extension counit with the exact
restriction-of-scalars comparison and this tensor presentation to construct ε.
For a K-flat complex, the extension counit is invertible, as are the other two
comparisons. Tensoring with any module preserves quasi-isomorphisms between K-flat
complexes: an acyclic K-flat cone remains acyclic after tensoring, and symmetry
switches the fixed factor to the required side. The K-flat characterization of
left derived functors therefore applies to ε. No flatness of the residue module
is required. This works on every scheme, including the empty one. -/
theorem integralReduction_restrictTensor (T : Scheme.{u}) :
    ∃ ε : DerivedCategory.Qh ⋙ (integralReduction ℓ E T ⋙
          (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory) ⟶
        Functor.mapHomotopyCategory
          (tensorLeft ((Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
            (Mod.regular (condensedRingObj
              (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T)))) (.up ℤ) ⋙
          DerivedCategory.Qh,
      Functor.IsLeftDerivedFunctor
        (integralReduction ℓ E T ⋙
          (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory)
        ε (HomotopyCategory.quasiIso
          (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
            (condensedRingObj (integralCoeff ℓ E) T)) (.up ℤ)) := by
  exact ⟨CategoryTheory.Mod.tensorPresentationDerivedCounit
    (coefficientMap (integralReductionMap ℓ E) T),
    CategoryTheory.Mod.tensorPresentationDerivedCounit_isLeftDerivedFunctor
      (coefficientMap (integralReductionMap ℓ E) T)⟩

end AlgebraicGeometry.ProEtale.CondensedRing

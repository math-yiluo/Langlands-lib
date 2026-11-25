/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
public import WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedFiniteExceptionalAt
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness

/-!
# The relative Hom bijection at a specified compactification

The original existence, dimension-bound and coherent-comparison interface is reexported.
These helpers realize its normalized Hom chain for the right adjoint of the actual
specified compactification, rather than the opaque choice inside HasCompactification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [CompactSpace Y]
  (c : Compactification f)
  [(Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).IsLeftAdjoint]

/-- The specified ordinary etale compact-support right adjoint takes R-nu-star of
bounded-below inputs to bounded-below objects. This is the finite-amplitude step of
the relative adjunction, with the compactification retained literally. -/
theorem specifiedExceptionalEtale_boundedBelow
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) :
    DerivedCategory.TStructure.t.plus
      ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} Λ) c).rightAdjoint.obj
        ((comparisonLowerStar (ModuleCat.{u + 1} Λ) Y).rightDerivedFunctor.obj K.obj)) := by
  let : HasCompactification f := ⟨⟨c⟩⟩
  let adj₁ := Adjunction.ofIsLeftAdjoint
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c)
  let adj₂ := (Etale.rightDerivedUpperShriekAdjunction Λ f).ofNatIsoLeft
    (Etale.rightDerivedLowerShriekIso Λ c).symm
  let e := adj₁.rightAdjointUniq adj₂
  have hR : DerivedCategory.TStructure.t.plus
      ((Etale.rightDerivedUpperShriek Λ f).obj
        ((comparisonLowerStar (ModuleCat.{u + 1} Λ) Y).rightDerivedFunctor.obj K.obj)) := by
    apply Etale.plus_rightDerivedUpperShriek_obj
    exact plus_rightDerivedFunctor_comparisonLowerStar_obj K.property
  exact DerivedCategory.TStructure.t.plus.prop_of_iso (e.app _).symm hR

/-- The normalized Hom chain of the class adjunction, evaluated at an explicit retained
etale origin. The successive factors are alpha, the normalized compact-support
comparison, the comparison adjunction, the specified etale adjunction, full faithfulness
of comparison on a bounded-below target, and alpha again. Every factor is an existing
canonical bijection; this does not choose an arbitrary equivalence from existence. -/
def specifiedExceptionalHomEquiv
    (M : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (W : Scheme.FixedEtaleOriginWitness X Λ M)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) :
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj M.obj ⟶ K.obj) ≃
      (M.obj ⟶ (sfFiniteExceptionalAt Λ c).obj K.obj) :=
  ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).mapIso
      W.iso).symm.homFromEquiv.trans
    (((fixedCompactSupportComparisonIso Λ c).app W.complex).homFromEquiv.trans
      (((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv _ K.obj).trans
        (((Adjunction.ofIsLeftAdjoint
          (Etale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} Λ) c)).homEquiv _ _).trans
          ((Equiv.ofBijective
            (fun a ↦ (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map a)
            (bijective_comparisonUpperStar_mapDerivedCategory_map _ _
              (specifiedExceptionalEtale_boundedBelow Λ c K))).trans
            W.iso.homFromEquiv))))

end AlgebraicGeometry.ProEtale

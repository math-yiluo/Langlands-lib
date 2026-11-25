/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemInterfaces
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels
import WeilConjectures.Algebra.Homology.System.SystemGrothendieck
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.ShrinkYoneda
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator

/-! # Ordinary pro-etale open extension -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
variable (O : Type (u + 1)) [CommRing O] (ell : O)
  {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
  (I : ExceptionalProOrdinaryImage O ell j)

/-- Open restriction on strict pro-etale coefficient systems and on each level has
an extension-by-zero left adjoint.

Source: Stacks 03DI; Zheng Construction 4.1.
(blueprint: lem-sf-pro-open-restriction-right-adjoints).

Proof: weakly etale restriction preserves all small limits on sheaves of sets.
The normalized moduleUnderlying comparison and the conservative limit-preserving
underlying-sheaf functor imply all-limit preservation for every level inverse image.
Evaluation has a left adjoint, so it preserves all small limits. Evaluations jointly
reflect isomorphisms and hence existing limits; inverseEvaluation therefore implies
all-limit preservation for the system inverse image. The coefficient-system category
is equivalent to the Grothendieck abelian category of strict ring systems, and each
level module category is Grothendieck abelian. Apply the special adjoint functor
theorem to their small coseparators. Empty opens and the zero quotient ring obey the
same argument. No finiteness of the rings or boundedness of complexes is needed. -/
theorem exceptionalProOpen_rightAdjoints :
    I.inverse.IsRightAdjoint ∧ ∀ n : ℕ, (I.lift n).modules.IsRightAdjoint := by
  classical
  let groth (T : Scheme.{u}) :
      IsGrothendieckAbelian.{u + 1} (CoefficientSystem (J := Scheme.ProEt.topology T) O ell) := by
    let B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1} :=
      coefficientRings (J := Scheme.ProEt.topology T) (O := O) (ell := ell)
    let e := coefficientSystemEquivalence (J := Scheme.ProEt.topology T) (O := O) (ell := ell)
    let := strictRingSystem_isGrothendieckAbelian B
    exact IsGrothendieckAbelian.of_equivalence e.symm
  let := groth X
  let := groth Z
  have evalRight (T : Scheme.{u}) (n : ℕ) :
      (coefficientEvaluation (J := Scheme.ProEt.topology T)
        (O := O) (ell := ell) n).IsRightAdjoint :=
    ((coefficientOrdinaryEvaluationExtension
      (J := Scheme.ProEt.topology T) (O := O) (ell := ell)).some.adj n).isRightAdjoint
  have evalLimits (T : Scheme.{u}) (n : ℕ) :
      PreservesLimits (coefficientEvaluation (J := Scheme.ProEt.topology T)
        (O := O) (ell := ell) n) := by
    have := evalRight T n
    infer_instance
  let := evalLimits
  have underlyingLimits (T : Scheme.{u}) (n : ℕ) :
      PreservesLimits (coefficientUnderlying (J := Scheme.ProEt.topology T) O ell n) := by
    have : PreservesLimits (coefficientUnderlying (J := Scheme.ProEt.topology T) O ell n ⋙
        sheafToPresheaf (Scheme.ProEt.topology T) (Type (u + 1))) := by
      change PreservesLimits ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _) ⋙
        (whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat.{u + 1}))
      infer_instance
    exact preservesLimits_of_reflects_of_preserves _
      (sheafToPresheaf (Scheme.ProEt.topology T) (Type (u + 1)))
  have levelLimits (n : ℕ) : PreservesLimits (I.lift n).modules := by
    let := underlyingLimits X n
    let := underlyingLimits Z n
    have := Scheme.restriction_preservesLimits j
    have : PreservesLimits ((I.lift n).modules ⋙
        coefficientUnderlying (J := Scheme.ProEt.topology X) O ell n) :=
      preservesLimits_of_natIso (I.lift n).moduleUnderlying.symm
    let : ReflectsLimits (coefficientUnderlying (J := Scheme.ProEt.topology X) O ell n) :=
      reflectsLimits_of_reflectsIsomorphisms
    exact preservesLimits_of_reflects_of_preserves _
      (coefficientUnderlying (J := Scheme.ProEt.topology X) O ell n)
  let := levelLimits
  have conservative : JointlyReflectIsomorphisms
      (coefficientEvaluation (J := Scheme.ProEt.topology X) (O := O) (ell := ell)) := by
    constructor
    intro M N f hf
    let e := coefficientSystemEquivalence (J := Scheme.ProEt.topology X) (O := O) (ell := ell)
    have : IsIso (e.functor.map f) :=
      (strictRingSystem_isIso_iff
        (coefficientRings (J := Scheme.ProEt.topology X) (O := O) (ell := ell))
        (e.functor.map f)).mpr hf
    exact isIso_of_reflects_iso f e.functor
  have : PreservesLimits I.inverse := by
    constructor
    intro K _
    constructor
    intro F
    constructor
    intro c hc
    refine ⟨conservative.jointlyReflectsLimit ?_⟩
    intro n
    have : PreservesLimits (I.inverse ⋙
        coefficientEvaluation (J := Scheme.ProEt.topology X) (O := O) (ell := ell) n) :=
      preservesLimits_of_natIso (I.inverseEvaluation n).symm
    exact isLimitOfPreserves (I.inverse ⋙
      coefficientEvaluation (J := Scheme.ProEt.topology X) (O := O) (ell := ell) n) hc
  constructor
  · exact isRightAdjoint_of_preservesLimits_of_isCoseparating.{u + 1}
      (isCoseparator_coseparator (CoefficientSystem (J := Scheme.ProEt.topology Z) O ell))
      I.inverse
  · intro n
    let := isGrothendieckAbelian_coefficientUniverse
      ((sheafCompose (Scheme.ProEt.topology Z) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficientQuotientSheaf (J := Scheme.ProEt.topology Z) O ell n))
    exact isRightAdjoint_of_preservesLimits_of_isCoseparating.{u + 1}
      (isCoseparator_coseparator (coefficientLevelModules (J := Scheme.ProEt.topology Z) O ell n))
      (I.lift n).modules

end AlgebraicGeometry

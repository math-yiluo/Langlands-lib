/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveClosedCoverRefinement
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# Reflection of integral finite constant models across surjective closed immersions

## References

* Stacks Project, Tags 09AB and 09BK
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The condensed valuation ring of the finite p-adic extension, with continuous-function
sections and the topology of the unique extending spectral absolute value. This merely
specializes the existing continuous coefficient construction. -/
noncomputable def integralModelCondensedCoefficients (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  letI := spectralNorm.normedField (Padic l) E
  Mon.mk (Profinite.continuousCoefficientRingObj (Padic.coefficientExtensionIntegers l E))

/-- The integral condensed coefficient ring is commutative, by its pointwise operations. -/
noncomputable instance integralModelCondensedCoefficients_isCommMonObj
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    IsCommMonObj (integralModelCondensedCoefficients l E).X :=
  letI := spectralNorm.normedField (Padic l) E
  inferInstanceAs (IsCommMonObj
    (Profinite.continuousCoefficientRingObj (Padic.coefficientExtensionIntegers l E)))

attribute [local irreducible] upperStar lowerStar upperStarFromPoint
  CondensedRing.upperStarComp upperStarFromPointComp
  Mod.extendScalarsIsoComapInv

private theorem pointModelPullback {S T : Scheme.{u}} (f : S ⟶ T)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    Nonempty ((CondensedRing.upperStar Λ f).obj
      (((upperStarFromPoint T).mapMod Λ).obj P) ≅
        ((upperStarFromPoint S).mapMod Λ).obj P) := by
  let φ := condensedPullbackHom Λ f
  let N := ((upperStarFromPoint S).mapMod Λ).obj P
  let e := (Functor.mapModCompIso (upperStarFromPoint T) (upperStar Ab.{u + 1} f)
    (upperStarFromPointComp f).hom Λ).app P
  exact ⟨(Mod.extendScalars φ).mapIso e ≪≫
    (Mod.extendScalarsIsoComapInv φ).app ((Mod.comap φ).obj N) ≪≫
      (Mod.comapEquivalenceOfIsIso φ).unitIso.symm.app N⟩

-- Keep the composition comparison abstract when applying it to chosen pullback maps.
private theorem exists_pullback_cover {X Z : Scheme.{u}} (i : Z ⟶ X)
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X) :
    ∃ B : Scheme.Cover.{u} Scheme.proetalePrecoverage Z,
      ∃ (a : B.I₀ → C.I₀) (q : ∀ b, B.X b ⟶ C.X (a b)),
        ∀ b, B.f b ≫ i = q b ≫ C.f (a b) := by
  refine ⟨C.pullback₁ i, id, fun b ↦ pullback.snd i (C.f b), fun b ↦ ?_⟩
  exact pullback.condition

end AlgebraicGeometry.ProEtale

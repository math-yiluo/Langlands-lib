/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.ModuleObjects
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import Mathlib.CategoryTheory.ObjectProperty.Ind
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperBoundedBelowCoproducts
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
public import WeilConjectures.Compactification.Defs

/-!
# Proper pushforward and uniformly bounded coproducts

Both coproducts are ambient unbounded derived coproducts. They are exhibited by colimit
cofans, so their existence is part of the conclusion, rather than an extra hypothesis.
The displayed `desc` is the canonical comparison: its composite with the i-th injection
is the derived pushforward of the i-th source injection. By uniqueness of colimits the
assertion is independent of the exhibited cofans.

Ind-constructibility is `ObjectProperty.ind.{u + 1}` of the recorded finite constant-model
predicate, computed in the module-object category, imposed on every cohomology object.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Proper derived module pushforward commutes with sums of ind-constructible complexes
in a common integer interval, for the finite subextension E of the fixed algebraic closure.
-/
theorem properUnboundedWindowBounded
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p]
    (a b : ℤ) (I : Type (u + 1))
    (M : I → DerivedCategory (pulledBackModuleObjects (Profinite.continuousMapRingObj E) X))
    (hM : ∀ (i : I) (r : ℤ), ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
      ((DerivedCategory.homologyFunctor _ r).obj (M i)))
    (hbound : ∀ (i : I) (r : ℤ), r < a ∨ b < r →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj (M i))) :
    ∃ (c : Cofan M) (_ : IsColimit c)
      (d : Cofan (fun i ↦
        (CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj
          (M i))) (hd : IsColimit d),
      IsIso (hd.desc (Cofan.mk
        ((CondensedRing.lowerStar
          (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj c.pt)
        (fun i ↦ (CondensedRing.lowerStar
          (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.map
          (c.inj i)))) := by
  classical
  -- The existing qcqs theorem only needs the common lower cohomology bound.
  have _ := hM
  let C := pulledBackModuleObjects (Profinite.continuousMapRingObj E) X
  let F := (CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor
  have : HasColimitsOfSize.{u + 1, u + 1} C :=
    IsGrothendieckAbelian.hasColimits C
  have : HasCoproducts.{u + 1} C := fun J ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete J)
  have : HasCoproducts.{u + 1} (DerivedCategory C) := derived_hasCoproducts
  have hN (i : I) : (M i).IsGE a :=
    (DerivedCategory.isGE_iff (M i) a).2 (fun r hr ↦ hbound i r (Or.inl hr))
  have : PreservesColimit (Discrete.functor M) F :=
    CondensedRing.condensed_boundedBelow_preservesCoproduct
      (Profinite.continuousMapRingObj E) p I a M hN
  let c : Cofan M := Cofan.mk (∐ M) (Sigma.ι M)
  let d : Cofan (fun i ↦ F.obj (M i)) :=
    Cofan.mk (F.obj c.pt) (fun i ↦ F.map (c.inj i))
  have hd : IsColimit d :=
    (isColimitMapCoconeCofanMkEquiv F M c.inj).1
      (isColimitOfPreserves F (coproductIsCoproduct M))
  refine ⟨c, coproductIsCoproduct M, d, hd, ?_⟩
  change IsIso (hd.desc d)
  have hid : hd.desc d = 𝟙 d.pt := hd.hom_ext (by simp)
  rw [hid]
  infer_instance

/-- Proper derived module pushforward commutes with sums of ind-constructible complexes
in a common integer interval, for the finite-subextension-valued condensed algebraic closure.
-/
theorem properUnboundedWindowBounded_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p]
    (a b : ℤ) (I : Type (u + 1))
    (M : I → DerivedCategory (pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) X))
    (hM : ∀ (i : I) (r : ℤ), ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
      ((DerivedCategory.homologyFunctor _ r).obj (M i)))
    (hbound : ∀ (i : I) (r : ℤ), r < a ∨ b < r →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj (M i))) :
    ∃ (c : Cofan M) (_ : IsColimit c)
      (d : Cofan (fun i ↦
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj
          (M i))) (hd : IsColimit d),
      IsIso (hd.desc (Cofan.mk
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj c.pt)
        (fun i ↦ (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.map
          (c.inj i)))) := by
  classical
  -- The existing qcqs theorem only needs the common lower cohomology bound.
  have _ := hM
  let C := pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) X
  let F := (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor
  have : HasColimitsOfSize.{u + 1, u + 1} C :=
    IsGrothendieckAbelian.hasColimits C
  have : HasCoproducts.{u + 1} C := fun J ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete J)
  have : HasCoproducts.{u + 1} (DerivedCategory C) := derived_hasCoproducts
  have hN (i : I) : (M i).IsGE a :=
    (DerivedCategory.isGE_iff (M i) a).2 (fun r hr ↦ hbound i r (Or.inl hr))
  have : PreservesColimit (Discrete.functor M) F :=
    CondensedRing.condensed_boundedBelow_preservesCoproduct
      (Profinite.padicAlgClRingObj ℓ) p I a M hN
  let c : Cofan M := Cofan.mk (∐ M) (Sigma.ι M)
  let d : Cofan (fun i ↦ F.obj (M i)) :=
    Cofan.mk (F.obj c.pt) (fun i ↦ F.map (c.inj i))
  have hd : IsColimit d :=
    (isColimitMapCoconeCofanMkEquiv F M c.inj).1
      (isColimitOfPreserves F (coproductIsCoproduct M))
  refine ⟨c, coproductIsCoproduct M, d, hd, ?_⟩
  change IsIso (hd.desc d)
  have hid : hd.desc d = 𝟙 d.pt := hd.hom_ext (by simp)
  rw [hid]
  infer_instance

end AlgebraicGeometry.ProEtale

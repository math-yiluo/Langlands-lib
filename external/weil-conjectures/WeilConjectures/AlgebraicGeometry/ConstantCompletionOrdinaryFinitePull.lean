/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionDerivedPull
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryFinitePullExistence
import WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryFinitePullUniqueness
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback

/-!
# Constant coefficient completion: OrdinaryFinitePull

The ordinary finite pullback comparison (`ordinaryFinitePull_existsUnique`).

Part of the split of `Sheaf.Paper.ConstantCompletionEquivalence`.
Source: Stacks Project, Tags 093M, 099I, 099L, 099M, 0A0E, 06YY and 0940
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

attribute [local irreducible] completed
variable {J A I}
attribute [local irreducible] derivedExtension
attribute [local irreducible] SheafOfModules.monoidalCategory
variable (J A I)
variable {J A I}
attribute [local irreducible] strictLimit
variable (J A I)
attribute [local irreducible] ordinaryUnit
attribute [local irreducible] quotientPresentation
variable {J A I}
variable {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}
variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)
attribute [local semireducible] completed
attribute [local irreducible] completed
variable (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
variable [hL : PreservesFiniteLimits L]
attribute [local irreducible] derivedPull pull change

include V adj hL in
/-- Ordinary constant-coefficient pullback commutes with finite reduction, normalized
by the two insertions. This fixes the canonical tensor reassociation in the quotient
coefficient category. Source: Stacks 06YY, 099L
(auxiliary; not a blueprint node).
Proof: inverse image preserves balanced generators and relations because it preserves
finite products and colimits. Both sides are the same quotient of u^(-1)M. The maps
send a generalized element m to the same class. These generate the tensor sheaf, giving
uniqueness, naturality in M, and compatibility with quotient ring maps. -/
theorem ordinaryFinitePull_existsUnique (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    ∃! e : pull F (constantMap F A) ⋙ change (quotient J' A I n) ≅
        change (quotient J A I n) ⋙ pull F (constantMap F (A ⧸ I ^ (n + 1))),
      ∀ M : Mod (constant J A),
        pullInsertion F (constantMap F A) M ≫
            insertion (quotient J' A I n) ((pull F (constantMap F A)).obj M) ≫
            (underlying (finite J' A I n)).map (e.hom.app M) =
          L.map (insertion (quotient J A I n) M) ≫
            pullInsertion F (constantMap F (A ⧸ I ^ (n + 1)))
              ((change (quotient J A I n)).obj M) := by
  obtain ⟨e, he⟩ := ordinaryFinitePull_exists (J := J) (F := F) (V := V) (adj := adj) A I n
  refine ⟨e, he, ?_⟩
  intro e' he'
  exact (ordinaryFinitePull_unique (J := J) (F := F) (V := V) (adj := adj) A I n e e' he he').symm

end CategoryTheory.ConstantCompletion

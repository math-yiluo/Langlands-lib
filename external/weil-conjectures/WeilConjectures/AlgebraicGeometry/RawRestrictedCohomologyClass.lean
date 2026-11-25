/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonIsIso
import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonNaturality

/-! # The specified raw class of restricted cohomology

Source: Stacks Project, Tag 03Q8, and the comparison square in Tag 0EYM.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The inverse of the specified raw evaluation comparison, cached as a construction.
The inverse is unique, and no raw representative is chosen from mere existence.
Source: Stacks Project, Tags 03Q8 and 0EYM.
(blueprint: def-sc-raw-restricted-cohomology-class). -/
@[irreducible]
noncomputable def rawRestrictedCohomologyClass {S Y : Scheme.{u}} (h : Y ⟶ S)
    (q : ℕ) (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (V : S.Etale)
    (x : rawAffineRestrictedCohomology h q G V) :
    (abelianHigherDirectImageRawPresheaf h q G).obj (op V) := by
  letI := isIso_rawRestrictedCohomologyComparison h q G V
  exact (asIso (rawRestrictedCohomologyComparison h q G V)).inv x

/-- Evaluation recovers the given restricted cohomology class.
Source: Stacks Project, Tag 03Q8.
(blueprint: def-sc-raw-restricted-cohomology-class).

Proof: The construction is the inverse of the evaluation isomorphism. Its
inverse-hom identity, evaluated at x, is the asserted equation. -/
theorem rawRestrictedCohomologyClass_spec {S Y : Scheme.{u}} (h : Y ⟶ S)
    (q : ℕ) (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (V : S.Etale)
    (x : rawAffineRestrictedCohomology h q G V) :
    rawRestrictedCohomologyComparison h q G V
      (rawRestrictedCohomologyClass h q G V x) = x := by
  let := isIso_rawRestrictedCohomologyComparison h q G V
  unfold rawRestrictedCohomologyClass
  exact Iso.inv_hom_id_apply (asIso (rawRestrictedCohomologyComparison h q G V)) x

/-- Pulling back the specified raw class evaluates to the restricted cohomology map.
Source: Stacks Project, Tags 03Q8 and 0EYM.
(blueprint: def-sc-raw-restricted-cohomology-class).

Proof: Apply naturality of raw evaluation to the inverse evaluation class.
Evaluation of that class is the original input by the inverse-hom identity. -/
theorem rawRestrictedCohomologyClass_map {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (q : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ((a)^*[AddCommGrpCat.{u + 1}]).obj F ⟶ F') (V : S.Etale)
    (x : rawAffineRestrictedCohomology h q F V) :
    rawAffineRestrictedCohomologyMap a h h' w q F F' φ V x =
      rawRestrictedCohomologyComparison h' q F' V
        (abelianHigherDirectImageRawPullback a h h' w q F F' φ V
          (rawRestrictedCohomologyClass h q F V x)) := by
  have hn := rawRestrictedCohomologyComparison_naturality a h h' w q F F' φ V
    (rawRestrictedCohomologyClass h q F V x)
  rw [rawRestrictedCohomologyClass_spec] at hn
  exact hn

/-- The canonical raw class commutes with the specified restricted pullback.
Source: Stacks Project, Tags 03Q8 and 0EYM.
(blueprint: def-sc-raw-restricted-cohomology-class).

Proof: Evaluation is injective. Evaluating the left side recovers the restricted
cohomology map, and evaluating the right side gives the same map by naturality. -/
theorem rawRestrictedCohomologyClass_naturality {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (q : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ((a)^*[AddCommGrpCat.{u + 1}]).obj F ⟶ F') (V : S.Etale)
    (x : rawAffineRestrictedCohomology h q F V) :
    rawRestrictedCohomologyClass h' q F' V
      (rawAffineRestrictedCohomologyMap a h h' w q F F' φ V x) =
      abelianHigherDirectImageRawPullback a h h' w q F F' φ V
        (rawRestrictedCohomologyClass h q F V x) := by
  let := isIso_rawRestrictedCohomologyComparison h' q F' V
  apply (ConcreteCategory.bijective_of_isIso (rawRestrictedCohomologyComparison h' q F' V)).1
  rw [rawRestrictedCohomologyClass_spec, ← rawRestrictedCohomologyClass_map]


end AlgebraicGeometry.Etale

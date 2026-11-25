/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!
# The unit comparison map of étale pullbacks

Let `h₁ : T ⟶ S` and `h₂ : S ⟶ R` be morphisms of schemes. For an abelian étale sheaf `G` on
`R`, the unit of `h₁^* ⊣ h₁_*` induces a comparison map
`h₂_* h₂^* G ⟶ (h₁ ≫ h₂)_* (h₁ ≫ h₂)^* G`
(`AlgebraicGeometry.Etale.unitComparison`), compatible with the units of `h₂` and `h₁ ≫ h₂`
(`AlgebraicGeometry.Etale.unit_app_comp_unitComparison`). On sections over an étale `R`-scheme
`W` it is the pullback of sections of `G|_{W ×_R S}` to `W ×_R T`.

Continuity of sections at inverse limits, phrased with these comparison maps, is
`AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Etale

variable {R S T : Scheme.{u}}

/-- The comparison map `h₂_* h₂^* G ⟶ h₁₂_* h₁₂^* G` for `h₁₂ = h₁ ≫ h₂`, induced by the unit of
`h₁^* ⊣ h₁_*` at `h₂^* G` and the composition isomorphisms of pushforwards and pullbacks. -/
noncomputable def unitComparison (h₁ : T ⟶ S) (h₂ : S ⟶ R) (h₁₂ : T ⟶ R)
    (hh₁₂ : h₁₂ = h₁ ≫ h₂) (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (h₂)_*[AddCommGrpCat.{u + 1}].obj ((h₂)^*[AddCommGrpCat.{u + 1}].obj G) ⟶
      (h₁₂)_*[AddCommGrpCat.{u + 1}].obj ((h₁₂)^*[AddCommGrpCat.{u + 1}].obj G) :=
  (h₂)_*[AddCommGrpCat.{u + 1}].map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h₁).unit.app
        ((h₂)^*[AddCommGrpCat.{u + 1}].obj G)) ≫
    (lowerStarComp AddCommGrpCat.{u + 1} h₁ h₂ h₁₂ hh₁₂).hom.app _ ≫
      (h₁₂)_*[AddCommGrpCat.{u + 1}].map
        ((upperStarComp AddCommGrpCat.{u + 1} h₁ h₂ h₁₂ hh₁₂).inv.app G)

/-- The comparison map is compatible with the units: the unit of `h₂` followed by the comparison
map is the unit of `h₁ ≫ h₂`. -/
@[reassoc]
lemma unit_app_comp_unitComparison (h₁ : T ⟶ S) (h₂ : S ⟶ R) (h₁₂ : T ⟶ R)
    (hh₁₂ : h₁₂ = h₁ ≫ h₂) (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h₂).unit.app G ≫
        unitComparison h₁ h₂ h₁₂ hh₁₂ G =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h₁₂).unit.app G := by
  have h := upperStarComp_hom_app_unit_app AddCommGrpCat.{u + 1} h₁ h₂ G h₁₂ hh₁₂
  rw [Adjunction.comp_unit_app] at h
  rw [← cancel_mono ((h₁₂)_*[AddCommGrpCat.{u + 1}].map
    ((upperStarComp AddCommGrpCat.{u + 1} h₁ h₂ h₁₂ hh₁₂).hom.app G)), h, unitComparison]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.comp_obj,
    CategoryTheory.Functor.map_id, Category.comp_id]

end Etale

end AlgebraicGeometry

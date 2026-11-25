/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps
public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
import all WeilConjectures.AlgebraicGeometry.DerivedBaseChangeOpenRestriction
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenComparisonUnit

/-! # Transposition of the canonical base-change map for one open

Source: Stacks Project, Tags 08HY, 08FE and 0D5T.
(blueprint: lem-pc-derived-base-change-open-transpose).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AlgebraicGeometry
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Transposing the open base-change component gives restriction of the transposed
coefficient map followed by the inverse normalized direct-image/open comparison.
There is only one open; no cover, boundary, short exact sequence or shift occurs.
Source: Stacks Tags 08HY (remark-base-change), 08FE
(lemma-restrict-direct-image-open) and 0D5T (lemma-derived-pushforward-composition).
(blueprint: lem-pc-derived-base-change-open-transpose).

Proof: postcompose both maps with the invertible schemeMVOpenComparison hom.
Their common target is the open direct image of the restriction of Rg(K').
Precomposition with the old-open unit is injective on maps into any such right
adjoint object: transpose under its restriction adjunction and cancel restriction
of the unit, which is invertible by schemeDerivedOpen_unit_isIso.
For the first path, naturality of the g Hom equivalence changes precomposition
with that unit to pullback of the unit before the open component. Apply
mvOpenBaseChange_unit: this is ψ followed by the new-open unit. Transpose again
using Hom-equivalence naturality on the right, and apply
schemeMVOpenComparison_unit. The result is the transpose of ψ followed by the
old-open unit at Rg(K'). Naturality of the old-open unit gives the same expression
for the second path. The injectivity and the initial isomorphism cancellation
prove the equation. Empty and top opens and zero ψ satisfy exactly the same unit
identities; no SES boundary, composition-mate computation or shift is needed. -/
theorem derivedBaseChange_open_transpose
    {X X' : Scheme.{u}} (g : X' ⟶ X) (W : X.Opens)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (ψ : (derivedPullback g).obj K ⟶ K') :
    (mvDerivedPullbackAdjunction g).homEquiv
      ((schemeDerivedDirectImage W.ι).obj
        ((schemeOpenRestriction X W).mapDerivedCategory.obj K))
      ((schemeDerivedDirectImage (g ⁻¹ᵁ W).ι).obj
        ((schemeOpenRestriction X' (g ⁻¹ᵁ W)).mapDerivedCategory.obj K'))
      (schemeDerivedBaseChangeMap W.ι (g ⁻¹ᵁ W).ι g
          (g.resLE W (g ⁻¹ᵁ W) le_rfl) (Scheme.Hom.resLE_comp_ι g le_rfl)
          ((schemeOpenRestriction X W).mapDerivedCategory.obj K) ≫
        (schemeDerivedDirectImage (g ⁻¹ᵁ W).ι).map
          ((mvPullbackOpenRestrictionIso g W).inv.app K ≫
            (schemeOpenRestriction X' (g ⁻¹ᵁ W)).mapDerivedCategory.map ψ)) =
      (schemeDerivedDirectImage W.ι).map
        ((schemeOpenRestriction X W).mapDerivedCategory.map
          ((mvDerivedPullbackAdjunction g).homEquiv K K' ψ)) ≫
        (schemeMVOpenComparison g W K').inv := by
  let a := mvDerivedPullbackAdjunction g
  let o := schemeMVAdjunction X W
  let H := (schemeOpenRestriction X W).mapDerivedCategory ⋙ schemeDerivedDirectImage W.ι
  let B := (schemeDerivedDirectImage (g ⁻¹ᵁ W).ι).obj
    ((schemeOpenRestriction X' (g ⁻¹ᵁ W)).mapDerivedCategory.obj K')
  let α := a.homEquiv K K' ψ
  let t := schemeDerivedBaseChangeMap W.ι (g ⁻¹ᵁ W).ι g
      (g.resLE W (g ⁻¹ᵁ W) le_rfl) (Scheme.Hom.resLE_comp_ι g le_rfl)
      ((schemeOpenRestriction X W).mapDerivedCategory.obj K) ≫
    (schemeDerivedDirectImage (g ⁻¹ᵁ W).ι).map
      ((mvPullbackOpenRestrictionIso g W).inv.app K ≫
        (schemeOpenRestriction X' (g ⁻¹ᵁ W)).mapDerivedCategory.map ψ)
  let c := schemeMVOpenComparison g W K'
  change a.homEquiv (H.obj K) B t = H.map α ≫ c.inv
  apply (cancel_mono c.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have : IsIso ((schemeOpenRestriction X W).mapDerivedCategory.map (o.unit.app K)) :=
    schemeDerivedOpen_unit_isIso X W o K
  apply precomp_rightAdjoint_injective o (o.unit.app K)
  have hu : (derivedPullback g).map (o.unit.app K) ≫ t =
      ψ ≫ (schemeMVAdjunction X' (g ⁻¹ᵁ W)).unit.app K' := by
    simpa only [t, o, mvOpenRestrictionAdjunction, schemeMVAdjunction,
      schemeOpenModuleAdjunction, Category.assoc] using mvOpenBaseChange_unit g K K' ψ W
  rw [← Category.assoc, ← a.homEquiv_naturality_left (o.unit.app K) t, hu]
  dsimp only [Functor.id_obj]
  erw [a.homEquiv_naturality_right ψ
    ((schemeMVAdjunction X' (g ⁻¹ᵁ W)).unit.app K')]
  rw [Category.assoc, schemeMVOpenComparison_unit X' X g W K']
  exact o.unit.naturality α


end AlgebraicGeometry

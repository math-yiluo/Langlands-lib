/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
public import Mathlib.AlgebraicGeometry.ResidueField

/-! # Derived test sections and their canonical restriction

Source: Stacks Project, Tags 0D5S and 08HY.
(blueprint: def-sc-picard-derived-model-sections)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

variable [hD : ∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

/-- Test sections are morphisms out of the pulled-back degree-zero structure sheaf.
Source: Stacks Project, Tags 0D5S and 08HY.
(blueprint: def-sc-picard-derived-model-sections) -/
abbrev picardDerivedModelSections {W T : Scheme.{v}}
    (E : schemeDerivedCategory W) (t : T ⟶ W) :=
  (derivedPullback t).obj ((DerivedCategory.singleFunctor
    (SheafOfModules.{v} (moduleRings W.toRingedSpace)) 0).obj
      (SheafOfModules.unit (moduleRings W.toRingedSpace))) ⟶
    (derivedPullback t).obj E

/-- Conjugate pullback of a test section by the canonical derived composition comparison.
Source: Stacks Project, Tag 0D5S.
(blueprint: def-sc-picard-derived-model-sections) -/
def picardDerivedModelRestriction {W T T' : Scheme.{v}}
    (E : schemeDerivedCategory W) (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
    (h : i ≫ t = t') (ξ : picardDerivedModelSections E t) :
    picardDerivedModelSections E t' :=
  let c := (Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))) i t ≪≫
      eqToIso (congrArg (fun g : T' ⟶ W ↦ derivedPullback g) h)
  c.inv.app _ ≫ (derivedPullback i).map ξ ≫ c.hom.app E

/-- The residue point factors through any open neighbourhood, by the open immersion lift.
Source: Stacks Project, Tag 01IQ; Mathlib `IsOpenImmersion.lift`.
(blueprint: def-sc-picard-derived-model-sections) -/
def picardResidueLift (W : Scheme.{v}) (w : W) (V : W.Opens) (hwV : w ∈ V) :
    Spec (W.residueField w) ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι (W.fromSpecResidueField w) (by
    rw [W.range_fromSpecResidueField]
    intro x hx
    have hxw : x = w := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨⟨w, hwV⟩, rfl⟩)

omit hD in
/-- The open lift has the specified composite with the open immersion.
Source: Mathlib `IsOpenImmersion.lift_fac`.
(blueprint: def-sc-picard-derived-model-sections) -/
theorem picardResidueLift_comp (W : Scheme.{v}) (w : W) (V : W.Opens) (hwV : w ∈ V) :
    picardResidueLift W w V hwV ≫ V.ι = W.fromSpecResidueField w := by
  exact IsOpenImmersion.lift_fac _ _ _

end
end AlgebraicGeometry.Scheme

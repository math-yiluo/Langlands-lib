/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedFiberCohomologyFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import all WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde

/-! # Factoring derived fibre cohomology through an open neighbourhood

Source: Stacks Project, Tag 08DW.
(blueprint: new-derived-fiber-open-factorization)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory
namespace AlgebraicGeometry.Scheme

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The residue morphism viewed inside an open neighbourhood of its image. -/
def openResiduePoint (W : Scheme.{v}) (w : W) (U : W.Opens) (hwU : w ∈ U) :
    Spec (W.residueField w) ⟶ U.toScheme :=
  Spec.map (asIso (U.ι.residueFieldMap ⟨w, hwU⟩)).inv ≫
    U.toScheme.fromSpecResidueField ⟨w, hwU⟩

private theorem openResiduePoint_comp (W : Scheme.{v}) (w : W) (U : W.Opens)
    (hwU : w ∈ U) : openResiduePoint W w U hwU ≫ U.ι = W.fromSpecResidueField w := by
  dsimp only [openResiduePoint]
  rw [Category.assoc, ← Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  simp

variable
  [∀ Y : Scheme.{v},
    HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
  [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
    (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]

/-- Fibre cohomology on the localized module site, with its canonical field action. -/
def localDerivedFiberCohomologyFunctor (W : Scheme.{v}) (w : W)
    (U : W.Opens) (hwU : w ∈ U) (i : ℤ) :
    DerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ⥤
        ModuleCat.{v} (W.residueField w) :=
  let V : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      SheafOfModules.{v} (moduleRings U.toScheme.toRingedSpace) :=
    (Modules.overEquiv U).functor
  letI : V.Additive := Functor.additive_of_preserves_binary_products _
  V.mapDerivedCategory ⋙
    derivedPullback (openResiduePoint W w U hwU) ⋙
    DerivedCategory.homologyFunctor
      (SheafOfModules.{v} (moduleRings (Spec (W.residueField w)).toRingedSpace)) i ⋙
    SheafOfModules.evaluation
      (moduleRings (Spec (W.residueField w)).toRingedSpace) (.op ⊤) ⋙
    ModuleCat.restrictScalars (ΓSpecIso (W.residueField w)).inv.hom

/-- A computation rule for the fibre functor, kept separate from its construction. -/
theorem localDerivedFiberCohomologyFunctor_eq (W : Scheme.{v}) (w : W)
    (U : W.Opens) (hwU : w ∈ U) (i : ℤ) :
    let V : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
        SheafOfModules.{v} (moduleRings U.toScheme.toRingedSpace) :=
      (Modules.overEquiv U).functor
    letI : V.Additive := Functor.additive_of_preserves_binary_products _
    localDerivedFiberCohomologyFunctor W w U hwU i =
      V.mapDerivedCategory ⋙ derivedPullback (openResiduePoint W w U hwU) ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{v} (moduleRings (Spec (W.residueField w)).toRingedSpace)) i ⋙
            moduleSpecΓFunctor (R := W.residueField w) := rfl

attribute [irreducible] localDerivedFiberCohomologyFunctor

/-- Restriction to a neighbourhood computes fibre cohomology naturally on derived arrows.
Source: Stacks Project, Tag 08DW, compatibility with restriction to opens.
(blueprint: new-derived-fiber-open-factorization)

Proof: Factor the residue morphism through U using the inverse of the residue-field
map of the open immersion. Derived pullback along U's inclusion is naturally exact
restriction to the localized module site followed by its canonical equivalence
with modules on U.toScheme. Compose this comparison with the natural composition
isomorphism for derived pullback and the factorization equation. Take homology
and field-valued global sections. Every comparison is a natural isomorphism,
so this works for all derived objects and arrows, without perfectness or affinity. -/
theorem derived_fiber_open_factorization (W : Scheme.{v}) (w : W)
    (U : W.Opens) (hwU : w ∈ U) (i : ℤ) :
    Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory ⋙
        localDerivedFiberCohomologyFunctor W w U hwU i ≅
          derivedFiberCohomologyFunctor W w i) := by
  let R := SheafOfModules.overFunctor.{v} (moduleRings W.toRingedSpace) U
  let V : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      SheafOfModules.{v} (moduleRings U.toScheme.toRingedSpace) :=
    (Modules.overEquiv U).functor
  have : V.Additive := Functor.additive_of_preserves_binary_products _
  let g := openResiduePoint W w U hwU
  obtain ⟨a⟩ := pullbackOpenIso W U
  obtain ⟨b⟩ := pullbackCompIso g U.ι
  let θ : R.mapDerivedCategory ⋙ V.mapDerivedCategory ⋙ derivedPullback g ≅
      derivedPullback (W.fromSpecResidueField w) :=
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso R V)
      (derivedPullback g) ≪≫
    Functor.isoWhiskerRight a.symm (derivedPullback g) ≪≫ b ≪≫
    eqToIso (congrArg (fun f ↦ derivedPullback f) (openResiduePoint_comp W w U hwU))
  exact ⟨Functor.isoWhiskerLeft R.mapDerivedCategory
    (eqToIso (localDerivedFiberCohomologyFunctor_eq W w U hwU i)) ≪≫
    Functor.isoWhiskerRight θ
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{v} (moduleRings (Spec (W.residueField w)).toRingedSpace)) i ⋙
        SheafOfModules.evaluation
          (moduleRings (Spec (W.residueField w)).toRingedSpace) (.op ⊤) ⋙
        ModuleCat.restrictScalars (ΓSpecIso (W.residueField w)).inv.hom)⟩

end
end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import Mathlib.CategoryTheory.Triangulated.Functor

public import WeilConjectures.AlgebraicGeometry.SchemeCanonicalTensorShift
import WeilConjectures.AlgebraicGeometry.SchemeCanonicalTensorShiftRightUnitor
/-! # Exactness and unitality of canonical tensor shifts
Source: Stacks Project, Tag 06YH and the Koszul unitor identity.
(blueprint: lem-sc-scheme-canonical-tensor-shift-properties).
-/
@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace DerivedCategory

universe v s
variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{s} C]
  [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C] [HasColimitsOfSize.{0, 0} C]
  [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (.up ℤ))]

attribute [local instance] commShift₂CurriedTensor
open DerivedCategory.TensorCommShift₂

private lemma independent_tensorRight_eq (P : CochainComplex.KFlat C) :
    Functor.CommShift₂.commShiftFlipObj (G := curriedTensor (DerivedCategory C))
      (h := .int) ((LKFlat C).obj P) =
      commShiftTensorRightQhObj ((HomotopyCategory.quotient C _).obj P.obj)
        ((HomotopyCategory.kFlat_quotient_obj_iff _).2 P.2) := by
  exact commShiftTensorRight_eq C P

private lemma independent_tensorRight_exact (K : DerivedCategory C) :
    let : (tensorRight K).CommShift ℤ :=
      Functor.CommShift₂.commShiftFlipObj (h := .int) K
    (tensorRight K).IsTriangulated := by
  let : ∀ K : DerivedCategory C, (tensorRight K).CommShift ℤ :=
    fun K ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) K
  have := Localization.essSurj (LKFlat C) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
  let P := (LKFlat C).objPreimage K
  have hP : (tensorRight ((LKFlat C).obj P)).IsTriangulated := by
    have h := isTriangulated_tensorRightQhObj ((HomotopyCategory.quotient C _).obj P.obj)
      ((HomotopyCategory.kFlat_quotient_obj_iff _).2 P.2)
    rw [← independent_tensorRight_eq] at h
    exact h
  have : NatTrans.CommShift ((curriedTensor (DerivedCategory C)).flip.mapIso
      ((LKFlat C).objObjPreimageIso K)).hom ℤ :=
    Functor.CommShift₂.commShift_flip_map (G := curriedTensor (DerivedCategory C)) (h := .int) _
  exact Functor.isTriangulated_of_iso
    ((curriedTensor (DerivedCategory C)).flip.mapIso ((LKFlat C).objObjPreimageIso K))

end DerivedCategory

namespace AlgebraicGeometry
/-- Canonical tensor shifts are exact and their degree-one right-unitor squares hold.
Source: Stacks Tag 06YH; total-complex shift/unitor calculation used in Tag 08EU.
(blueprint: lem-sc-scheme-canonical-tensor-shift-properties).

Proof. For a fixed K-flat complex the canonical shift comparison agrees with the
comparison descended from tensoring mapping-cone triangles on the homotopy category.
The tensor functor is therefore exact. A K-flat replacement of the fixed factor and
naturality of the two-variable shift comparison transport this to every fixed object.
For the unitor square, use the bifunctor localization comparison with the unit fixed
in the second factor and a K-flat complex P in the first. Expand the comparison's
shift square. The complex right unitor satisfies the Koszul translation identity in
every degree. Naturality of the unitor absorbs the inclusion's shift map. Cancel the
invertible localization shift comparison to obtain the square at Q(P). The identity
functor has its standard shift. Zero factors and the empty scheme give zero maps. -/
theorem schemeCanonicalTensorShift_properties (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    letI := schemeCanonicalTensorShift Y
    letI : ∀ M : schemeDerivedCategory Y, (tensorRight M).CommShift ℤ :=
      fun M => Functor.CommShift₂.commShiftFlipObj (h := .int) M
    (∀ M : schemeDerivedCategory Y, (tensorRight M).IsTriangulated) ∧
      (∀ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
        CochainComplex.IsKFlatTensor (R := Y.sheaf) P →
        let K := DerivedCategory.Q.obj P
        let τ := (rightUnitorNatIso (schemeDerivedCategory Y)).hom
        ((tensorRight (𝟙_ (schemeDerivedCategory Y))).commShiftIso (1 : ℤ)).hom.app K ≫
            (τ.app K)⟦(1 : ℤ)⟧' =
          τ.app (K⟦(1 : ℤ)⟧) ≫ ((𝟭 (schemeDerivedCategory Y)).commShiftIso
            (1 : ℤ)).hom.app K) := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  let := SheafOfModules.symmetricCategory Y.sheaf
  have : MonoidalPreadditive (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed Y.sheaf).1
  let : MonoidalClosed (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed Y.sheaf).2.1
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  have : HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    hasColimitsOfSizeShrink.{0, 0, u, u} _
  have := schemeModule_hasFunctorialFlatResolution Y
  have := DerivedCategory.hasDerivedMonoidalCategory
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  let := schemeCanonicalTensorShift Y
  let : ∀ M : schemeDerivedCategory Y, (tensorRight M).CommShift ℤ :=
    fun M ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) M
  constructor
  · intro M
    exact DerivedCategory.independent_tensorRight_exact _ M
  · exact schemeCanonicalTensorShift_rightUnitor Y

end AlgebraicGeometry

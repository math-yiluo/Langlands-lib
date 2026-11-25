/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree

/-! # Underived affine Hom evaluation

Source: Stacks Project, duality.tex, Tags 0BUZ, 0BV0, and 0AX3.
-/

@[expose] public section
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Identify restricted algebra-Hom with Hom from the pushed-forward structure sheaf,
compatibly with its evaluation counit.

Source: Stacks Project, duality.tex, Tags 0BUZ, 0BV0, and 0AX3.
(blueprint: lem-sc-underived-affine-hom-counit)

Proof: The restriction of the unit of f_*O_X is definitionally equal to f_* of
the unit of O_X: sections and restriction maps are identical, as are their
O_Y-module structures. Thus iH itself supplies j. On each open U and section φ,
precomposition with O_Y → f_*O_X followed by canonical unit-Hom evaluation
returns iH(φ) applied to the image of 1 under the ring map. This image is 1.
The hypothesis h_eval identifies the result with the counit. Extensionality on
opens and sections proves the equality. This also applies to the empty scheme
and zero section rings. -/
theorem underived_affine_hom_counit
    {Y X : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (H : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))
      [H.Additive]
      (iH : H ⋙ SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩ ≅
        (SheafOfModules.homFunctor Y.sheaf).obj
          (op ((SheafOfModules.restrictScalars
            (R := moduleRings Y.toRingedSpace)
            (R' := moduleRings (directImageAlgebraSpace f))
            ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).obj
              (SheafOfModules.unit (moduleRings (directImageAlgebraSpace f))))))
      (adj₀ : SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩ ⊣ H)
    (h_eval : ∀ (F : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (U : Y.Opens)
          (φ : (H.obj F).val.obj (op U)),
        ((adj₀.counit.app F).val.app (op U)).hom φ =
          ((((iH.hom.app F).val.app (op U)).hom φ).app (op (Over.mk (𝟙 U)))).hom
            (1 : (moduleRings (directImageAlgebraSpace f)).obj.obj (op U)))
    : ∀ F : SheafOfModules.{u} (moduleRings Y.toRingedSpace),
        iH.hom.app F ≫
          ((SheafOfModules.homFunctor Y.sheaf).map
            (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).op).app F ≫
          (SheafOfModules.homObjUnitIso (R := Y.sheaf) F).hom = adj₀.counit.app F := by
  intro F
  apply SheafOfModules.hom_ext
  ext U φ
  change ((((iH.hom.app F).val.app U).hom φ).app
    (op (Over.mk (𝟙 U.unop)))).hom ((f.c.app U).hom 1) =
      ((adj₀.counit.app F).val.app U).hom φ
  rw [map_one]
  exact (h_eval F U.unop φ).symm

end AlgebraicGeometry

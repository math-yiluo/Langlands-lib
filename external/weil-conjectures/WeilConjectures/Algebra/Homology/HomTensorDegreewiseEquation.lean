/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.KFlat

/-!
# Degreewise currying equation interface

Source: Stacks Project, Cohomology on Sites, Lemma 21.34.1, Tag 0A90.
(blueprint: def-sc-hom-tensor-degreewise-equation)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

/-- The product projections of the chosen Hom complex. These are the projections
specified together with its bifunctor in `homComplex_exists` (Stacks, Section 0A8X).
(blueprint: def-sc-hom-tensor-degreewise-equation) -/
noncomputable def homTensorCurryProjection (L M : CochainComplex Mod ℤ)
    (n p q : ℤ) (h : p + n = q) :
    (homComplex (R := R) L M).X n ⟶ SheafOfModules.homObj (R := R) (L.X p) (M.X q) :=
  (Classical.choose (Classical.choose_spec (homComplex_exists (R := R)))) L M n p q h

/-- Map from the sectionwise presheaf tensor to the underlying sheaf tensor.
It is the sheafification unit followed by the inverse of the tensor comparison.
Source: Stacks, Modules on Sites, Section 03EK.
(blueprint: def-sc-hom-tensor-degreewise-equation) -/
noncomputable def homTensorCurrySectionMap (A B : Mod) :
    letI := SheafOfModules.monoidalCategory R
    A.val ⊗ B.val ⟶ (A ⊗ B).val := by
  let := SheafOfModules.monoidalCategory R
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
      (A.val ⊗ B.val) ≫
        (SheafOfModules.tensorObjIsoSheafification (R := R) A B).inv.val

set_option synthInstance.maxSize 256 in
/-- The degreewise comparison sends `x ⊗ y` to `f(x)(y)` on every localized site.
The equation uses pure tensors before sheafification; it therefore does not assert
that every section of a sheaf tensor is a sum of global pure tensors.
Source: Stacks, Tag 0A90, degreewise construction.
(blueprint: def-sc-hom-tensor-degreewise-equation) -/
def HomTensorDegreewiseEquation (K L M : CochainComplex Mod ℤ) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    ((homComplex (R := R) K (homComplex (R := R) L M)).X n ⟶
      (homComplex (R := R)
        (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M).X n) → Prop := by
  let := SheafOfModules.monoidalCategory R
  intro a
  exact ∀ (p q : ℤ) (U : Cᵒᵖ)
    (s : (homComplex (R := R) K (homComplex (R := R) L M)).X n |>.val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : (K.X p).val.obj (op W.unop.left))
    (y : (L.X q).val.obj (op W.unop.left)),
    let φ := ((homTensorCurryProjection R
      (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M
      n (p + q) (p + q + n) rfl).val.app U).hom ((a.val.app U).hom s)
    let ψ := ((homTensorCurryProjection R K (homComplex (R := R) L M)
      n p (p + n) rfl).val.app U).hom s
    let χ := ((homTensorCurryProjection R L M (p + n) q (p + q + n)
      (by omega)).val.app (op W.unop.left)).hom ((ψ.app W).hom x)
    (φ.app W).hom
      (((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
        p q (p + q) rfl).val.app (op W.unop.left)).hom
        (((homTensorCurrySectionMap R (K.X p) (L.X q)).app (op W.unop.left)).hom
          (x ⊗ₜ[R.obj.obj (op W.unop.left)] y))) =
      (χ.app (op (Over.mk (𝟙 W.unop.left)))).hom y

end CategoryTheory

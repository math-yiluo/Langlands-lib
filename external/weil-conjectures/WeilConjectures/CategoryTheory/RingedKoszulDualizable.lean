/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import WeilConjectures.Algebra.Homology.Monoidal.Dual
import WeilConjectures.CategoryTheory.Monoidal.Dualizable

/-! # Dualizability of the actual positive Koszul stages

Source: Stacks Project, sites-cohomology.tex, Tag 08JJ; more-algebra.tex, Tag 0913.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  SheafOfModules.monoidalClosed

local instance koszulDualizableMonoidalPreadditive : MonoidalPreadditive (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  (SheafOfModules.tensorClosed O).1.some

local instance koszulDualizableHasColimitsOfSize : HasColimitsOfSize.{0, 0} (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  hasColimitsOfSizeShrink.{0, 0, u, u} _

private theorem factor_dualizable
    (s : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    IsDualizable (ringedKoszulFactor O s m) := by
  let K := ringedKoszulFactor O s m
  have : K.IsStrictlyGE 0 := (K.isStrictlyGE_iff 0).mpr fun n hn ↦
    HomologicalComplex.isZero_double_X _ _ n (by omega) (by omega)
  have : K.IsStrictlyLE 1 := (K.isStrictlyLE_iff 1).mpr fun n hn ↦
    HomologicalComplex.isZero_double_X _ _ n (by omega) (by omega)
  apply CochainComplex.isDualizable_of_isStrictlyGE_of_isStrictlyLE 0 1
  intro n
  by_cases h0 : n = 0
  · subst n
    exact isDualizable_unit.of_iso (HomologicalComplex.doubleXIso₀ _ _).symm
  · by_cases h1 : n = 1
    · subst n
      exact isDualizable_unit.of_iso (HomologicalComplex.doubleXIso₁ _ _ (by decide)).symm
    · exact CategoryTheory.IsZero.isDualizable
        (HomologicalComplex.isZero_double_X _ _ n h0 h1)

/-- Every actual finite positive Koszul stage is dualizable as an ordinary complex.
Source: Stacks 08JJ, 0913 (auxiliary; not a blueprint node).

Proof: one factor has the unit in degrees zero and one, and zero elsewhere.
These terms are dualizable, so the bounded-complex dual construction gives a dual
for the factor. Induct on the number of factors, using dualizability of the unit
for the empty tensor and closure under tensor products for the successor. -/
theorem ringedKoszulStage_dualizable (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    IsDualizable ((ringedKoszulDiagram O r b).obj m) := by
  induction r with
  | zero => exact isDualizable_unit
  | succ r ih =>
    exact (factor_dualizable O (b 0) m).tensorObj (ih (fun i ↦ b i.succ))

end CategoryTheory

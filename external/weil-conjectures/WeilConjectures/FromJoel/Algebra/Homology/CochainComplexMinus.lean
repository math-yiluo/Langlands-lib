/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.CategoryTheory.ObjectProperty.Shift

/-!
# C^-

Migrated from `Mathlib/Algebra/Homology/CochainComplexMinus.lean`
on the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

open CategoryTheory Limits

namespace CochainComplex

variable (C : Type*) [Category C]

protected def minus [HasZeroMorphisms C] : ObjectProperty (CochainComplex C ℤ) :=
  fun K ↦ ∃ (n : ℤ), K.IsStrictlyLE n

instance [HasZeroMorphisms C] : (CochainComplex.minus C).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro _ _ e ⟨n, _⟩
    exact ⟨n, isStrictlyLE_of_iso e n⟩

/-- Bounded above complexes are stable under the shift. Through Mathlib's
`ObjectProperty.hasShift` and `ObjectProperty.commShiftι`, this equips `C^-` with a shift and
the inclusion `C^- ⥤ C(C)` with a commutation with shifts. -/
instance [Preadditive C] : (CochainComplex.minus C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K ⟨k, _⟩ ↦ ⟨k - n, K.isStrictlyLE_shift k n _ (by omega)⟩⟩

abbrev Minus [HasZeroMorphisms C] :=
  (CochainComplex.minus C).FullSubcategory

namespace Minus

section

variable [HasZeroMorphisms C]

abbrev ι : Minus C ⥤ CochainComplex C ℤ := ObjectProperty.ι _

def fullyFaithfulι : (ι C).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

instance : (ι C).Full := ObjectProperty.full_ι _
instance : (ι C).Faithful := ObjectProperty.faithful_ι _

def quasiIso [CategoryWithHomology C] : MorphismProperty (Minus C) :=
  (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).inverseImage (ι C)

instance [CategoryWithHomology C] : (quasiIso C).RespectsIso := by
  dsimp [quasiIso]; infer_instance

end

end Minus

end CochainComplex

namespace CategoryTheory

namespace Functor

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

section

variable [HasZeroMorphisms C] [HasZeroMorphisms D] [F.PreservesZeroMorphisms]

set_option backward.defeqAttrib.useBackward true in
@[simps!]
def mapCochainComplexMinus : CochainComplex.Minus C ⥤ CochainComplex.Minus D :=
  ObjectProperty.lift _ (CochainComplex.Minus.ι C ⋙ F.mapHomologicalComplex _) (fun K => by
    obtain ⟨i, hi⟩ := K.2
    refine ⟨i, ?_⟩
    dsimp [CochainComplex.Minus.ι]
    infer_instance)

@[simps!]
def mapCochainComplexMinusCompι :
    F.mapCochainComplexMinus ⋙ CochainComplex.Minus.ι D ≅
      CochainComplex.Minus.ι C ⋙ F.mapHomologicalComplex _ := Iso.refl _

end

end Functor

end CategoryTheory

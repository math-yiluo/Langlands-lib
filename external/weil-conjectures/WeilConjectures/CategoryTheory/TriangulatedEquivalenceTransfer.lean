/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Shift.Induced
import Mathlib.CategoryTheory.Preadditive.Transfer
import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Transferring triangulated structures across an equivalence

Source: Stacks Project, Derived Categories, Tags 05QK and 05QL.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

open Limits

/-- An equivalent category inherits a triangulated structure with a compatible shift.
Source: Stacks Project, Derived Categories, Tags 05QK and 05QL, the axioms for exact
functors and triangulated categories
(blueprint: lem-pc-triangulated-equivalence-transfer).

Proof: Transport the additive groups on Hom sets along the fully faithful inverse
functor. The image of a zero object is zero. Define the shift by conjugating each
shift functor by the equivalence, with coherence maps induced by its unit and counit.
These shifts are additive since all factors are additive. Declare a triangle to be
distinguished if it is isomorphic to the image of a distinguished triangle of C.
The unit and counit identify rotations, contractible triangles and triangle morphisms
with their originals. Therefore the existence of cone triangles, completion of
triangle morphisms and the octahedral axiom all transport along the equivalence.
Both directions preserve distinguished triangles, and the inverse shift compatibility
is the one induced by the adjunction of the equivalence. No nonempty generating
family or compactness hypothesis is used. -/
theorem triangulatedEquivalenceTransfer
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    (e : C ≌ D) :
    ∃ (_ : HasZeroObject D) (_ : HasShift D ℤ) (_ : Preadditive D)
      (_ : ∀ n : ℤ, (shiftFunctor D n).Additive) (_ : Pretriangulated D)
      (_ : IsTriangulated D) (_ : e.functor.CommShift ℤ),
      let := e.commShiftInverse ℤ
      e.functor.IsTriangulated ∧ e.inverse.IsTriangulated := by
  let pD := Preadditive.ofFullyFaithful e.fullyFaithfulInverse
  let : Preadditive D := pD
  let : e.inverse.Additive := e.fullyFaithfulInverse.additive_ofFullyFaithful
  let : e.functor.Additive := e.symm.additive_inverse_of_FullyFaithful
  let zD : HasZeroObject D := (Functor.map_isZero e.functor (isZero_zero C)).hasZeroObject
  let : HasZeroObject D := zD
  let s := fun n : ℤ ↦ e.inverse ⋙ shiftFunctor C n ⋙ e.functor
  let j : ∀ n : ℤ, e.functor ⋙ s n ≅ shiftFunctor C n ⋙ e.functor := fun n ↦
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e.unitIso.symm _ ≪≫ (Functor.leftUnitor _)
  let sD := HasShift.induced e.functor ℤ s j
  let : HasShift D ℤ := sD
  let cD := Functor.CommShift.ofInduced e.functor ℤ s j
  let : e.functor.CommShift ℤ := cD
  let aD : ∀ n : ℤ, (shiftFunctor D n).Additive := by
    intro n
    change (s n).Additive
    dsimp [s]
    infer_instance
  let : ∀ n : ℤ, (shiftFunctor D n).Additive := aD
  let W := MorphismProperty.isomorphisms C
  let : e.functor.IsLocalization W :=
    Functor.IsLocalization.of_isEquivalence e.functor W (le_refl _)
  let : W.HasLeftCalculusOfFractions := by
    exact
      { exists_leftFraction := fun {X Y} φ ↦ by
          let : IsIso φ.s := φ.hs
          exact ⟨{ Y' := Y, f := inv φ.s ≫ φ.f, s := 𝟙 Y, hs := inferInstance }, by simp⟩
        ext := fun {X' X Y} f₁ f₂ s hs h ↦ by
          let : IsIso s := hs
          exact ⟨_, 𝟙 _, inferInstance, by simpa using (cancel_epi s).mp h⟩ }
  let : W.IsCompatibleWithTriangulation := by
    refine
      { condition := ?_
        compatible_with_triangulation := ?_ }
    · intro n
      ext X Y f
      change IsIso ((shiftFunctor C n).map f) ↔ IsIso f
      constructor
      · intro h
        let := h
        exact isIso_of_reflects_iso f (shiftFunctor C n)
      · intro h
        let := h
        infer_instance
    · intro T₁ T₂ hT₁ hT₂ a b ha hb h
      let : IsIso a := ha
      let : IsIso b := hb
      let φ := Pretriangulated.completeDistinguishedTriangleMorphism T₁ T₂ hT₁ hT₂ a b h
      exact ⟨φ.hom₃,
        Pretriangulated.isIso₃_of_isIso₁₂ φ hT₁ hT₂ ha hb,
        φ.comm₂, φ.comm₃⟩
  let tD := Triangulated.Localization.pretriangulated e.functor W
  let : Pretriangulated D := tD
  let : e.functor.IsTriangulated := Triangulated.Localization.isTriangulated_functor
    e.functor W
  let iD := Triangulated.Localization.isTriangulated e.functor W
  let : IsTriangulated D := iD
  refine ⟨zD, sD, pD, aD, tD, iD, cD, inferInstance, ?_⟩
  let := e.commShiftInverse ℤ
  let : e.CommShift ℤ := e.commShift_of_functor ℤ
  exact Functor.isTriangulated_of_precomp_iso e.unitIso.symm

end CategoryTheory

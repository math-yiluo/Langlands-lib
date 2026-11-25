/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable

/-!
# The dual of a bounded complex of dualizable objects

A strictly bounded complex `P` of dualizable objects, concentrated in degrees `[a, b]`, has a
right dual in `D(A)` which lies in degrees `≤ -a`
(`DerivedCategory.exists_exactPairing_Q_obj`): it is the image of the termwise dual complex
`P^∨` (`CochainComplex.rightDual`), concentrated in degrees `[-b, -a]`. This refines
`DerivedCategory.isDualizable_Q_obj` by keeping track of the dual.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]

local instance localInstance_DualizableBounded_1 : HasColimitsOfSize.{0, 0} A :=
  hasColimitsOfSizeShrink A

/-- A bounded complex `P` of dualizable objects in degrees `[a, b]` has a right dual in `D(A)`
lying in degrees `≤ -a`. -/
theorem exists_exactPairing_Q_obj (P : CochainComplex A ℤ) (a b : ℤ) [P.IsStrictlyGE a]
    [P.IsStrictlyLE b] (hP : ∀ n, IsDualizable (P.X n)) :
    ∃ (Y : DerivedCategory A) (_ : ExactPairing (Q.obj P) Y), Y.IsLE (-a) := by
  let _ : ∀ n, HasRightDual (P.X n) := fun n ↦ (hP n).some
  let _ := CochainComplex.exactPairingRightDual P a b
  let H := HomotopyCategory.quotient A (.up ℤ)
  have hP' : ∀ n, IsDualizable (P.rightDual.X n) := fun n ↦
    ⟨{ rightDual := P.X (-n)
       exact := (BraidedCategory.exactPairing_swap (P.X (-n)) (P.X (-n))ᘁ :) }⟩
  let X : (HomotopyCategory.quasiIso A (.up ℤ)).kFlat.FullSubcategory :=
    ⟨H.obj P, (HomotopyCategory.kFlat_quotient_obj_iff _).2
      (CochainComplex.kFlat_of_bounded_of_flat P a b (fun n ↦ (hP n).flat))⟩
  let Y : (HomotopyCategory.quasiIso A (.up ℤ)).kFlat.FullSubcategory :=
    ⟨H.obj P.rightDual, (HomotopyCategory.kFlat_quotient_obj_iff _).2
      (CochainComplex.kFlat_of_bounded_of_flat P.rightDual (-b) (-a) (fun n ↦ (hP' n).flat))⟩
  let _ : ExactPairing ((ObjectProperty.ι _).obj X) ((ObjectProperty.ι _).obj Y) :=
    ExactPairing.map H P P.rightDual
  let _ : ExactPairing X Y := ExactPairing.ofFullyFaithful (ObjectProperty.ι _) X Y
  let _ := Functor.Monoidal.ofLaxMonoidal (kFlatQh A)
  let _ : ExactPairing ((kFlatQh A).obj X) ((kFlatQh A).obj Y) := ExactPairing.map (kFlatQh A) X Y
  let e : Q.obj P ≅ (kFlatQh A).obj X := ((quotientCompQhIso A).app P).symm
  refine ⟨(kFlatQh A).obj Y, exactPairingCongrLeft e, ?_⟩
  exact (TStructure.t (C := A)).isLE_of_iso ((quotientCompQhIso A).app P.rightDual).symm (-a)

end DerivedCategory

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.Monoidal.Dual
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-!
# Bounded complexes of dualizable objects are dualizable in the derived category

Let `A` be a braided monoidal closed Grothendieck abelian category with functorial flat
resolutions. A bounded complex `P` of dualizable objects of `A` is dualizable in `D(A)` for the
derived tensor product: its termwise dual `P^∨` is paired with `P` in the category of complexes
(`CochainComplex.exactPairingRightDual`), both `P` and `P^∨` are bounded complexes of flat
objects, hence K-flat, and `Qh : K(A) ⥤ D(A)` is monoidal on K-flat complexes.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]

local instance localInstance_Dualizable_1 : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A

instance : IsIso (ε (Qh : _ ⥤ DerivedCategory A)) := inferInstanceAs (IsIso (𝟙 _))

/-- The lax monoidal structure `Qh K ⊗ᴸ Qh L ⟶ Qh (K ⊗ L)` is an isomorphism when `K` is
K-flat. -/
lemma isIso_μ_Qh_of_kFlat (K L : HomotopyCategory A (.up ℤ))
    (hK : (HomotopyCategory.quasiIso A (.up ℤ)).kFlat K) : IsIso (μ Qh K L) :=
  have := isLeftDerivedFunctor₂CurriedTensor A
  (MorphismProperty.kFlat_prod_id_derives_curriedTensor (HomotopyCategory.quasiIso A (.up ℤ))
    Qh).isIso_of_isLeftDerivabilityStructure (LF := curriedTensor (DerivedCategory A))
      (μNatTrans Qh) ⟨K, hK⟩ L

variable (A) in
/-- The restriction of `Qh : K(A) ⥤ D(A)` to the K-flat complexes. -/
noncomputable abbrev kFlatQh :
    (HomotopyCategory.quasiIso A (.up ℤ)).kFlat.FullSubcategory ⥤ DerivedCategory A :=
  (HomotopyCategory.quasiIso A (.up ℤ)).kFlat.ι ⋙ Qh

instance : IsIso (ε (kFlatQh A)) := by
  rw [Functor.LaxMonoidal.comp_ε, ObjectProperty.ι_ε, CategoryTheory.Functor.map_id,
    Category.comp_id]
  exact inferInstanceAs (IsIso (𝟙 _))

instance (X Y : (HomotopyCategory.quasiIso A (.up ℤ)).kFlat.FullSubcategory) :
    IsIso (μ (kFlatQh A) X Y) := by
  rw [Functor.LaxMonoidal.comp_μ, ObjectProperty.ι_μ, CategoryTheory.Functor.map_id,
    Category.comp_id]
  exact isIso_μ_Qh_of_kFlat _ _ X.property

/-- A bounded complex of dualizable objects is dualizable in the derived category. -/
theorem isDualizable_Q_obj (P : CochainComplex A ℤ) (a b : ℤ) [P.IsStrictlyGE a]
    [P.IsStrictlyLE b] (hP : ∀ n, IsDualizable (P.X n)) : IsDualizable (Q.obj P) := by
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
  have h : IsDualizable ((kFlatQh A).obj X) :=
    ⟨{ rightDual := (kFlatQh A).obj Y, exact := ExactPairing.map (kFlatQh A) X Y }⟩
  exact IsDualizable.of_iso ((quotientCompQhIso A).app P) h

/-- A bounded complex `P` of objects with chosen right duals is paired in the derived category
with its termwise dual complex `P.rightDual`: the image of the chain-level pairing
`CochainComplex.exactPairingRightDual` is an exact pairing of `Q.obj P` and
`Q.obj P.rightDual`. -/
theorem nonempty_exactPairing_Q_obj (P : CochainComplex A ℤ) (a b : ℤ) [P.IsStrictlyGE a]
    [P.IsStrictlyLE b] [∀ n, HasRightDual (P.X n)] :
    Nonempty (ExactPairing (Q.obj P) (Q.obj P.rightDual)) := by
  let _ := CochainComplex.exactPairingRightDual P a b
  let H := HomotopyCategory.quotient A (.up ℤ)
  have hP (n : ℤ) : IsDualizable (P.X n) := ⟨inferInstance⟩
  have hP' (n : ℤ) : IsDualizable (P.rightDual.X n) :=
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
  let _ : ExactPairing ((kFlatQh A).obj X) ((kFlatQh A).obj Y) :=
    ExactPairing.map (kFlatQh A) X Y
  exact ⟨exactPairingCongr (X' := (kFlatQh A).obj X) (Y' := (kFlatQh A).obj Y)
    ((quotientCompQhIso A).app P).symm
    ((quotientCompQhIso A).app P.rightDual).symm⟩

end DerivedCategory

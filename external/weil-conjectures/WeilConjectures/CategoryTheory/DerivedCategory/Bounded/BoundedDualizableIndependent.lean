/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable

/-! # Bounded dualizable complexes with an independent localization universe

Source: Stacks Project, Tag 0FNS; the termwise dual construction.
-/

@[expose] public section
set_option autoImplicit false

universe v u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace DerivedCategory
variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{w} A] [Abelian.HasFunctorialFlatResolution A]

local instance instHasColimitsOfSize_boundedDualizableIndependent
    : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A

/-- A bounded complex of dualizable objects remains dualizable after localization
in any supported universe.
Source: Stacks 0FNS; the bounded termwise dual argument.
Proof: equip every term with a right dual and form the signed dual complex.
Both complexes are bounded and flat, hence K-flat. The homotopy quotient sends
their pairing to an exact pairing. On K-flat objects the derived localization
has invertible tensorators and unit, so it preserves the exact pairing.
Transport along the canonical composite-localization comparison.
(blueprint: lem-sf-bounded-dualizable-independent). -/
theorem isDualizable_Q_obj_independent (P : CochainComplex A ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] (hP : ∀ n, IsDualizable (P.X n)) :
    IsDualizable (Q.obj P) := by
  let _ : ∀ n, HasRightDual (P.X n) := fun n ↦ (hP n).some
  let _ := CochainComplex.exactPairingRightDual P a b
  let H := HomotopyCategory.quotient (A) (.up ℤ)
  have hd' (n : ℤ) : IsDualizable (P.rightDual.X n) :=
    ⟨{ rightDual := P.X (-n)
       exact := BraidedCategory.exactPairing_swap (P.X (-n)) (P.X (-n))ᘁ }⟩
  let W := HomotopyCategory.quasiIso (A) (.up ℤ)
  let F : W.kFlat.FullSubcategory ⥤ DerivedCategory (A) := W.kFlat.ι ⋙ Qh
  have : IsIso (Functor.LaxMonoidal.ε F) := by
    dsimp only [F]
    rw [Functor.LaxMonoidal.comp_ε, ObjectProperty.ι_ε,
      CategoryTheory.Functor.map_id, Category.comp_id]
    exact inferInstanceAs (IsIso (Functor.LaxMonoidal.ε (toDerivedMonoidal Qh W)))
  have (U V : W.kFlat.FullSubcategory) : IsIso (Functor.LaxMonoidal.μ F U V) := by
    dsimp only [F]
    rw [Functor.LaxMonoidal.comp_μ, ObjectProperty.ι_μ,
      CategoryTheory.Functor.map_id, Category.comp_id]
    exact DerivedMonoidal.isIso_counit_app_app_of_kFlat_left Qh W U.obj V.obj U.property
  let _ := Functor.Monoidal.ofLaxMonoidal F
  let U : W.kFlat.FullSubcategory :=
    ⟨H.obj P, (HomotopyCategory.kFlat_quotient_obj_iff _).2
      (CochainComplex.kFlat_of_bounded_of_flat P a b (fun n ↦ (hP n).flat))⟩
  let V : W.kFlat.FullSubcategory :=
    ⟨H.obj P.rightDual, (HomotopyCategory.kFlat_quotient_obj_iff _).2
      (CochainComplex.kFlat_of_bounded_of_flat P.rightDual (-b) (-a) (fun n ↦ (hd' n).flat))⟩
  let _ : ExactPairing ((ObjectProperty.ι _).obj U) ((ObjectProperty.ι _).obj V) :=
    ExactPairing.map H P P.rightDual
  let _ : ExactPairing U V := ExactPairing.ofFullyFaithful (ObjectProperty.ι _) U V
  have h : IsDualizable (F.obj U) :=
    ⟨{ rightDual := F.obj V, exact := ExactPairing.map F U V }⟩
  exact h.of_iso ((quotientCompQhIso _).app P)

end DerivedCategory

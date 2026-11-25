/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import all WeilConjectures.CategoryTheory.Monoidal.Closed.DualizableCoefficientHomAction

/-! # A dualizable factor in the second variable of internal Hom -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace CategoryTheory.MonoidalClosed

/-- The evaluation-defined exchange is invertible for a dualizable last factor.
Source: Stacks 08JD, 08JJ, 08JC.
Proof: choose a dual D of Q. Tensoring by D is left adjoint to tensoring by Q.
Compose this adjunction with the tensor-K/closed-Hom adjunction in the two orders.
The associator identifies their left adjoints, so uniqueness identifies their right
adjoints. Their counits show that this isomorphism is precisely the transpose of
reassociation followed by evaluation tensored with Q.
(blueprint: lem-per-dualizable-second-hom-exchange). -/
theorem isIso_ihomTensorToIhom_of_isDualizable
    {C : Type*} [Category* C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] (K L Q : C) (hQ : IsDualizable Q) :
    IsIso (ihomTensorToIhom K L Q) := by
  obtain ⟨hQ⟩ := hQ
  let := hQ
  let := BraidedCategory.exactPairing_swap Q Qᘁ
  exact isIso_coefficientTranspose K (ihom.adjunction K) L Qᘁ Q

end CategoryTheory.MonoidalClosed

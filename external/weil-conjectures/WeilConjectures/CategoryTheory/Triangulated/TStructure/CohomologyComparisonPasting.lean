/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart

/-! # Pasting canonical truncation and cohomology comparisons

Source: BBD, Proposition 1.3.3(i)--(ii), Theorem 1.3.6, printed pp. 29--31.
The transformation, composition and pasting calculations are the agent argument extracted
from the coefficient-stage descent proof, rather than a verbatim BBD theorem
(blueprint: lem-a1-cohomology-comparison-pasting).

Cohomology is written using the existing `truncGELE j j` followed by the j-shift.
All equations are in the ambient category; the heart is a full subcategory.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uC vC uD vD uB vB uE vE uA vA uZ vZ

namespace CategoryTheory.Triangulated.TStructure

open Limits

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [triC : IsTriangulated C]
  {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [triD : IsTriangulated D]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B]
  [HasShift B ℤ] [∀ n : ℤ, (shiftFunctor B n).Additive]
  [Pretriangulated B] [triB : IsTriangulated B]
  {E : Type uE} [Category.{vE} E] [Preadditive E] [HasZeroObject E]
  [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive]
  [Pretriangulated E] [triE : IsTriangulated E]
  {A : Type uA} [Category.{vA} A] [Preadditive A] [HasZeroObject A]
  [HasShift A ℤ] [∀ n : ℤ, (shiftFunctor A n).Additive]
  [Pretriangulated A] [triA : IsTriangulated A]
  {Z : Type uZ} [Category.{vZ} Z] [Preadditive Z] [HasZeroObject Z]
  [HasShift Z ℤ] [∀ n : ℤ, (shiftFunctor Z n).Additive]
  [Pretriangulated Z] [triZ : IsTriangulated Z]

variable (tC : TStructure C) (tD : TStructure D)
  (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [hF : F.IsTExact tC tD]

end CategoryTheory.Triangulated.TStructure

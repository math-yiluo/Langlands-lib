/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Filtration


public import WeilConjectures.CategoryTheory.CanonicalFiltration
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Subquotients and cycle notation for filtered cochain complexes

Source: Stacks Project, Homology, Section 12.24 (Tag 012K), displayed cycle and boundary
formulas (blueprint: def-sp-filtered-complex-subquotients).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : CochainComplex C ℤ} (F : DecreasingFiltration K)

/-- The degreewise filtration step is the image of the subcomplex inclusion in degree `n`.
Source: Stacks, Tag 012K (blueprint: def-sp-filtered-complex-subquotients). -/
noncomputable def complexStep (p n : ℤ) : Subobject (K.X n) :=
  imageSubobject ((F.step p).arrow.f n)

/-- The quotient complex `FᵃK / FᵇK`, for `a ≤ b`, is the cokernel of the inclusion.
Source: Stacks, Tag 012K (blueprint: def-sp-filtered-complex-subquotients). -/
noncomputable def complexQuotient (a b : ℤ) (h : a ≤ b) : CochainComplex C ℤ :=
  cokernel (Subobject.ofLE (F.step b) (F.step a) (F.antitone_step h))

/-- The canonical projection to the quotient complex.
Source: Stacks, Tag 012K (blueprint: def-sp-filtered-complex-subquotients). -/
noncomputable def complexQuotientπ (a b : ℤ) (h : a ≤ b) :
    (F.step a : CochainComplex C ℤ) ⟶ F.complexQuotient a b h :=
  cokernel.π (Subobject.ofLE (F.step b) (F.step a) (F.antitone_step h))

/-- The unquotiented cycles inside `FᵖKⁿ`: intersection with the inverse image of `Fᵖ⁺ʳ`.
Source: Stacks, Tag 012K (blueprint: def-sp-filtered-complex-subquotients). -/
noncomputable def complexCycleRepresentatives (p n r : ℤ) :
    Subobject ((F.step p : CochainComplex C ℤ).X n) :=
  (Subobject.pullback ((F.step p).arrow.f n)).obj
    (F.complexStep p n ⊓ (Subobject.pullback (K.d n (n + 1))).obj
      (F.complexStep (p + r) (n + 1)))

/-- Cycles as a subobject of `grᵖKⁿ`: add `Fᵖ⁺¹`, restrict to `Fᵖ`, and take its image
under the graded projection. Source: Stacks, Tag 012K
(blueprint: def-sp-filtered-complex-subquotients). -/
noncomputable def complexCycles (p n r : ℤ) :
    Subobject ((F.gradedPiece p).X n) :=
  (Subobject.«exists»
    ((F.complexQuotientπ p (p + 1) (Int.le_add_one (show p ≤ p from le_rfl))).f n)).obj
    ((Subobject.pullback ((F.step p).arrow.f n)).obj
      ((F.complexStep p n ⊓ (Subobject.pullback (K.d n (n + 1))).obj
        (F.complexStep (p + r) (n + 1))) ⊔ F.complexStep (p + 1) n))

/-- Boundaries as a subobject of `grᵖKⁿ`: intersect `Fᵖ` with the image of `d(Fᵖ⁻ʳ⁺¹)`,
add `Fᵖ⁺¹`, restrict to `Fᵖ`, and project. Source: Stacks, Tag 012K
(blueprint: def-sp-filtered-complex-subquotients). -/
noncomputable def complexBoundaries (p n r : ℤ) :
    Subobject ((F.gradedPiece p).X n) :=
  (Subobject.«exists»
    ((F.complexQuotientπ p (p + 1) (Int.le_add_one (show p ≤ p from le_rfl))).f n)).obj
    ((Subobject.pullback ((F.step p).arrow.f n)).obj
      ((F.complexStep p n ⊓ (Subobject.«exists» (K.d (n - 1) n)).obj
        (F.complexStep (p - r + 1) (n - 1))) ⊔ F.complexStep (p + 1) n))

end CategoryTheory.DecreasingFiltration

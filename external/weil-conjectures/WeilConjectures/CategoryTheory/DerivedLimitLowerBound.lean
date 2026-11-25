/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # A common lower bound for a sequential derived limit

Source: the Roos-triangle argument in Step 6 of
`lem-pur-zero-section-bottom-coefficients`, refining the universal case of
`thm-pur-localized-top-chern.proof.md`, Step 3.
-/

@[expose] public section
set_option autoImplicit false

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- The Roos derived limit preserves a common cohomological lower bound.
Source: blueprint `thm-pur-localized-top-chern.proof.md`, Step 3, universal
zero-section case, native integral-coefficient refinement, Step 6.
(blueprint: lem-pur-roos-common-lower-bound).

Proof: orthogonality tests the lower bound of the product: a map from an object
in degrees at most a-1 is zero after every projection and hence is zero. In the
Roos triangle L -> product K -> product K -> L[1], the exact segment from
H^(q-1)(product K) through H^q(L) to H^q(product K) has zero outer terms for
q<a. Thus H^q(L)=0. This includes a=0 and q=-1 and uses no surjectivity of the
supported transition maps. -/
theorem isGE_of_isDerivedLimit
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : ℕ → DerivedCategory A) [HasProduct K]
    (f : ∀ n, K (n + 1) ⟶ K n) (L : DerivedCategory A)
    (hL : IsDerivedLimit f L) (a : ℤ) (hK : ∀ n, (K n).IsGE a) : L.IsGE a := by
  have hP : (∏ᶜ K).IsGE a := by
    refine (DerivedCategory.TStructure.t.isGE_iff_orthogonal (a - 1) a (by omega) _).2 ?_
    intro Y g hY
    apply Pi.hom_ext
    intro n
    rw [zero_comp]
    exact DerivedCategory.TStructure.t.zero_of_isLE_of_isGE _ (a - 1) a
      (by omega) hY (hK n)
  obtain ⟨p, δ, hT⟩ := hL
  apply (DerivedCategory.isGE_iff L a).2
  intro q hq
  have hExact := DerivedCategory.HomologySequence.exact₁
    (Triangle.mk p (towerTransitionEndomorphism f) δ) hT (q - 1) q (by omega)
  let := hP
  exact hExact.isZero_of_both_isZero
    (DerivedCategory.isZero_of_isGE (∏ᶜ K) a (q - 1) (by omega))
    (DerivedCategory.isZero_of_isGE (∏ᶜ K) a q hq)

end CategoryTheory

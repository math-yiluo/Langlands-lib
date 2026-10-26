import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Renard's Noether isomorphisms and complementary subobjects

Statements of Renard 2026, Appendix A.VI.2(9), printed page 263 / PDF page 269,
on actual categorical subobjects, their chosen inclusions and actual cokernels.
-/

namespace Langlands.Renard

open CategoryTheory CategoryTheory.Limits

universe u v

/-- Renard A.VI.2(9)(i): for subobjects `A ≤ B` of `X`, the canonical map
`B/A ⟶ X/A` induced by `B.arrow` is a monomorphism, and the cokernel of this map
is isomorphic to `X/B` compatibly with the two quotient projections from `X`. -/
def NestedQuotientIsoStatement (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ (X : C) (A B : Subobject X) (h : A ≤ B),
    let j := cokernel.map (Subobject.ofLE A B h) A.arrow (𝟙 (A : C)) B.arrow (by simp);
    Mono j ∧
      ∃ e : cokernel j ≅ cokernel B.arrow,
        cokernel.π A.arrow ≫ cokernel.π j ≫ e.hom = cokernel.π B.arrow

/-- Renard A.VI.2(9)(ii): `B/(A ⊓ B) ≅ (A ⊔ B)/A`, by an isomorphism compatible
with the projection from `B` and the inclusion `B ⟶ A ⊔ B`. -/
def SecondIsoStatement (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ (X : C) (A B : Subobject X),
    ∃ e : cokernel (Subobject.ofLE (A ⊓ B) B inf_le_right) ≅
        cokernel (Subobject.ofLE A (A ⊔ B) le_sup_left),
      cokernel.π (Subobject.ofLE (A ⊓ B) B inf_le_right) ≫ e.hom =
        Subobject.ofLE B (A ⊔ B) le_sup_right ≫
          cokernel.π (Subobject.ofLE A (A ⊔ B) le_sup_left)

/-- Renard's consequence of A.VI.2(9)(ii): if `A ⊓ B = ⊥` and `A ⊔ B = ⊤`, the
map `A ⊕ B ⟶ X` induced by the two subobject inclusions is an isomorphism. -/
def ComplementarySubobjectsSumStatement (C : Type u) [Category.{v} C] [Abelian C] :
    Prop :=
  ∀ (X : C) (A B : Subobject X),
    A ⊓ B = ⊥ → A ⊔ B = ⊤ → IsIso (coprod.desc A.arrow B.arrow)

/-- The combined statement family of Renard A.VI.2(9). -/
def NoetherIsomorphismsStatement (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  NestedQuotientIsoStatement C ∧ SecondIsoStatement C ∧
    ComplementarySubobjectsSumStatement C

end Langlands.Renard

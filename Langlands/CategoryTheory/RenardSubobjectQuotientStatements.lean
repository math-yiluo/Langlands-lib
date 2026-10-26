import Mathlib.CategoryTheory.Abelian.Subobject

/-! Statements of Renard 2026, Appendix A.VI.2(2–3), in the orders of A.I.2. -/

namespace Langlands.Renard

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

/-- Actual kernel and cokernel maps are inverse on subobject and quotient classes,
reverse the source orders, and agree with the categorical maps on representatives. -/
def SubobjectQuotientCorrespondenceStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ X : C,
    (∀ P : Subobject X, kernelOrderHom X (cokernelOrderHom X P) = P) ∧
    (∀ K : Subobject (op X),
      cokernelOrderHom X (kernelOrderHom X (OrderDual.toDual K)) =
        OrderDual.toDual K) ∧
    (∀ P Q : Subobject X,
      P ≤ Q ↔
        OrderDual.ofDual (cokernelOrderHom X Q) ≤
          OrderDual.ofDual (cokernelOrderHom X P)) ∧
    (∀ K L : Subobject (op X),
      K ≤ L ↔
        kernelOrderHom X (OrderDual.toDual L) ≤
          kernelOrderHom X (OrderDual.toDual K)) ∧
    (∀ (Y : C) (i : Y ⟶ X) [Mono i],
      cokernelOrderHom X (Subobject.mk i) =
        OrderDual.toDual (Subobject.mk (cokernel.π i).op)) ∧
    (∀ (Y : C) (p : X ⟶ Y) [Epi p],
      kernelOrderHom X (OrderDual.toDual (Subobject.mk p.op)) =
        Subobject.mk (kernel.ι p))

/-- Binary intersections and sums are the actual infimum and supremum of
categorical subobjects, with their universal order properties. -/
def BinarySubobjectLatticeStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ (X : C) (P Q : Subobject X),
    (∀ R : Subobject X, R ≤ P ⊓ Q ↔ R ≤ P ∧ R ≤ Q) ∧
    (∀ R : Subobject X, P ⊔ Q ≤ R ↔ P ≤ R ∧ Q ≤ R)

/-- The combined statement family of Renard A.VI.2(2–3). -/
def SubobjectQuotientAndLatticeStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  SubobjectQuotientCorrespondenceStatement C ∧ BinarySubobjectLatticeStatement C

end Langlands.Renard

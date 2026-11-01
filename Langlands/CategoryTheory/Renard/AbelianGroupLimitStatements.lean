import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Group.ULift

/-!
# Renard A.IV.2: products and direct sums of abelian groups

Statement-only descriptions of the actual Cartesian product and DirectSum
models, their universal properties, and the finite-support comparison.
Index and group universes are independent; individual factors are lifted
to the common category containing both concrete models.
-/

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard.AbelianGroupLimit

universe uI uG

/-- The Cartesian product, with coordinate projections into lifted factors,
is a product in the common ambient category of abelian groups. -/
def CartesianProductStatement : Prop :=
  ∀ (I : Type uI) (G : I → AddCommGrpCat.{uG}),
    let H : I → AddCommGrpCat.{max uI uG} :=
      fun i => AddCommGrpCat.of (ULift.{uI} (G i))
    let p : Fan H :=
      Fan.mk (AddCommGrpCat.of (∀ i, G i)) fun i =>
        AddCommGrpCat.ofHom
          (((AddEquiv.ulift : ULift.{uI} (G i) ≃+ G i).symm.toAddMonoidHom).comp
            (Pi.evalAddMonoidHom (fun i => G i) i))
    Nonempty (IsLimit p)

/-- The actual direct sum, with its single-coordinate inclusions from
lifted factors, is a coproduct in the common ambient category. -/
def DirectSumCoproductStatement : Prop := by
  classical
  exact ∀ (I : Type uI) (G : I → AddCommGrpCat.{uG}),
    let H : I → AddCommGrpCat.{max uI uG} :=
      fun i => AddCommGrpCat.of (ULift.{uI} (G i))
    let c : Cofan H :=
      Cofan.mk (AddCommGrpCat.of (DirectSum I (fun i => G i))) fun i =>
        AddCommGrpCat.ofHom
          ((DirectSum.of (fun i => G i) i).comp
            (AddEquiv.ulift : ULift.{uI} (G i) ≃+ G i).toAddMonoidHom)
    Nonempty (IsColimit c)

/-- The direct sum embeds into the full product as exactly the finite-support
families, and its inclusions become the usual product single inclusions. -/
def FiniteSupportComparisonStatement : Prop := by
  classical
  exact ∀ (I : Type uI) (G : I → AddCommGrpCat.{uG}),
    let e := DirectSum.coeFnAddMonoidHom (fun i => G i)
    Function.Injective e ∧
      (∀ x : ∀ i, G i,
        x ∈ Set.range e ↔ Set.Finite {i | x i ≠ 0}) ∧
      (∀ i : I,
        e.comp (DirectSum.of (fun i => G i) i) =
          AddMonoidHom.single (fun i => G i) i)

/-- For a finite index type, the full Cartesian product with its usual
single-coordinate inclusions is itself a coproduct of the lifted factors. -/
def FiniteProductCoproductStatement : Prop := by
  classical
  exact ∀ (I : Type uI) [Finite I] (G : I → AddCommGrpCat.{uG}),
    let H : I → AddCommGrpCat.{max uI uG} :=
      fun i => AddCommGrpCat.of (ULift.{uI} (G i))
    let c : Cofan H :=
      Cofan.mk (AddCommGrpCat.of (∀ i, G i)) fun i =>
        AddCommGrpCat.ofHom
          ((AddMonoidHom.single (fun i => G i) i).comp
            (AddEquiv.ulift : ULift.{uI} (G i) ≃+ G i).toAddMonoidHom)
    Nonempty (IsColimit c)

/-- The concrete product and direct-sum example in source order, with the
coordinate comparison before its finite-product specialization. -/
def AbelianGroupLimitStatements : Prop :=
  CartesianProductStatement.{uI, uG} ∧
    DirectSumCoproductStatement.{uI, uG} ∧
      FiniteSupportComparisonStatement.{uI, uG} ∧
        FiniteProductCoproductStatement.{uI, uG}

end Langlands.Renard.AbelianGroupLimit

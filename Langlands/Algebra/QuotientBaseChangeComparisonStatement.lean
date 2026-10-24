import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Canonical base change of a quotient comparison -/

universe u v w

open scoped TensorProduct

namespace Langlands.Algebra

/-- Equal extended ideals make the actual comparison of quotient algebras
bijective after base change. The second conclusion records the same comparison
in the left-tensor linear-map convention used by the local injectivity criterion.
This proposition states the comparison; it does not prove it. -/
def QuotientBaseChangeComparisonStatement : Prop :=
  ∀ (R : Type u) (B : Type v) (T : Type w)
    [CommRing R] [CommRing B] [CommRing T] [Algebra R B] [Algebra R T]
    (I J : Ideal B) (hIJ : I ≤ J),
    I.map (algebraMap B (B ⊗[R] T)) = J.map (algebraMap B (B ⊗[R] T)) →
    Function.Bijective
      (Algebra.TensorProduct.map (Ideal.Quotient.factorₐ R hIJ) (AlgHom.id R T)) ∧
    Function.Bijective
      (LinearMap.lTensor T (Ideal.Quotient.factorₐ R hIJ).toLinearMap)

end Langlands.Algebra

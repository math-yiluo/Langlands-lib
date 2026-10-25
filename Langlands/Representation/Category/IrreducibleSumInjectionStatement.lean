import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RepresentationTheory.Irreducible

/-! The actual sum map from two inequivalent irreducible representations. -/

namespace Langlands

universe uK uG uV uW uX

/-- Nonzero intertwiners from two inequivalent irreducibles into one
representation give an injective sum map on their actual binary product. -/
def IrreducibleSumInjectionStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (A : Rep.{uV} k G) (B : Rep.{uW} k G) (C : Rep.{uX} k G),
    Representation.IsIrreducible A.ρ →
    Representation.IsIrreducible B.ρ →
    ¬ Nonempty (A.ρ.Equiv B.ρ) →
    ∀ (f : A.ρ.IntertwiningMap C.ρ) (g : B.ρ.IntertwiningMap C.ρ),
      f ≠ 0 → g ≠ 0 →
        Function.Injective
          (f.comp (Representation.IntertwiningMap.fst k A.ρ B.ρ) +
            g.comp (Representation.IntertwiningMap.snd k A.ρ B.ρ))

end Langlands

import Langlands.Global.AdelicFunctoriality.NormStatement

/-! # Determinant compatibility and quotient descent as exact reductions -/

namespace Langlands.Global.AdelicFunctoriality

open NumberField
open scoped NumberField

universe u v

/-- The principal-norm identity implies a unique continuous descent of the
constructed idelic norm to the actual principal-idele quotients. -/
def IdeleClassNormDescent : Prop :=
  PrincipalNormCompatibility.{u, v} →
    ∀ (K : Type u) (L : Type v) [Field K] [Field L]
      [NumberField K] [NumberField L] [Algebra K L],
      ∃! f : IdeleClassGroup (𝓞 L) L →ₜ* IdeleClassGroup (𝓞 K) K,
        ∀ a : IdeleGroup (𝓞 L) L,
          f (QuotientGroup.mk a) = QuotientGroup.mk (ideleNorm (K := K) a)

/-- The two reductions needed to assemble the global norm theorem from the
separate completed tensor comparison. Neither premise is asserted here. -/
def NormAssembly : Prop :=
  (CompletedTensorComparison.{u, v} → PrincipalNormCompatibility.{u, v}) ∧
    IdeleClassNormDescent.{u, v}

end Langlands.Global.AdelicFunctoriality

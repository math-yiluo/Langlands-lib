import Langlands.BaseChange.CuspidalSigmaLift
import Langlands.BaseChange.PseudoCoefficient
import Langlands.JacquetLanglands.EssentiallySquareIntegrable

/-!
# Decomposition of σ-discrete series into an orbit of discrete series

The forward implication of Arthur–Clozel, Chapter 1, Lemma 2.8, and Henniart–Lemaire,
II.4.6, for cyclic extensions of characteristic-zero nonarchimedean local fields.
-/

namespace Langlands.BaseChange

universe u v uW

/-- A σ-discrete series of positive rank is the normalized parabolic product of the
conjugates in one orbit of an irreducible square-integrable representation, each
occurring once. -/
def SigmaDiscreteSeriesOrbitDecompositionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l n : ℕ), IsCyclicAlgebra σ l → 0 < n →
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (P : Representation ℂ (GeneralLinear n E) W), IsSigmaDiscreteSeries σ n P →
      ∃ (t m : ℕ) (hm : 0 < m) (h : t * m = n)
        (X : Type uW) (_ : AddCommGroup X) (_ : Module ℂ X)
        (Q : Representation ℂ (GeneralLinear m E) X),
        Q.IsIrreducible ∧ JacquetLanglands.IsSquareIntegrable Q ∧
        (∀ i : ℕ, Nonempty (Q.Equiv (Q.comp (entrywiseAut (σ ^ i) m).toMonoidHom)) ↔ t ∣ i) ∧
        Nonempty (P.Equiv ((sigmaOrbitProduct σ t hm Q).comp
          (GeneralLinear.reindex (R := E) (finCongr h)).symm.toMonoidHom))

end Langlands.BaseChange

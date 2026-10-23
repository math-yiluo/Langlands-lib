import Langlands.Representation.Geometric.WeylDefinitions
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Generic real parameters for a nested pair of standard GL Levis

The concrete permutation predicate and the open-dense statement specialize
Silberger 1978, Lemma 5.2. No representation-theoretic comparison is assumed.
-/

namespace Langlands

open GeneralLinear Geometric

/-- Regular coarse determinant exponents for which every fine-partition Weyl
permutation fixing the shifted exponent lies in the coarse Levi Weyl group. -/
def IsRelativeGenericParameter {n : ℕ} (B C : BlockShape n)
    (v₀ : Fin B.length → ℝ) (t : Fin C.length → ℝ) : Prop :=
  Function.Injective t ∧
    ∀ w : Equiv.Perm (Fin n),
      (∀ a b, blockIndex B (w a) = blockIndex B (w b) ↔
        blockIndex B a = blockIndex B b) →
      (∀ a, v₀ (blockIndex B (w a)) - t (blockIndex C (w a)) =
        v₀ (blockIndex B a) - t (blockIndex C a)) →
      w ∈ blockWeyl C

/-- The generic parameters form an open dense subset of the entire real
coarse exponent space. The fine blocks must lie inside coarse blocks. -/
def GLRelativeGenericParameterStatement : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (B C : BlockShape n),
    (∀ a b : Fin n, blockIndex B a = blockIndex B b →
      blockIndex C a = blockIndex C b) →
    ∀ v₀ : Fin B.length → ℝ,
      IsOpen {t : Fin C.length → ℝ | IsRelativeGenericParameter B C v₀ t} ∧
        Dense {t : Fin C.length → ℝ | IsRelativeGenericParameter B C v₀ t}

end Langlands

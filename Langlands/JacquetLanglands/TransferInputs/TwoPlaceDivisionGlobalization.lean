import Langlands.Algebra.BrauerGroup
import Langlands.LocalField.Definitions
import Langlands.Shimura.Unitary.FiniteScalarExtension
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-! # Global realization of a local division algebra at two places -/

noncomputable section

universe u

namespace Langlands.JacquetLanglands

open NumberField hiding FinitePlace
open Global Langlands.Brauer
open Shimura.FiniteUnitary (IsDivisionAt IsSplitAt)
open scoped TensorProduct

/-- A local division algebra of degree `n` in characteristic zero has a global
division model of degree `n` over a totally complex number field. The model
has division completions at the given place and a second finite place,
splits everywhere else, and has a third finite place available. -/
def TwoPlaceDivisionGlobalizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (D : Type u) [DivisionRing D] [Algebra F D] [FiniteDimensional F D]
    [Algebra.IsCentral F D] [TopologicalSpace D] [IsModuleTopology F D] (n : ℕ),
    Module.finrank F D = n ^ 2 →
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsTotallyComplex K)
      (v w r : FinitePlace K) (A : CSA.{0, 0} K) (e : FiniteCompletion K v ≃+* F)
      (f : FiniteCompletion K v ⊗[K] A ≃+* D),
      v ≠ w ∧ v ≠ r ∧ w ≠ r ∧
      Module.finrank K A = n ^ 2 ∧ (∀ x : A, x ≠ 0 → IsUnit x) ∧
      IsDivisionAt K A v ∧ IsDivisionAt K A w ∧
      (∀ p : FinitePlace K, p ≠ v → p ≠ w → IsSplitAt K A p n) ∧
      Nonempty (InfiniteAdeles K ⊗[K] A ≃ₐ[InfiniteAdeles K]
        Matrix (Fin n) (Fin n) (InfiniteAdeles K)) ∧
      Continuous e ∧ Continuous e.symm ∧
      (letI := moduleTopology (FiniteCompletion K v) (FiniteCompletion K v ⊗[K] A)
       Continuous f ∧ Continuous f.symm) ∧
      ∀ x : FiniteCompletion K v,
        f (algebraMap (FiniteCompletion K v) (FiniteCompletion K v ⊗[K] A) x) =
          algebraMap F D (e x)

end Langlands.JacquetLanglands

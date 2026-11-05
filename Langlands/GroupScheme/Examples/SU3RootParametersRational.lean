import Langlands.GroupScheme.Examples.SU3RootParametersQuadratic

noncomputable section
open scoped TensorProduct
open Algebra

namespace Langlands.GroupScheme.SU3Root

universe u v

variable (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
  [IsQuadraticExtension k L] [Algebra.IsSeparable k L]

local instance : FiniteDimensional k L :=
  .of_finrank_pos (by rw [IsQuadraticExtension.finrank_eq_two k L]; decide)

/-- An actual element of field trace one, obtained from separability. -/
def traceOne : L := Classical.choose (Algebra.trace_surjective k L 1)

@[simp] theorem trace_traceOne : Algebra.trace k L (traceOne k L) = 1 :=
  Classical.choose_spec (Algebra.trace_surjective k L 1)

theorem traceOne_add_conjugate :
    traceOne k L + conjugation k L (traceOne k L) = 1 := by
  rw [← algebraMap_trace, trace_traceOne, map_one]

/-- Root parameters after identifying the rational tensor algebra with the extension field. -/
abbrev rationalParameters := Parameters (fieldInvolution k L)

/-- The trace-one formula supplies a point above every first coordinate. -/
def rationalLift (u : L) : rationalParameters k L :=
  ⟨(u, traceOne k L * (u * conjugation k L u)), by
    change traceOne k L * (u * conjugation k L u) +
      conjugation k L (traceOne k L * (u * conjugation k L u)) =
        u * conjugation k L u
    simp only [map_mul, conjugation_involutive k L u]
    calc
      _ = (traceOne k L + conjugation k L (traceOne k L)) *
          (u * conjugation k L u) := by ring
      _ = _ := by rw [traceOne_add_conjugate, one_mul]⟩

@[simp] theorem rationalLift_first (u : L) : (rationalLift k L u).first = u := rfl

@[simp] theorem rationalLift_second (u : L) :
    (rationalLift k L u).second = traceOne k L * (u * conjugation k L u) := rfl

/-- Surjectivity is proved here at the actual field-valued points. -/
theorem rational_firstHom_surjective :
    Function.Surjective (Parameters.firstHom (fieldInvolution k L)) := by
  intro u
  exact ⟨rationalLift k L (Multiplicative.toAdd u), rfl⟩

instance rationalCentralNormal : (Parameters.central (fieldInvolution k L)).Normal :=
  inferInstanceAs (Parameters.firstHom (fieldInvolution k L)).ker.Normal

/-- The quotient by the central trace-zero subgroup is the additive extension field. -/
def rationalQuotientEquiv :
    rationalParameters k L ⧸ Parameters.central (fieldInvolution k L) ≃*
      Multiplicative L :=
  QuotientGroup.quotientKerEquivOfRightInverse
    (Parameters.firstHom (fieldInvolution k L))
    (fun u => rationalLift k L (Multiplicative.toAdd u)) (fun _ => rfl)

@[simp] theorem rationalQuotientEquiv_mk (x : rationalParameters k L) :
    rationalQuotientEquiv k L (QuotientGroup.mk x) = Multiplicative.ofAdd x.first := rfl

/-- The canonical tensor left-unit equivalence commutes with the actual conjugations. -/
theorem rationalTensor_bar (x : k ⊗[k] L) :
    Algebra.TensorProduct.lid k L ((tensorInvolution k L k).bar x) =
      (fieldInvolution k L).bar (Algebra.TensorProduct.lid k L x) := by
  change Algebra.TensorProduct.lid k L (tensorConjugation k L k x) =
    conjugation k L (Algebra.TensorProduct.lid k L x)
  induction x using TensorProduct.inductionOn with
  | tmul r x => simp only [tensorConjugation_tmul, Algebra.TensorProduct.lid_tmul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The group-valued functor at k is identified with the actual field coordinate group. -/
def rationalParametersEquiv : tensorParameters k L k ≃* rationalParameters k L :=
  Parameters.mapEquiv (Algebra.TensorProduct.lid k L).toRingEquiv (rationalTensor_bar k L)

@[simp] theorem rationalParametersEquiv_first (x : tensorParameters k L k) :
    (rationalParametersEquiv k L x).first = Algebra.TensorProduct.lid k L x.first := rfl

@[simp] theorem rationalParametersEquiv_second (x : tensorParameters k L k) :
    (rationalParametersEquiv k L x).second = Algebra.TensorProduct.lid k L x.second := rfl

theorem rationalParametersEquiv_mem_central (x : tensorParameters k L k) :
    rationalParametersEquiv k L x ∈ Parameters.central (fieldInvolution k L) ↔
      x ∈ Parameters.central (tensorInvolution k L k) := by
  simp only [Parameters.mem_central, rationalParametersEquiv_first]
  exact (Algebra.TensorProduct.lid k L).map_eq_zero_iff

end Langlands.GroupScheme.SU3Root

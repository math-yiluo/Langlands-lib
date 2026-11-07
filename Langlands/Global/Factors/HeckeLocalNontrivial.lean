import Langlands.Global.Factors.HeckeAdditiveComponents
import Mathlib.Topology.Algebra.PontryaginDual

/-! # Local nontriviality from the actual adelic multiplication pairing -/

noncomputable section

namespace Langlands.Global.HeckeFunctionalEquation

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- Multiplication by a single finite coordinate remains supported there. -/
theorem finiteAdditiveInclusion_mul (v : FinitePlace K)
    (x : FiniteCompletion K v) (a : Adeles K) :
    finiteAdditiveInclusion K v x * a =
      finiteAdditiveInclusion K v (x * finiteProjection K v a) := by
  classical
  apply Prod.ext
  · change (0 : InfiniteAdeles K) * a.1 = 0
    exact zero_mul _
  · exact (RestrictedProduct.single_mul _ v x a.2).symm

/-- Multiplication by a single infinite coordinate remains supported there. -/
theorem infiniteAdditiveInclusion_mul (v : InfinitePlace K)
    (x : InfiniteCompletion K v) (a : Adeles K) :
    infiniteAdditiveInclusion K v x * a =
      infiniteAdditiveInclusion K v (x * infiniteProjection K v a) := by
  classical
  apply Prod.ext
  · funext w
    change (Pi.single v x : ∀ w, InfiniteCompletion K w) w * a.1 w =
      (Pi.single v (x * a.1 v) : ∀ w, InfiniteCompletion K w) w
    by_cases h : w = v
    · subst w
      simp
    · simp [Pi.single_eq_of_ne h]
  · change (0 : FiniteAdeles K) * a.2 = 0
    exact zero_mul _

/-- The actual restriction to an infinite completion as an additive character. -/
def infiniteAdditiveRestriction
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K)) (v : InfinitePlace K) :
    AddChar (InfiniteCompletion K v) Circle :=
  ψ.toAddChar.compAddMonoidHom (infiniteAdditiveInclusion K v)

theorem continuous_infiniteAdditiveRestriction
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K)) (v : InfinitePlace K) :
    Continuous (infiniteAdditiveRestriction ψ v) :=
  ψ.continuous_toFun.comp (continuous_infiniteAdditiveInclusion K v)

section Pairing

variable (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (e : Multiplicative (Adeles K) ≃ₜ* PontryaginDual (Multiplicative (Adeles K)))
    (he : ∀ a x : Multiplicative (Adeles K),
      e a x = ψ (Multiplicative.toAdd a * Multiplicative.toAdd x))

include e he

/-- Injectivity of the supplied multiplication-pairing equivalence detects zero. -/
theorem eq_zero_of_pairing_trivial (a : Adeles K)
    (h : ∀ x : Adeles K, ψ (a * x) = 1) : a = 0 := by
  change Multiplicative.ofAdd a = Multiplicative.ofAdd (0 : Adeles K)
  apply e.injective
  apply PontryaginDual.ext
  intro x
  rw [he, he]
  simpa using h (Multiplicative.toAdd x)

/-- The finite restriction is nontrivial whenever the actual multiplication
pairing is the supplied injective equivalence. -/
theorem finiteAdditiveRestriction_ne_one_of_pairing (v : FinitePlace K) :
    finiteAdditiveRestriction ψ v ≠ 1 := by
  classical
  intro h
  have hzero : finiteAdditiveInclusion K v 1 = 0 := by
    apply eq_zero_of_pairing_trivial ψ e he
    intro a
    rw [finiteAdditiveInclusion_mul]
    have hx := congrArg (fun θ : AddChar (FiniteCompletion K v) Circle =>
      θ (finiteProjection K v a)) h
    simpa [finiteAdditiveRestriction] using hx
  have hcoord := congrArg (finiteProjection K v) hzero
  have hbad : (1 : FiniteCompletion K v) = 0 := by
    change (Pi.single v (1 : FiniteCompletion K v) :
      ∀ w, FiniteCompletion K w) v = 0 at hcoord
    simpa only [Pi.single_eq_same] using hcoord
  exact one_ne_zero hbad

/-- The infinite restriction is nontrivial under the same pairing hypothesis. -/
theorem infiniteAdditiveRestriction_ne_one_of_pairing (v : InfinitePlace K) :
    infiniteAdditiveRestriction ψ v ≠ 1 := by
  classical
  intro h
  have hzero : infiniteAdditiveInclusion K v 1 = 0 := by
    apply eq_zero_of_pairing_trivial ψ e he
    intro a
    rw [infiniteAdditiveInclusion_mul]
    have hx := congrArg (fun θ : AddChar (InfiniteCompletion K v) Circle =>
      θ (infiniteProjection K v a)) h
    simpa [infiniteAdditiveRestriction] using hx
  have hcoord := congrArg (infiniteProjection K v) hzero
  have hbad : (1 : InfiniteCompletion K v) = 0 := by
    change (Pi.single v (1 : InfiniteCompletion K v) :
      ∀ w, InfiniteCompletion K w) v = 0 at hcoord
    simpa only [Pi.single_eq_same] using hcoord
  exact one_ne_zero hbad

/-- The finite local-data existential in the global target follows from
the multiplication-pairing equivalence, using the published Haar existence. -/
theorem finite_localData_of_pairing (v : FinitePlace K) :
    ∃ ψv : @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (CompletionPadic.topologicalData v).topology,
      IsFiniteAdditiveComponent ψ v ψv ∧
        Nonempty (LocalFactor.PadicAbelian.SelfDualHaar (CompletionPadic.topologicalData v) ψv) := by
  let h := finiteAdditiveRestriction_ne_one_of_pairing ψ e he v
  exact ⟨finiteAdditiveComponent ψ v h,
    isFiniteAdditiveComponent_finiteAdditiveComponent ψ v h,
    nonempty_selfDualHaar_of_nontrivial_restriction ψ v h⟩

end Pairing

end Langlands.Global.HeckeFunctionalEquation

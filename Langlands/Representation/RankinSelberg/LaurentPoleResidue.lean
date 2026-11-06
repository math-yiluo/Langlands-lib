import Langlands.Representation.RankinSelberg.LaurentEvaluation
import Langlands.Representation.RankinSelberg.EqualRankTrilinearReduction

/-! # Nonzero Laurent residues and descent to bilinear forms -/

noncomputable section

namespace Langlands.RankinSelberg

open Polynomial

universe uV uW uS uG

/-- Vanishing of every cleared generator at a point passes to the Laurent span. -/
theorem IsNormalizedGenerator.laurentEval_eq_zero_of_span
    {values : Set RationalFunctions} {P : ℂ[X]}
    (hP : IsNormalizedGenerator values P) (x : ℂˣ)
    (hvalues : ∀ R ∈ values, ∀ a : LaurentCoefficients,
      laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * R →
        laurentEval x a = 0)
    {R : RationalFunctions} (hR : R ∈ zetaSpan values) :
    ∀ a : LaurentCoefficients,
      laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * R →
        laurentEval x a = 0 := by
  induction hR using Submodule.span_induction with
  | mem R hR => exact hvalues R hR
  | zero =>
    intro a ha
    have hz : a = 0 := laurentToRatFunc_injective (by simpa using ha)
    simp [hz]
  | add R S hR hS ihR ihS =>
    intro a ha
    obtain ⟨b, hb⟩ := hP.clearsDenominators hR
    obtain ⟨c, hc⟩ := hP.clearsDenominators hS
    have heq : a = b + c := laurentToRatFunc_injective (by
      rw [map_add, hb, hc, ha, mul_add])
    rw [heq, map_add, ihR b hb, ihS c hc, add_zero]
  | smul b R hR ih =>
    intro a ha
    obtain ⟨c, hc⟩ := hP.clearsDenominators hR
    have heq : a = b * c := laurentToRatFunc_injective (by
      rw [map_mul, hc, ha, Algebra.smul_def, algebraMap_laurent]
      ring)
    rw [heq, map_mul, ih c hc, mul_zero]

/-- For each nonzero point, some cleared generating value, possibly depending
on that point, has nonzero evaluation there. This uses the full
normalized-generator equality, not just a common denominator. -/
theorem IsNormalizedGenerator.exists_laurentEval_ne_zero
    {values : Set RationalFunctions} {P : ℂ[X]}
    (hP : IsNormalizedGenerator values P) (x : ℂˣ) :
    ∃ R ∈ values, ∃ a : LaurentCoefficients,
      laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * R ∧
        laurentEval x a ≠ 0 := by
  by_contra h
  have hvalues : ∀ R ∈ values, ∀ a : LaurentCoefficients,
      laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * R →
        laurentEval x a = 0 := by
    intro R hR a ha
    by_contra hne
    exact h ⟨R, hR, a, ha, hne⟩
  have hmem : (algebraMap ℂ[X] RationalFunctions P)⁻¹ ∈ zetaSpan values := by
    rw [hP.2]
    exact Submodule.mem_span_singleton_self _
  have hz := hP.laurentEval_eq_zero_of_span x hvalues hmem 1
    (by simp [RatFunc.algebraMap_ne_zero hP.polynomial_ne_zero])
  simpa using hz

section Trilinear

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {S : Type uS} [AddCommGroup S] [Module ℂ S]

/-- Evaluation of the uniquely lifted denominator-cleared rational family.
At a root of the clearing polynomial this records its possible residue. -/
def clearedLaurentForm (P : ℂ[X])
    (C : V →ₗ[ℂ] W →ₗ[ℂ] S →ₗ[ℂ] RationalFunctions)
    (hclear : ∀ v w φ, ∃ a : LaurentCoefficients,
      laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * C v w φ)
    (x : ℂˣ) : V →ₗ[ℂ] W →ₗ[ℂ] S →ₗ[ℂ] ℂ :=
  trilinearPostcomp (laurentEval x).toLinearMap (laurentLift P C hclear)

/-- The cleared form agrees with the evaluation of any Laurent lift. -/
theorem clearedLaurentForm_eq (P : ℂ[X])
    (C : V →ₗ[ℂ] W →ₗ[ℂ] S →ₗ[ℂ] RationalFunctions)
    (hclear : ∀ v w φ, ∃ a : LaurentCoefficients,
      laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * C v w φ)
    (x : ℂˣ) (v : V) (w : W) (φ : S) (a : LaurentCoefficients)
    (ha : laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * C v w φ) :
    clearedLaurentForm P C hclear x v w φ = laurentEval x a := by
  change laurentEval x (laurentLift P C hclear v w φ) = laurentEval x a
  congr 1
  apply laurentToRatFunc_injective
  rw [laurentLift_spec, ha]

/-- A normalized generator makes its cleared trilinear form nonzero at every
nonzero spectral point. -/
theorem clearedLaurentForm_ne_zero
    {values : Set RationalFunctions} {P : ℂ[X]}
    (hP : IsNormalizedGenerator values P)
    (C : V →ₗ[ℂ] W →ₗ[ℂ] S →ₗ[ℂ] RationalFunctions)
    (hclear : ∀ v w φ, ∃ a : LaurentCoefficients,
      laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * C v w φ)
    (hvalues : ∀ R ∈ values, ∃ v w φ, C v w φ = R) (x : ℂˣ) :
    clearedLaurentForm P C hclear x ≠ 0 := by
  obtain ⟨R, hR, a, ha, hne⟩ := hP.exists_laurentEval_ne_zero x
  obtain ⟨v, w, φ, hC⟩ := hvalues R hR
  intro hz
  apply hne
  have heq := clearedLaurentForm_eq P C hclear x v w φ a (by rw [hC]; exact ha)
  rw [hz] at heq
  exact heq.symm

/-- If the rational family is Laurent on a test submodule, then the cleared
form vanishes there at every root of its clearing polynomial. -/
theorem clearedLaurentForm_vanishes_on
    (P : ℂ[X]) (C : V →ₗ[ℂ] W →ₗ[ℂ] S →ₗ[ℂ] RationalFunctions)
    (hclear : ∀ v w φ, ∃ a : LaurentCoefficients,
      laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * C v w φ)
    (K : Submodule ℂ S)
    (hK : ∀ v w φ, φ ∈ K → ∃ a : LaurentCoefficients,
      laurentToRatFunc a = C v w φ)
    (x : ℂˣ) (hx : P.eval (x : ℂ) = 0) :
    TrilinearReduction.restrict K (clearedLaurentForm P C hclear x) = 0 := by
  ext v w φ
  obtain ⟨a, ha⟩ := hK v w φ.val φ.property
  change clearedLaurentForm P C hclear x v w φ.val = 0
  rw [clearedLaurentForm_eq P C hclear x v w φ.val (P.toLaurent * a)
    (by rw [map_mul, laurentToRatFunc_toLaurent, ha]), map_mul,
    laurentEval_toLaurent, hx, zero_mul]

/-- A nonzero normalized residue which vanishes on the kernel of an invariant
test functional descends to a nonzero covariant bilinear form. -/
theorem exists_bilinear_of_clearedLaurent_root
    {G : Type uG} [Group G]
    {values : Set RationalFunctions} {P : ℂ[X]}
    (hP : IsNormalizedGenerator values P)
    (C : V →ₗ[ℂ] W →ₗ[ℂ] S →ₗ[ℂ] RationalFunctions)
    (hclear : ∀ v w φ, ∃ a : LaurentCoefficients,
      laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * C v w φ)
    (hvalues : ∀ R ∈ values, ∃ v w φ, C v w φ = R)
    (e : S →ₗ[ℂ] ℂ) (φ₀ : S) (hφ₀ : e φ₀ = 1)
    (hK : ∀ v w φ, e φ = 0 → ∃ a : LaurentCoefficients,
      laurentToRatFunc a = C v w φ)
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (a : G → S →ₗ[ℂ] S) (χ : G → ℂ)
    (he : ∀ g φ, e (a g φ) = e φ)
    (x : ℂˣ) (hx : P.eval (x : ℂ) = 0)
    (hinv : TrilinearReduction.Invariant ρ σ a χ (clearedLaurentForm P C hclear x)) :
    ∃ β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ, β ≠ 0 ∧
      (∀ v w φ, clearedLaurentForm P C hclear x v w φ = e φ * β v w) ∧
      (∀ g v w, β (ρ g v) (σ g w) = χ g * β v w) := by
  let B := clearedLaurentForm P C hclear x
  have hB := clearedLaurentForm_ne_zero hP C hclear hvalues x
  have hres : TrilinearReduction.restrict (LinearMap.ker e) B = 0 :=
    clearedLaurentForm_vanishes_on P C hclear (LinearMap.ker e) hK x hx
  have hfactor := TrilinearReduction.factor_evaluation e φ₀ hφ₀ B hres
  refine ⟨TrilinearReduction.evaluate φ₀ B, ?_, hfactor, ?_⟩
  · intro hz
    apply hB
    ext v w φ
    rw [hfactor, hz]
    simp
  · intro g v w
    have h := hinv g v w φ₀
    rw [hfactor, he, hφ₀, one_mul] at h
    exact h

end Trilinear

end Langlands.RankinSelberg

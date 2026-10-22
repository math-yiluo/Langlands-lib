import Langlands.Shimura.Unitary.Similitude
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Algebra.Central.Defs
import Mathlib.RingTheory.SimpleRing.Defs

/-! # Second-kind involutions on central simple CM-field algebras -/

universe u v w z

namespace Langlands.Shimura

open CategoryTheory NumberField Algebra

section CM

variable (E : Type u) (K : Type v)
variable [Field E] [NumberField E] [IsTotallyReal E]
variable [Field K] [NumberField K] [IsTotallyComplex K]
variable [Algebra E K] [IsQuadraticExtension E K]

/-- The actual complex conjugation of a CM extension, as an automorphism over
the specified totally real subfield. -/
noncomputable def cmConjugation : K ≃ₐ[E] K := by
  letI : IsCMField K := IsCMField.ofCMExtension E K
  refine
    { (IsCMField.complexConj K).toRingEquiv with
      commutes' := ?_ }
  intro e
  let e' : NumberField.maximalRealSubfield K :=
    CMExtension.equivMaximalRealSubfield E K e
  change IsCMField.complexConj K (algebraMap (NumberField.maximalRealSubfield K) K e') =
    algebraMap (NumberField.maximalRealSubfield K) K e'
  exact (IsCMField.complexConj K).commutes e'

omit [NumberField E] in
theorem cmConjugation_involutive : Function.Involutive (cmConjugation E K) := by
  let : IsCMField K := IsCMField.ofCMExtension E K
  exact IsCMField.complexConj_apply_apply (K := K)

omit [NumberField E] in
theorem cmConjugation_ne_one : cmConjugation E K ≠ 1 := by
  let : IsCMField K := IsCMField.ofCMExtension E K
  intro h
  apply IsCMField.complexConj_ne_one (K := K)
  ext k
  exact congrArg (fun f : K ≃ₐ[E] K => f k) h

omit [NumberField E] in
theorem embedding_cmConjugation (φ : K →+* ℂ) (k : K) :
    φ (cmConjugation E K k) = star (φ k) := by
  let : IsCMField K := IsCMField.ofCMExtension E K
  exact IsCMField.complexEmbedding_complexConj K φ k

variable (A : Type w) [Ring A] [Algebra K A] [Algebra E A]
variable [IsScalarTower E K A]

/-- An involution of the second kind on the actual CM-field algebra. -/
structure SecondKindInvolution where
  involution : AlgebraInvolution E A
  onCenter (k : K) :
    involution (algebraMap K A k) = algebraMap K A (cmConjugation E K k)

/-- The central simple algebra input of Harris Section 1.
It contains an actual algebra and involution, not a group or geometric output. -/
structure CentralSimpleUnitaryData (n : ℕ) extends SecondKindInvolution E K A where
  rank_gt_one : 1 < n
  central : Algebra.IsCentral K A
  simple : IsSimpleRing A
  finite : FiniteDimensional K A
  dimension : Module.finrank K A = n ^ 2

namespace SecondKindInvolution

variable {E K A}
variable (σ : SecondKindInvolution E K A)
variable [Algebra ℚ A] [IsScalarTower ℚ E A]

/-- Restrict the actual involution from the totally real field to the rationals. -/
def rationalInvolution : AlgebraInvolution ℚ A where
  linear := σ.involution.linear.restrictScalars ℚ
  map_one := σ.involution.map_one
  map_mul := σ.involution.map_mul
  involutive := σ.involution.involutive

omit [IsScalarTower E K A] in
@[simp] theorem rationalInvolution_apply (a : A) :
    σ.rationalInvolution a = σ.involution a := rfl

omit [IsScalarTower E K A] in
theorem rationalInvolution_center (k : K) :
    σ.rationalInvolution (algebraMap K A k) =
      algebraMap K A (cmConjugation E K k) :=
  σ.onCenter k

/-- The rational unitary-similitude functor of this second-kind involution.
The multiplier belongs to the test rational algebra itself. -/
noncomputable def rationalSimilitudeFunctor :
    CommAlgCat.{z} ℚ ⥤ GrpCat.{max w z} :=
  σ.rationalInvolution.similitudeFunctor

end SecondKindInvolution

end CM

end Langlands.Shimura

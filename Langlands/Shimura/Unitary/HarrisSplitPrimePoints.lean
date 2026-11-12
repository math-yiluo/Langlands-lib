import Langlands.Shimura.Unitary.ImaginaryQuadraticSplitPoints
import Langlands.Shimura.Unitary.CMData

/-!
# Harris's similitude group at a prime split in the imaginary quadratic field

Let `K/E` be a CM extension, `A` a `K`-algebra with an involution `σ` of the
second kind and `ι : F →+* K` an embedding of an imaginary quadratic field.
The rational involution of `σ` restricts to complex conjugation on `F`. Hence,
at a finite place `v` of `ℚ` and an embedding `u : F →+* ℚ_v` (so the prime of
`v` splits in `F`), the points of the rational similitude group over `ℚ_v` are
`(ℚ_v ⊗[F, u] A)ˣ × ℚ_vˣ`. This is the identification of Harris (1998, (A.1))
and Harris (1999, (4.2)) before `ℚ_v ⊗[F, u] A` is decomposed over the places
of `K` above `u`; that decomposition is not made here.
-/

noncomputable section

open scoped TensorProduct
open NumberField

set_option autoImplicit false

universe u v w z

namespace Langlands.Shimura

section CM

variable {E : Type u} {K : Type v}
variable [Field E] [NumberField E] [IsTotallyReal E]
variable [Field K] [NumberField K] [IsTotallyComplex K]
variable [Algebra E K] [Algebra.IsQuadraticExtension E K]
variable {F : Type w} [Field F] [NumberField F] [IsCMField F]

omit [NumberField E] in
/-- The complex conjugation of the CM extension `K/E` restricts to the complex
conjugation of a CM field `F` embedded in `K`. -/
theorem cmConjugation_comp (ι : F →+* K) (t : F) :
    cmConjugation E K (ι t) = ι (IsCMField.complexConj F t) := by
  let φ : K →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  rw [embedding_cmConjugation]
  have h := IsCMField.complexEmbedding_complexConj F (φ.comp ι) t
  rw [RingHom.comp_apply, RingHom.comp_apply] at h
  rw [h]
  rfl

variable {A : Type z} [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower E K A]
variable [Algebra ℚ A] [IsScalarTower ℚ E A]

/-- The `F`-algebra structure on `A` through an embedding `ι : F →+* K`. -/
abbrev imaginaryQuadraticAlgebra (ι : F →+* K) : Algebra F A :=
  Algebra.compHom A ι

omit [IsScalarTower E K A] in
/-- An involution of the second kind relative to `K/E` is, as a rational
involution, of the second kind relative to every CM field `F` embedded in `K`. -/
theorem SecondKindInvolution.isConjugationOn (σ : SecondKindInvolution E K A)
    (ι : F →+* K) :
    letI := imaginaryQuadraticAlgebra (A := A) ι
    ImaginaryQuadraticSplit.IsConjugationOn F σ.rationalInvolution := by
  intro t
  change σ.rationalInvolution (algebraMap K A (ι t)) = algebraMap K A (ι _)
  rw [σ.rationalInvolution_center, cmConjugation_comp]

variable [Algebra.IsQuadraticExtension ℚ F]

/-- Harris's identification at a finite place `v` of `ℚ` and an embedding
`u : F →+* ℚ_v` of the imaginary quadratic field: the points of the rational
similitude group over `ℚ_v` are `(ℚ_v ⊗[F, u] A)ˣ × ℚ_vˣ`, through the
projection of the algebra unit and the multiplier. -/
def SecondKindInvolution.splitPrimePoints (σ : SecondKindInvolution E K A)
    (ι : F →+* K) (v : Global.FinitePlace ℚ) (u : F →+* Global.FiniteCompletion ℚ v) :
    letI := imaginaryQuadraticAlgebra (A := A) ι
    letI := u.toAlgebra
    σ.rationalInvolution.Points (Global.FiniteCompletion ℚ v) ≃*
      (Global.FiniteCompletion ℚ v ⊗[F] A)ˣ × (Global.FiniteCompletion ℚ v)ˣ :=
  letI := imaginaryQuadraticAlgebra (A := A) ι
  letI := u.toAlgebra
  ImaginaryQuadraticSplit.pointsEquiv σ.rationalInvolution _ (σ.isConjugationOn ι)

omit [IsScalarTower E K A] in
theorem SecondKindInvolution.splitPrimePoints_fst_val (σ : SecondKindInvolution E K A)
    (ι : F →+* K) (v : Global.FinitePlace ℚ) (u : F →+* Global.FiniteCompletion ℚ v)
    (g : σ.rationalInvolution.Points (Global.FiniteCompletion ℚ v)) :
    letI := imaginaryQuadraticAlgebra (A := A) ι
    letI := u.toAlgebra
    ((σ.splitPrimePoints ι v u g).1 : Global.FiniteCompletion ℚ v ⊗[F] A) =
      ImaginaryQuadraticSplit.projection F A _ g.1.1 := rfl

omit [IsScalarTower E K A] in
theorem SecondKindInvolution.splitPrimePoints_snd (σ : SecondKindInvolution E K A)
    (ι : F →+* K) (v : Global.FinitePlace ℚ) (u : F →+* Global.FiniteCompletion ℚ v)
    (g : σ.rationalInvolution.Points (Global.FiniteCompletion ℚ v)) :
    (σ.splitPrimePoints ι v u g).2 =
      AlgebraInvolution.Points.multiplier σ.rationalInvolution _ g := rfl

end CM

end Langlands.Shimura

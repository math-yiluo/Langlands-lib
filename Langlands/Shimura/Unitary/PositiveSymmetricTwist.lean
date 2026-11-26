import Langlands.Shimura.Unitary.HermitianCongruence
import Langlands.Global.AdelicFunctoriality.Norm
import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.Analysis.Real.Sqrt

/-! # Positive symmetric twists preserve real signatures -/

noncomputable section

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global.AdelicFunctoriality
open scoped TensorProduct InfiniteExtension NumberField.LiesOver

universe u v w x

section Roots

variable {E : Type u} {F : Type v} [Field E] [NumberField E]
  [Field F] [NumberField F] [IsTotallyReal F] [Algebra E F]
  (t : Fˣ) (ht : ∀ q : InfinitePlace F, 0 < (q.embedding (t : F)).re)

omit [NumberField F] in
include ht in
private theorem exists_completion_squareRoot (q : InfinitePlace F) :
    ∃ a : q.Completion, a * a = algebraMap F q.Completion (t : F) := by
  let hq := IsTotallyReal.isReal q
  let f := InfinitePlace.Completion.extensionEmbeddingOfIsReal hq
  let y := Real.sqrt ((q.embedding (t : F)).re)
  obtain ⟨x, hx⟩ := InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal hq y
  refine ⟨x, (RingHom.injective f) ?_⟩
  rw [map_mul, show f x = y from hx]
  change y * y = InfinitePlace.Completion.extensionEmbeddingOfIsReal hq
    ((WithAbs.equiv q.val).symm (t : F) : q.Completion)
  rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe, RingEquiv.apply_symm_apply]
  exact Real.mul_self_sqrt (ht q).le

include ht in
private theorem exists_realTensor_squareRoot (τ : E →+* ℝ) :
    letI : Algebra E ℝ := τ.toAlgebra
    ∃ a : ℝ ⊗[E] F, a * a = 1 ⊗ₜ[E] (t : F) := by
  let : Algebra E ℝ := τ.toAlgebra
  let v := InfinitePlace.mk (Complex.ofRealHom.comp τ)
  have hτ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp τ) :=
    ComplexEmbedding.isReal_iff.mpr (by ext x; simp [ComplexEmbedding.conjugate_coe_eq])
  have hv : v.IsReal := InfinitePlace.isReal_mk_iff.mpr hτ
  have hτ' : InfinitePlace.embedding_of_isReal hv = τ := by
    ext e
    apply Complex.ofReal_injective
    rw [InfinitePlace.embedding_of_isReal_apply]
    exact congrArg (fun g : E →+* ℂ => g e) (InfinitePlace.embedding_mk_eq_of_isReal hτ)
  let f : v.Completion →ₐ[E] ℝ :=
    { toRingHom := InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
      commutes' := fun a => by
        change InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
          ((WithAbs.equiv v.val).symm a : v.Completion) = τ a
        rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe, RingEquiv.apply_symm_apply, hτ'] }
  let e := AlgEquiv.ofBijective f (InfinitePlace.Completion.bijective_extensionEmbeddingOfIsReal hv)
  let g := Algebra.TensorProduct.congr e (AlgEquiv.refl : F ≃ₐ[E] F)
  let C := infiniteTensorEquiv (L := F) v
  choose b hb using fun q : InfinitePlacesAbove F v => exists_completion_squareRoot t ht q.val
  let a := C.symm b
  have ha : a * a = 1 ⊗ₜ[E] (t : F) := by
    apply C.injective
    rw [map_mul, show C a = b from C.apply_symm_apply b]
    funext q
    rw [infiniteTensorEquiv_apply, infiniteTensorMap_one_tmul]
    exact hb q
  refine ⟨g a, ?_⟩
  rw [← map_mul, ha]
  change ((e 1) ⊗ₜ[E] (t : F)) = _
  rw [map_one]

end Roots

section Symmetric

variable {E : Type u} {F : Type v} {A : Type w}
  [Field E] [NumberField E] [Field F] [NumberField F] [IsTotallyReal F] [Algebra E F]
  [Ring A] [Algebra E A] (σ : AlgebraInvolution E A) (i : F →ₐ[E] A)
  (hi : ∀ y : F, σ (i y) = i y) (t : Fˣ)
  (ht : ∀ q : InfinitePlace F, 0 < (q.embedding (t : F)).re)

set_option maxRecDepth 4096 in
/-- In every real scalar extension, the image of a totally positive unit of a
symmetric subfield is the square of an invertible symmetric element. -/
def realSymmetricUnitSquareRoot (τ : E →+* ℝ) :
    letI : Algebra E ℝ := τ.toAlgebra
    { b : (ℝ ⊗[E] A)ˣ // σ.baseChange ℝ (b : ℝ ⊗[E] A) = b ∧
      b * b = Units.map (Algebra.TensorProduct.includeRight : A →ₐ[E] ℝ ⊗[E] A).toMonoidHom
        (Units.map i.toMonoidHom t) } := by
  let : Algebra E ℝ := τ.toAlgebra
  let B := ℝ ⊗[E] A
  let jF : F →ₐ[E] ℝ ⊗[E] F := Algebra.TensorProduct.includeRight
  let jA : A →ₐ[E] B := Algebra.TensorProduct.includeRight
  let g := Algebra.TensorProduct.map (AlgHom.id E ℝ) i
  let ex := exists_realTensor_squareRoot t ht τ
  let a := ex.choose
  have ha : a * a = jF (t : F) := ex.choose_spec
  have hau : IsUnit a := isUnit_mul_self_iff.mp (ha ▸ (Units.map jF.toMonoidHom t).isUnit)
  let b := Units.map g.toMonoidHom hau.unit
  have hb : (b : B) = g a := congrArg g hau.unit_spec
  have hsym (x : ℝ ⊗[E] F) : σ.baseChange ℝ (g x) = g x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s x => simp only [g, Algebra.TensorProduct.map_tmul, AlgebraInvolution.baseChange_tmul, hi]
  refine ⟨b, hb.symm ▸ hsym a, Units.ext ?_⟩
  change (b : B) * (b : B) = jA (i (t : F))
  rw [hb, ← map_mul, ha]
  rfl

end Symmetric

section Signature

variable {E : Type u} {K : Type v} {F : Type x} {A : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]
  [Field F] [NumberField F] [IsTotallyReal F] [Algebra E F]
  [Ring A] [Algebra E A] [Algebra K A]
  (σ : SecondKindInvolution E K A) (i : F →ₐ[E] A) (hi : ∀ y : F, σ.involution (i y) = i y)
  (t : Fˣ) (ht : ∀ q : InfinitePlace F, 0 < (q.embedding (t : F)).re)

set_option maxRecDepth 4096 in
include ht in
/-- Twisting by the image of a totally positive unit of a symmetric subfield
preserves the actual real signature charts. -/
theorem hasSignature_twist_of_positive (τ : E →+* ℝ) {n r : ℕ} (h : HasSignature σ τ n r) :
    HasSignature (σ.twist (Units.map i.toMonoidHom t) (hi (t : F))) τ n r := by
  let : Algebra E ℝ := τ.toAlgebra
  let B := ℝ ⊗[E] A
  let j : A →ₐ[E] B := Algebra.TensorProduct.includeRight
  let z : Aˣ := Units.map i.toMonoidHom t
  have hz : σ.involution (z : A) = z := hi (t : F)
  let b := realSymmetricUnitSquareRoot σ.involution i hi t ht τ
  let c := MulSemiringAction.toAlgEquiv ℝ B (ConjAct.toConjAct b.val)
  have hc (x : B) : c x = (b.val : B) * x * (↑b.val⁻¹ : B) := rfl
  have hsq : (b.val : B) * (b.val : B) = j (z : A) := congrArg Units.val b.property.2
  have hinvsq : (↑b.val⁻¹ : B) * (↑b.val⁻¹ : B) = j (↑z⁻¹ : A) := by
    have h' := congrArg (fun q : Bˣ => (↑q⁻¹ : B)) b.property.2
    rwa [_root_.mul_inv_rev, Units.val_mul] at h'
  have hb : σ.involution.baseChange ℝ (b.val : B) = b.val := b.property.1
  have hbi : σ.involution.baseChange ℝ (↑b.val⁻¹ : B) = (↑b.val⁻¹ : B) := by
    change ((σ.involution.baseChange ℝ).units b.val⁻¹ : B) = _
    rw [AlgebraInvolution.units_inv, show (σ.involution.baseChange ℝ).units b.val = b.val from Units.ext hb]
  have hconj (x : B) : c ((σ.twist z hz).involution.baseChange ℝ x) =
      σ.involution.baseChange ℝ (c x) := by
    rw [hc, hc]
    change (b.val : B) * (σ.involution.adjoint z hz).baseChange ℝ x * (↑b.val⁻¹ : B) = _
    rw [AlgebraInvolution.baseChange_adjoint_apply σ.involution z hz ℝ x]
    change (b.val : B) * (j (↑z⁻¹ : A) * σ.involution.baseChange ℝ x * j (z : A)) *
      (↑b.val⁻¹ : B) = _
    rw [← hsq, ← hinvsq]
    simp only [AlgebraInvolution.apply_mul, hb, hbi]
    simp [mul_assoc]
  obtain ⟨hr, e, he⟩ := h
  exact ⟨hr, c.trans e, fun x => (congrArg e (hconj x)).trans (he (c x))⟩

end Signature

end Langlands.Shimura.FiniteUnitary

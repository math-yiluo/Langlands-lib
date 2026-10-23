import Langlands.Shimura.Unitary.ComplexScalarInvolution
import Langlands.Shimura.Unitary.ExchangeInvolution
import Mathlib.Algebra.Group.Pi.Units

noncomputable section
open Algebra Module
open scoped TensorProduct Classical
attribute [local instance 1100] Algebra.toModule

namespace Langlands.Shimura.ComplexMatrix

variable (S : Type*) [CommRing S] [Algebra ℂ S] [Algebra ℝ S] [IsScalarTower ℝ ℂ S]

/-- The coefficient-fixed signature transpose as an algebra involution. -/
def signatureTransposeInvolution (n r : ℕ) :
    AlgebraInvolution S (Matrix (Fin n) (Fin n) S) where
  linear :=
    { toFun := signatureTransposeOver S n r
      map_add' := signatureTransposeOver_add S n r
      map_smul' := signatureTransposeOver_smul S n r }
  map_one := by
    have h := congrArg Prod.fst (scalarSignatureInvolution S n r).apply_one
    simpa only [scalarSignatureInvolution_apply, Prod.fst_one, Prod.snd_one,
      Prod.fst_mul, Prod.snd_mul, LinearMap.coe_mk, AddHom.coe_mk] using h
  map_mul M N := by
    have h := congrArg Prod.fst
      ((scalarSignatureInvolution S n r).apply_mul (0, M) (0, N))
    simpa only [scalarSignatureInvolution_apply, Prod.fst_one, Prod.snd_one,
      Prod.fst_mul, Prod.snd_mul, LinearMap.coe_mk, AddHom.coe_mk] using h
  involutive M := by
    have h := congrArg Prod.fst ((scalarSignatureInvolution S n r).apply_apply (M, 0))
    simpa only [scalarSignatureInvolution_apply, Prod.fst_one, Prod.snd_one,
      Prod.fst_mul, Prod.snd_mul, LinearMap.coe_mk, AddHom.coe_mk] using h

@[simp] theorem signatureTransposeInvolution_apply (n r : ℕ)
    (M : Matrix (Fin n) (Fin n) S) :
    signatureTransposeInvolution S n r M = signatureTransposeOver S n r M := rfl

/-- Rearrange the ordered matrix pairs into a pair of families of matrices. -/
def familyPairEquiv (n : ℕ) (I : Type*) :
    (I → Matrix (Fin n) (Fin n) S × Matrix (Fin n) (Fin n) S) ≃ₐ[S]
      ((I → Matrix (Fin n) (Fin n) S) × (I → Matrix (Fin n) (Fin n) S)) where
  toFun p := (fun τ => (p τ).1, fun τ => (p τ).2)
  invFun p := fun τ => (p.1 τ, p.2 τ)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Signature transpose independently at each Harris index. -/
def harrisTransposeInvolution (n : ℕ) (I : Type*) [DecidableEq I]
    (distinguished : I) : AlgebraInvolution S (I → Matrix (Fin n) (Fin n) S) where
  linear :=
    { toFun := fun x τ => signatureTransposeInvolution S n
        (if τ = distinguished then n - 1 else n) (x τ)
      map_add' := by intros; funext τ; exact AlgebraInvolution.apply_add _ _ _
      map_smul' := by intros; funext τ; exact AlgebraInvolution.apply_smul _ _ _ }
  map_one := by
    funext τ
    exact (signatureTransposeInvolution S n (if τ = distinguished then n - 1 else n)).apply_one
  map_mul x y := by
    funext τ
    exact (signatureTransposeInvolution S n (if τ = distinguished then n - 1 else n)).apply_mul (x τ) (y τ)
  involutive x := by
    funext τ
    exact (signatureTransposeInvolution S n (if τ = distinguished then n - 1 else n)).apply_apply (x τ)

/-- The actual Harris split involution is an exchange involution after rearrangement. -/
theorem familyPairEquiv_involution (n : ℕ) (I : Type*) [DecidableEq I]
    (distinguished : I)
    (p : I → Matrix (Fin n) (Fin n) S × Matrix (Fin n) (Fin n) S) :
    familyPairEquiv S n I (harrisScalarMatrixInvolution S n I distinguished p) =
      (harrisTransposeInvolution S n I distinguished).exchange
        (familyPairEquiv S n I p) := by
  apply Prod.ext
  · funext τ
    exact congrArg Prod.fst (scalarSignatureInvolution_apply S n _ (p τ))
  · funext τ
    exact congrArg Prod.snd (scalarSignatureInvolution_apply S n _ (p τ))

/-- Harris split-matrix similitudes are a matrix unit at each index and one scalar unit. -/
def harrisSimilitudesEquiv (n : ℕ) (I : Type*) [DecidableEq I] (distinguished : I) :
    (harrisScalarMatrixInvolution S n I distinguished).similitudes ≃*
      ((I → (Matrix (Fin n) (Fin n) S)ˣ) × Sˣ) :=
  (AlgebraInvolution.similitudesEquiv _ _ (familyPairEquiv S n I)
    (familyPairEquiv_involution S n I distinguished)).trans
      (((harrisTransposeInvolution S n I distinguished).exchangeSimilitudesEquiv).trans
        (MulEquiv.prodCongr MulEquiv.piUnits (MulEquiv.refl Sˣ)))

@[simp] theorem harrisSimilitudesEquiv_fst (n : ℕ) (I : Type*) [DecidableEq I]
    (distinguished : I) (g : (harrisScalarMatrixInvolution S n I distinguished).similitudes)
    (τ : I) :
    ((harrisSimilitudesEquiv S n I distinguished g).1 τ : Matrix (Fin n) (Fin n) S) =
      ((g.val.1 : I → Matrix (Fin n) (Fin n) S × Matrix (Fin n) (Fin n) S) τ).1 := rfl

@[simp] theorem harrisSimilitudesEquiv_snd (n : ℕ) (I : Type*) [DecidableEq I]
    (distinguished : I) (g : (harrisScalarMatrixInvolution S n I distinguished).similitudes) :
    (harrisSimilitudesEquiv S n I distinguished g).2 =
      (harrisScalarMatrixInvolution S n I distinguished).multiplier g := by
  exact Units.ext rfl

/-- The omitted matrix is reconstructed by multiplier times inverse signature transpose. -/
theorem harrisSimilitudesEquiv_symm_second (n : ℕ) (I : Type*) [DecidableEq I]
    (distinguished : I) (p : (I → (Matrix (Fin n) (Fin n) S)ˣ) × Sˣ) (τ : I) :
    ((((harrisSimilitudesEquiv S n I distinguished).symm p).val.1 :
      I → Matrix (Fin n) (Fin n) S × Matrix (Fin n) (Fin n) S) τ).2 =
      algebraMap S (Matrix (Fin n) (Fin n) S) (p.2 : S) *
        signatureTransposeOver S n (if τ = distinguished then n - 1 else n)
          ((p.1 τ)⁻¹ : (Matrix (Fin n) (Fin n) S)ˣ) := rfl

end Langlands.Shimura.ComplexMatrix

namespace Langlands.Shimura.HarrisSignatureCharts

universe u v w z
open NumberField
variable {E : Type u} {K : Type v} {A : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {σ : SecondKindInvolution E K A} {n : ℕ}
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts σ n Φ)
  {ι : Type z} [Fintype ι] (b : Module.Basis ι E A)
  (S : Type*) [CommRing S] [Algebra ℂ S] [Algebra ℝ S] [IsScalarTower ℝ ℂ S]

/-- Split actual iterated scalar-extension similitudes into general linear and scalar units. -/
def iteratedScalarGroupSplitting :
    ((σ.rationalInvolution.baseChange ℝ).baseChange S).similitudes ≃*
      (((E →+* ℝ) → (Matrix (Fin n) (Fin n) S)ˣ) × Sˣ) :=
  (C.iteratedScalarSimilitudesEquiv S b).trans
    (ComplexMatrix.harrisSimilitudesEquiv S n (E →+* ℝ) C.distinguished)

@[simp] theorem iteratedScalarGroupSplitting_matrix
    (g : ((σ.rationalInvolution.baseChange ℝ).baseChange S).similitudes) (τ : E →+* ℝ) :
    ((C.iteratedScalarGroupSplitting b S g).1 τ : Matrix (Fin n) (Fin n) S) =
      (C.iteratedScalarMatrixEquiv b S (g.val.1 : S ⊗[ℝ] (ℝ ⊗[ℚ] A)) τ).1 := rfl

@[simp] theorem iteratedScalarGroupSplitting_multiplier
    (g : ((σ.rationalInvolution.baseChange ℝ).baseChange S).similitudes) :
    (C.iteratedScalarGroupSplitting b S g).2 =
      ((σ.rationalInvolution.baseChange ℝ).baseChange S).multiplier g := by
  exact Units.ext rfl

variable [Algebra ℚ S] [IsScalarTower ℚ ℝ S]

/-- Split actual Harris similitudes over every commutative complex coefficient algebra. -/
def scalarGroupSplitting :
    (σ.rationalInvolution.baseChange S).similitudes ≃*
      (((E →+* ℝ) → (Matrix (Fin n) (Fin n) S)ˣ) × Sˣ) :=
  (C.scalarSimilitudesEquiv S b).trans
    (ComplexMatrix.harrisSimilitudesEquiv S n (E →+* ℝ) C.distinguished)

@[simp] theorem scalarGroupSplitting_matrix
    (g : (σ.rationalInvolution.baseChange S).similitudes) (τ : E →+* ℝ) :
    ((C.scalarGroupSplitting b S g).1 τ : Matrix (Fin n) (Fin n) S) =
      (C.scalarMatrixEquiv b S (g.val.1 : S ⊗[ℚ] A) τ).1 := rfl

@[simp] theorem scalarGroupSplitting_multiplier
    (g : (σ.rationalInvolution.baseChange S).similitudes) :
    (C.scalarGroupSplitting b S g).2 = (σ.rationalInvolution.baseChange S).multiplier g := by
  exact Units.ext rfl

/-- Direct and iterated splittings agree through the actual tensor-tower comparison. -/
theorem scalarGroupSplitting_tower
    (g : (σ.rationalInvolution.baseChange S).similitudes) :
    C.iteratedScalarGroupSplitting b S
      (AlgebraInvolution.baseChangeTowerSimilitudes ℝ S σ.rationalInvolution g) =
      C.scalarGroupSplitting b S g := by
  apply Prod.ext
  · funext τ
    apply Units.ext
    rfl
  · exact Units.ext rfl

end Langlands.Shimura.HarrisSignatureCharts

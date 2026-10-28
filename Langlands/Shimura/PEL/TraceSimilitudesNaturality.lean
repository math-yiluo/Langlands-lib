import Langlands.Shimura.PEL.TraceSimilitudesBaseChange
import Mathlib.Algebra.Group.Equiv.Opposite

/-! # Coefficient naturality of the actual Harris trace similitudes -/

noncomputable section

universe u v w z t

open scoped TensorProduct

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField Module _root_.Algebra

variable {E : Type u} {K : Type v} {A : Type w}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n) (β : Aˣ)
    {S : Type z} {T : Type t} [CommRing S] [Algebra ℚ S]
    [CommRing T] [Algebra ℚ T]

omit [IsScalarTower E K A] in
/-- The actual extended pairing commutes with every coefficient algebra map. -/
theorem tracePairingBaseChange_changeCoefficients (f : S →ₐ[ℚ] T)
    (x y : S ⊗[ℚ] A) :
    f (D.tracePairingBaseChange S β x y) =
      D.tracePairingBaseChange T β
        (AlgebraInvolution.changeCoefficients f x)
        (AlgebraInvolution.changeCoefficients f y) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul s a =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul t b =>
      simp only [AlgebraInvolution.changeCoefficients_tmul,
        tracePairingBaseChange_tmul, map_mul, AlgHom.commutes]

variable (hβ : D.involution (β : A) = -(β : A))

/-- The existing bilinear subgroup for the actual inverse-unit trace form. -/
abbrev harrisBilinearSimilitudes (S : Type*) [CommRing S] [Algebra ℚ S] :=
  PEL.bilinearSimilitudes (S ⊗[ℚ] A)
    ((D.skewTwist β hβ).tracePairingBaseChange S β⁻¹)

/-- Coefficient extension of regular-module similitudes, constructed through
recovered units and the actual tensor-algebra coefficient map. -/
def harrisTraceSimilitudesMap (f : S →ₐ[ℚ] T) :
    D.harrisBilinearSimilitudes β hβ S →*
      D.harrisBilinearSimilitudes β hβ T :=
  (D.harrisTraceSimilitudesEquiv T β hβ).toMonoidHom.comp
    ((D.toSecondKindInvolution.rationalInvolution.pointsMap f).op.comp
      (D.harrisTraceSimilitudesEquiv S β hβ).symm.toMonoidHom)

@[simp] theorem harrisTraceSimilitudesMap_apply (f : S →ₐ[ℚ] T)
    (g : D.harrisBilinearSimilitudes β hβ S) (x : T ⊗[ℚ] A) :
    (D.harrisTraceSimilitudesMap β hβ f g).val.1 x =
      x * AlgebraInvolution.changeCoefficients f (g.val.1 1) := rfl

@[simp] theorem harrisTraceSimilitudesMap_multiplier (f : S →ₐ[ℚ] T)
    (g : D.harrisBilinearSimilitudes β hβ S) :
    (D.harrisTraceSimilitudesMap β hβ f g).val.2 =
      Units.map f.toMonoidHom g.val.2 := rfl

/-- This is extension of the actual linear action, on images of all tensors. -/
theorem harrisTraceSimilitudesMap_action (f : S →ₐ[ℚ] T)
    (g : D.harrisBilinearSimilitudes β hβ S) (x : S ⊗[ℚ] A) :
    (D.harrisTraceSimilitudesMap β hβ f g).val.1
        (AlgebraInvolution.changeCoefficients f x) =
      AlgebraInvolution.changeCoefficients f (g.val.1 x) := by
  rw [harrisTraceSimilitudesMap_apply, PEL.selfEquiv_apply g.val.1 x, map_mul]

/-- The algebraic-to-bilinear comparison commutes with coefficient extension. -/
theorem harrisTraceSimilitudesEquiv_natural (f : S →ₐ[ℚ] T)
    (g : (D.toSecondKindInvolution.rationalInvolution.Points S)ᵐᵒᵖ) :
    D.harrisTraceSimilitudesMap β hβ f (D.harrisTraceSimilitudesEquiv S β hβ g) =
      D.harrisTraceSimilitudesEquiv T β hβ
        ((D.toSecondKindInvolution.rationalInvolution.pointsMap f).op g) := by
  simp only [harrisTraceSimilitudesMap, MonoidHom.comp_apply,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulEquiv.symm_apply_apply]

@[simp] theorem harrisTraceSimilitudesMap_id :
    D.harrisTraceSimilitudesMap β hβ (AlgHom.id ℚ S) =
      MonoidHom.id (D.harrisBilinearSimilitudes β hβ S) := by
  ext g : 1
  apply Subtype.ext
  apply Prod.ext
  · ext x
    rw [harrisTraceSimilitudesMap_apply, AlgebraInvolution.changeCoefficients_id]
    exact (PEL.selfEquiv_apply g.val.1 x).symm
  · apply Units.ext
    rfl

theorem harrisTraceSimilitudesMap_comp {U : Type*} [CommRing U] [Algebra ℚ U]
    (f : S →ₐ[ℚ] T) (k : T →ₐ[ℚ] U) :
    D.harrisTraceSimilitudesMap β hβ (k.comp f) =
      (D.harrisTraceSimilitudesMap β hβ k).comp
        (D.harrisTraceSimilitudesMap β hβ f) := by
  ext g : 1
  apply Subtype.ext
  apply Prod.ext
  · ext x
    simp only [MonoidHom.comp_apply, harrisTraceSimilitudesMap_apply, one_mul,
      AlgebraInvolution.changeCoefficients_comp, AlgHom.comp_apply]
  · apply Units.ext
    rfl

/-- Over Q itself the original involution also gives the rational comparison. -/
def harrisRationalTraceSimilitudesEquiv :
    D.toSecondKindInvolution.rationalInvolution.similitudesᵐᵒᵖ ≃*
      PEL.bilinearSimilitudes A ((D.skewTwist β hβ).tracePairing β⁻¹) := by
  have hγ := D.involution.skewAdjoint_inverse_skew β hβ
  have hadj : (D.skewTwist β hβ).tracePairingAdjoint β⁻¹ hγ =
      D.toSecondKindInvolution.rationalInvolution :=
    D.toSecondKindInvolution.rationalInvolution.skewAdjoint_inverse β hβ
  exact PEL.algebraicBilinearEquiv _ _
    ((D.skewTwist β hβ).tracePairing_nondegenerate β⁻¹)
    (fun b x y => by
      simpa only [hadj, SecondKindInvolution.rationalInvolution_apply] using
        (D.skewTwist β hβ).tracePairing_right β⁻¹ hγ b x y)

@[simp] theorem harrisRationalTraceSimilitudesEquiv_apply
    (g : D.toSecondKindInvolution.rationalInvolution.similitudesᵐᵒᵖ) (x : A) :
    (D.harrisRationalTraceSimilitudesEquiv β hβ g).val.1 x =
      x * (g.unop.val.1 : A) := rfl

/-- The rational bilinear group maps diagonally through the actual tensor inclusion. -/
def harrisBilinearDiagonal (S : Type*) [CommRing S] [Algebra ℚ S] :
    PEL.bilinearSimilitudes A ((D.skewTwist β hβ).tracePairing β⁻¹) →*
      D.harrisBilinearSimilitudes β hβ S :=
  (D.harrisTraceSimilitudesEquiv S β hβ).toMonoidHom.comp
    ((D.toSecondKindInvolution.rationalInvolution.diagonalPoints S).op.comp
      (D.harrisRationalTraceSimilitudesEquiv β hβ).symm.toMonoidHom)

@[simp] theorem harrisBilinearDiagonal_apply (S : Type*) [CommRing S] [Algebra ℚ S]
    (g : PEL.bilinearSimilitudes A ((D.skewTwist β hβ).tracePairing β⁻¹))
    (x : S ⊗[ℚ] A) :
    (D.harrisBilinearDiagonal β hβ S g).val.1 x =
      x * ((1 : S) ⊗ₜ[ℚ] (g.val.1 1)) := rfl

@[simp] theorem harrisBilinearDiagonal_multiplier (S : Type*)
    [CommRing S] [Algebra ℚ S]
    (g : PEL.bilinearSimilitudes A ((D.skewTwist β hβ).tracePairing β⁻¹)) :
    (D.harrisBilinearDiagonal β hβ S g).val.2 =
      Units.map (algebraMap ℚ S).toMonoidHom g.val.2 := rfl

/-- The rational comparison agrees with the actual diagonal of algebraic points. -/
theorem harrisBilinearDiagonal_natural (S : Type*) [CommRing S] [Algebra ℚ S]
    (g : D.toSecondKindInvolution.rationalInvolution.similitudesᵐᵒᵖ) :
    D.harrisBilinearDiagonal β hβ S (D.harrisRationalTraceSimilitudesEquiv β hβ g) =
      D.harrisTraceSimilitudesEquiv S β hβ
        ((D.toSecondKindInvolution.rationalInvolution.diagonalPoints S).op g) := by
  simp only [harrisBilinearDiagonal, MonoidHom.comp_apply,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulEquiv.symm_apply_apply]

/-- All coefficient maps preserve the rational diagonal. -/
theorem harrisTraceSimilitudesMap_diagonal (f : S →ₐ[ℚ] T)
    (g : PEL.bilinearSimilitudes A ((D.skewTwist β hβ).tracePairing β⁻¹)) :
    D.harrisTraceSimilitudesMap β hβ f (D.harrisBilinearDiagonal β hβ S g) =
      D.harrisBilinearDiagonal β hβ T g := by
  apply Subtype.ext
  apply Prod.ext
  · ext x
    simp only [harrisTraceSimilitudesMap_apply, harrisBilinearDiagonal_apply,
      one_mul, AlgebraInvolution.changeCoefficients_tmul, map_one]
  · apply Units.ext
    exact f.commutes _

/-- Finite adelic trace similitudes evaluate in the actual finite completion. -/
def harrisFiniteLocalTraceSimilitudesMap (v : Langlands.Global.FinitePlace ℚ) :
    D.harrisBilinearSimilitudes β hβ (Langlands.Global.FiniteAdeles ℚ) →*
      D.harrisBilinearSimilitudes β hβ (Langlands.Global.FiniteCompletion ℚ v) :=
  D.harrisTraceSimilitudesMap β hβ (AlgebraInvolution.finiteEvaluation v)

/-- The actual finite-local map commutes with the original algebraic comparison. -/
theorem harrisFiniteLocalTraceSimilitudesEquiv_natural
    (v : Langlands.Global.FinitePlace ℚ)
    (g : D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) :
    D.harrisFiniteLocalTraceSimilitudesMap β hβ v
        (D.harrisFiniteAdelicTraceSimilitudesEquiv β hβ g) =
      D.harrisTraceSimilitudesEquiv (Langlands.Global.FiniteCompletion ℚ v) β hβ
        ((D.toSecondKindInvolution.rationalInvolution.pointsMap
          (AlgebraInvolution.finiteEvaluation v)).op g) :=
  D.harrisTraceSimilitudesEquiv_natural β hβ _ g

/-- Local evaluation of the finite adelic rational diagonal is the local diagonal. -/
theorem harrisFiniteLocalTraceSimilitudesMap_diagonal
    (v : Langlands.Global.FinitePlace ℚ)
    (g : PEL.bilinearSimilitudes A ((D.skewTwist β hβ).tracePairing β⁻¹)) :
    D.harrisFiniteLocalTraceSimilitudesMap β hβ v
        (D.harrisBilinearDiagonal β hβ (Langlands.Global.FiniteAdeles ℚ) g) =
      D.harrisBilinearDiagonal β hβ (Langlands.Global.FiniteCompletion ℚ v) g :=
  D.harrisTraceSimilitudesMap_diagonal β hβ _ g

end Langlands.Shimura.CentralSimpleUnitaryData

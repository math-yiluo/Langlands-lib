import Langlands.Shimura.Unitary.RationalScalarExtension
import Langlands.Global.AdelicFunctoriality.CompletedTensorComparisonProof
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Harris coefficient spaces and the product of actual completions -/

noncomputable section

universe u v w

open scoped TensorProduct

namespace Langlands.Shimura.Coefficients

open Langlands.Global AdelicFunctoriality

variable (L : Type u) [Field L] [NumberField L]
variable (p : FinitePlace ℚ)

/-- The canonical projection from Harris's coefficient algebra to one completion. -/
def harrisCoefficientProjection (l : FinitePlace L) [l.asIdeal.LiesOver p.asIdeal] :
    L ⊗[ℚ] FiniteCompletion ℚ p →ₐ[L] FiniteCompletion L l :=
  Algebra.TensorProduct.lift (Algebra.ofId L (FiniteCompletion L l))
    (FiniteExtension.completionMap p l).toRatAlgHom (fun _ _ => Commute.all _ _)

@[simp] theorem harrisCoefficientProjection_tmul (l : FinitePlace L)
    [l.asIdeal.LiesOver p.asIdeal] (a : L) (b : FiniteCompletion ℚ p) :
    harrisCoefficientProjection L p l (a ⊗ₜ[ℚ] b) =
      algebraMap L (FiniteCompletion L l) a * FiniteExtension.completionMap p l b := by
  simp [harrisCoefficientProjection]

@[simp] theorem harrisCoefficientProjection_includeRight (l : FinitePlace L)
    [l.asIdeal.LiesOver p.asIdeal] :
    ((harrisCoefficientProjection L p l).restrictScalars ℚ).comp
        Algebra.TensorProduct.includeRight =
      (FiniteExtension.completionMap p l).toRatAlgHom := by
  ext b
  simp [Algebra.TensorProduct.includeRight_apply]

/-- All the actual places of `L` above `p`, with their canonical projections. -/
def harrisCoefficientRingMap :
    L ⊗[ℚ] FiniteCompletion ℚ p →ₐ[L]
      ((l : FinitePlacesAbove L p) → FiniteCompletion L l.1) :=
  AlgHom.pi fun l => harrisCoefficientProjection L p l.1

/-- Bijectivity is the published completed-tensor theorem, with the factors exchanged. -/
theorem harrisCoefficientRingMap_bijective :
    Function.Bijective (harrisCoefficientRingMap L p) := by
  have heq : (harrisCoefficientRingMap L p : _ → _) =
      (finiteTensorMap (L := L) p) ∘
        (Algebra.TensorProduct.comm ℚ L (FiniteCompletion ℚ p)) := by
    funext x
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      ext l
      simp [harrisCoefficientRingMap, mul_comm]
    | add x y hx hy => simp only [map_add, Function.comp_apply, hx, hy]
  rw [heq]
  exact ((completedTensorComparison ℚ L).1 p).comp
    (Algebra.TensorProduct.comm ℚ L (FiniteCompletion ℚ p)).bijective

/-- Harris's coefficient algebra is the product of the actual completed fields above `p`. -/
def harrisCoefficientRingEquiv :
    L ⊗[ℚ] FiniteCompletion ℚ p ≃ₐ[L]
      ((l : FinitePlacesAbove L p) → FiniteCompletion L l.1) :=
  AlgEquiv.ofBijective (harrisCoefficientRingMap L p) (harrisCoefficientRingMap_bijective L p)

@[simp] theorem harrisCoefficientRingEquiv_apply
    (x : L ⊗[ℚ] FiniteCompletion ℚ p) (l : FinitePlacesAbove L p) :
    harrisCoefficientRingEquiv L p x l = harrisCoefficientProjection L p l.1 x := rfl

variable (W : Type w) [AddCommGroup W] [Module L W]

/-- The actual coefficient module, decomposed over all places above `p`. -/
def harrisCoefficientEquiv :
    ((L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W) ≃ₗ[L]
      ((l : FinitePlacesAbove L p) → FiniteCompletion L l.1 ⊗[L] W) := by
  classical
  exact (harrisCoefficientRingEquiv L p).toLinearEquiv.rTensor W ≪≫ₗ
    TensorProduct.piLeft L W (fun l : FinitePlacesAbove L p => FiniteCompletion L l.1)

@[simp] theorem harrisCoefficientEquiv_tmul
    (s : L ⊗[ℚ] FiniteCompletion ℚ p) (x : W) (l : FinitePlacesAbove L p) :
    harrisCoefficientEquiv L p W (s ⊗ₜ[L] x) l =
      harrisCoefficientProjection L p l.1 s ⊗ₜ[L] x := by
  simp [harrisCoefficientEquiv, TensorProduct.piLeft]

/-- Each component of the isomorphism is the canonical tensor projection. -/
theorem harrisCoefficientEquiv_apply
    (x : (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W) (l : FinitePlacesAbove L p) :
    harrisCoefficientEquiv L p W x l =
      (harrisCoefficientProjection L p l.1).toLinearMap.rTensor W x := by
  induction x using TensorProduct.inductionOn with
  | tmul s x => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

end Langlands.Shimura.Coefficients

namespace Langlands.Shimura.AlgebraInvolution

variable {A : Type v} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A)

/-- Composition on the named point groups is composition of the actual coefficient maps. -/
theorem pointsMap_comp_apply {R S T : Type*} [CommRing R] [Algebra ℚ R]
    [CommRing S] [Algebra ℚ S] [CommRing T] [Algebra ℚ T]
    (f : R →ₐ[ℚ] S) (g : S →ₐ[ℚ] T) (x : σ.Points R) :
    σ.pointsMap (g.comp f) x = σ.pointsMap g (σ.pointsMap f x) := by
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    change changeCoefficients (g.comp f) (x.1.1 : R ⊗[ℚ] A) =
      changeCoefficients g (changeCoefficients f (x.1.1 : R ⊗[ℚ] A))
    rw [changeCoefficients_comp]
    rfl
  · apply Units.ext
    rfl

namespace AlgebraicRepresentation

open Langlands.Global AdelicFunctoriality Coefficients

variable {σ} {L : Type u} [Field L] [NumberField L]
variable {W : Type w} [AddCommGroup W] [Module L W]
variable (ρ : (σ.baseChange L).AlgebraicRepresentation W) (p : FinitePlace ℚ)

/-- Componentwise evaluation of the local representation in all completions above `p`. -/
def harrisProductLocal :
    σ.Points (FiniteCompletion ℚ p) →*
      (((l : FinitePlacesAbove L p) → FiniteCompletion L l.1 ⊗[L] W) ≃ₗ[L]
        ((l : FinitePlacesAbove L p) → FiniteCompletion L l.1 ⊗[L] W)) where
  toFun g := LinearEquiv.piCongrRight fun l =>
    (ρ.actVia (FiniteExtension.completionMap p l.1).toRatAlgHom g).restrictScalars L
  map_one' := by ext x l; simp
  map_mul' g h := by ext x l; simp [LinearEquiv.mul_apply]

@[simp] theorem harrisProductLocal_apply (g : σ.Points (FiniteCompletion ℚ p))
    (x : (l : FinitePlacesAbove L p) → FiniteCompletion L l.1 ⊗[L] W)
    (l : FinitePlacesAbove L p) :
    ρ.harrisProductLocal p g x l =
      ρ.actVia (FiniteExtension.completionMap p l.1).toRatAlgHom g (x l) := rfl

/-- The coefficient projection carries the actual tensor-valued point to the completion-valued point. -/
theorem harrisCoefficientProjection_points (l : FinitePlacesAbove L p)
    (g : σ.Points (FiniteCompletion ℚ p)) :
    (σ.baseChange L).pointsMap (harrisCoefficientProjection L p l.1)
        (σ.towerPoints L (L ⊗[ℚ] FiniteCompletion ℚ p)
          (σ.pointsMap Algebra.TensorProduct.includeRight g)) =
      σ.towerPoints L (FiniteCompletion L l.1)
        (σ.pointsMap (FiniteExtension.completionMap p l.1).toRatAlgHom g) := by
  rw [← σ.towerPoints_naturality L]
  congr 1
  rw [← σ.pointsMap_comp_apply, harrisCoefficientProjection_includeRight]

/-- The canonical module splitting intertwines Harris's actual local action. -/
theorem harrisCoefficientEquiv_local (g : σ.Points (FiniteCompletion ℚ p))
    (x : (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W) :
    harrisCoefficientEquiv L p W (ρ.harrisLocal p g x) =
      ρ.harrisProductLocal p g (harrisCoefficientEquiv L p W x) := by
  ext l
  rw [harrisCoefficientEquiv_apply, harrisProductLocal_apply, harrisCoefficientEquiv_apply]
  have h := ρ.naturality (harrisCoefficientProjection L p l.1)
    (σ.towerPoints L (L ⊗[ℚ] FiniteCompletion ℚ p)
      (σ.pointsMap Algebra.TensorProduct.includeRight g)) x
  rw [harrisCoefficientProjection_points (σ := σ) (L := L) p l g] at h
  exact h.symm

variable [Module.Finite ℚ A]

/-- The finite-adelic action on Harris's whole tensor coefficient space. -/
def harrisAdelic :
    σ.FiniteAdelicPoints →*
      (((L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W) ≃ₗ[L ⊗[ℚ] FiniteCompletion ℚ p]
        ((L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W)) :=
  (ρ.harrisLocal p).comp (σ.finiteLocalMap p).toMonoidHom

/-- All actual completion actions assembled into one linear product action. -/
def harrisProductAdelic :
    σ.FiniteAdelicPoints →*
      (((l : FinitePlacesAbove L p) → FiniteCompletion L l.1 ⊗[L] W) ≃ₗ[L]
        ((l : FinitePlacesAbove L p) → FiniteCompletion L l.1 ⊗[L] W)) :=
  (ρ.harrisProductLocal p).comp (σ.finiteLocalMap p).toMonoidHom

@[simp] theorem harrisProductAdelic_apply (g : σ.FiniteAdelicPoints)
    (x : (l : FinitePlacesAbove L p) → FiniteCompletion L l.1 ⊗[L] W)
    (l : FinitePlacesAbove L p) :
    ρ.harrisProductAdelic p g x l = ρ.placeAction p l.1 g (x l) := rfl

/-- The adelic coefficient splitting is equivariant for the original actions. -/
theorem harrisCoefficientEquiv_adelic (g : σ.FiniteAdelicPoints)
    (x : (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W) :
    harrisCoefficientEquiv L p W (ρ.harrisAdelic p g x) =
      ρ.harrisProductAdelic p g (harrisCoefficientEquiv L p W x) :=
  ρ.harrisCoefficientEquiv_local p (σ.finiteLocalMap p g) x

/-- On the rational diagonal each factor is the scalar extension of the same rational action. -/
theorem harrisCoefficientEquiv_diagonal (g : σ.similitudes)
    (x : (L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W) (l : FinitePlacesAbove L p) :
    harrisCoefficientEquiv L p W (ρ.harrisAdelic p (σ.finiteAdelicDiagonal g) x) l =
      (ρ.rationalAction (σ.diagonalPoints L g)).baseChange L (FiniteCompletion L l.1) W W
        (harrisCoefficientEquiv L p W x l) := by
  rw [harrisCoefficientEquiv_adelic, harrisProductAdelic_apply, placeAction_diagonal]

end AlgebraicRepresentation
end Langlands.Shimura.AlgebraInvolution

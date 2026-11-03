import Langlands.Representation.MatrixCoefficient.LawsProof
import Langlands.Representation.Category.Contragredient
import Langlands.Representation.Smooth.Contragredient.Equivalence
import Langlands.Representation.Smooth.SmoothPart.BasicProof
import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Coefficient tensors of a canonical smooth representation

The tensor coefficient formula used in Waldspurger V.1, before the comparison
with product induction. The two group coordinates act on the vector and smooth
functional, respectively.
-/

noncomputable section

open scoped TensorProduct

namespace Langlands.Plancherel

universe uR uG uV uW uX

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]

/-- The algebraic tensor of a smooth representation with its actual smooth dual. -/
abbrev CoefficientTensor (A : SmoothRep.{uR, uG, uV} R G) :=
  A ⊗[R] SmoothDual A.representation

/-- The bilinear coefficient with values in locally constant functions. -/
def smoothCoefficientBilinear (A : SmoothRep.{uR, uG, uV} R G) :
    A →ₗ[R] SmoothDual A.representation →ₗ[R] LocallyConstant G R where
  toFun v :=
    { toFun := fun ℓ =>
        ⟨matrixCoefficient A.representation ℓ.val v,
          matrixCoefficient_isLocallyConstant A.representation ℓ.val v (A.isSmooth v)⟩
      map_add' := fun ℓ m => by ext g; rfl
      map_smul' := fun a ℓ => by ext g; rfl }
  map_add' v w := by ext ℓ g; simp [matrixCoefficient]
  map_smul' a v := by ext ℓ g; simp [matrixCoefficient]

/-- The actual linear extension `v ⊗ ℓ ↦ (g ↦ ℓ(π(g)v))`. -/
def coefficientTensorMap (A : SmoothRep.{uR, uG, uV} R G) :
    CoefficientTensor A →ₗ[R] LocallyConstant G R :=
  TensorProduct.lift (smoothCoefficientBilinear A)

@[simp]
theorem coefficientTensorMap_tmul (A : SmoothRep.{uR, uG, uV} R G)
    (v : A) (ℓ : SmoothDual A.representation) (g : G) :
    coefficientTensorMap A (v ⊗ₜ[R] ℓ) g = ℓ.val (A.representation g v) := rfl

/-- The external action: the first coordinate acts on vectors, the second on
smooth functionals. -/
def coefficientTensorAction (A : SmoothRep.{uR, uG, uV} R G) :
    Representation R (G × G) (CoefficientTensor A) :=
  Representation.tprod (A.representation.comp (MonoidHom.fst G G))
    ((smoothContragredient A.representation).comp (MonoidHom.snd G G))

@[simp]
theorem coefficientTensorAction_tmul (A : SmoothRep.{uR, uG, uV} R G)
    (x : G × G) (v : A) (ℓ : SmoothDual A.representation) :
    coefficientTensorAction A x (v ⊗ₜ[R] ℓ) =
      A.representation x.1 v ⊗ₜ[R] smoothContragredient A.representation x.2 ℓ := rfl

/-- Product stabilizers and pure-tensor spanning prove smoothness of the external action. -/
theorem isSmooth_coefficientTensorAction (A : SmoothRep.{uR, uG, uV} R G) :
    IsSmooth (coefficientTensorAction A) := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    obtain ⟨K, hK⟩ := A.isSmooth v
    obtain ⟨L, hL⟩ := isSmooth_smoothContragredient A.representation ℓ
    refine ⟨K.prod L, ?_⟩
    intro x
    change A.representation (x : G × G).1 v ⊗ₜ[R]
      smoothContragredient A.representation (x : G × G).2 ℓ = v ⊗ₜ[R] ℓ
    have hv : A.representation (x : G × G).1 v = v := hK ⟨_, x.property.1⟩
    have hℓ : smoothContragredient A.representation (x : G × G).2 ℓ = ℓ :=
      hL ⟨_, x.property.2⟩
    rw [hv, hℓ]
  | add t s ht hs => exact isSmoothVector_add ht hs

/-- A genuine smooth representation of the product group on coefficient tensors. -/
def coefficientTensorObject (A : SmoothRep.{uR, uG, uV} R G) :
    SmoothRep.{uR, uG, max uR uV} R (G × G) :=
  SmoothRep.of (coefficientTensorAction A) (isSmooth_coefficientTensorAction A)

/-- The group coordinates induce right and inverse left translation of coefficients. -/
theorem coefficientTensorMap_action (A : SmoothRep.{uR, uG, uV} R G)
    (x : G × G) (t : CoefficientTensor A) (g : G) :
    coefficientTensorMap A (coefficientTensorAction A x t) g =
      coefficientTensorMap A t (x.2⁻¹ * g * x.1) := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    change ℓ.val (A.representation x.2⁻¹
      (A.representation g (A.representation x.1 v))) =
      ℓ.val (A.representation (x.2⁻¹ * g * x.1) v)
    simp only [map_mul, Module.End.mul_apply]
  | add t s ht hs => simp only [map_add, LocallyConstant.add_apply, ht, hs]

/-- Every tensor coefficient has a common open subgroup of left and right invariance. -/
theorem coefficientTensorMap_biInvariant (A : SmoothRep.{uR, uG, uV} R G)
    (t : CoefficientTensor A) :
    ∃ K : OpenSubgroup G, ∀ (k l : K) (g : G),
      coefficientTensorMap A t ((k : G) * g * (l : G)) = coefficientTensorMap A t g := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    exact matrixCoefficient_biInvariant A.representation ℓ.val v ℓ.property (A.isSmooth v)
  | add t s ht hs =>
    obtain ⟨K, hK⟩ := ht
    obtain ⟨L, hL⟩ := hs
    refine ⟨K ⊓ L, ?_⟩
    intro k l g
    simp only [map_add, LocallyConstant.add_apply,
      hK ⟨k, k.property.1⟩ ⟨l, l.property.1⟩,
      hL ⟨k, k.property.2⟩ ⟨l, l.property.2⟩]

/-- The image is exactly the linear span of the actual smooth matrix coefficients. -/
theorem range_coefficientTensorMap (A : SmoothRep.{uR, uG, uV} R G) :
    LinearMap.range (coefficientTensorMap A) =
      Submodule.span R {f | ∃ (v : A) (ℓ : SmoothDual A.representation),
        f = smoothCoefficientBilinear A v ℓ} := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul v ℓ => exact Submodule.subset_span ⟨v, ℓ, rfl⟩
    | add t s ht hs => simpa only [map_add] using Submodule.add_mem _ ht hs
  · apply Submodule.span_le.mpr
    rintro _ ⟨v, ℓ, rfl⟩
    exact ⟨v ⊗ₜ[R] ℓ, rfl⟩

variable {A : SmoothRep.{uR, uG, uV} R G} {B : SmoothRep.{uR, uG, uW} R G}
  {C : SmoothRep.{uR, uG, uX} R G}

/-- Transport a tensor by `e` on vectors and inverse pullback on smooth functionals. -/
def coefficientTensorCongr (e : A.representation.Equiv B.representation) :
    CoefficientTensor A ≃ₗ[R] CoefficientTensor B :=
  TensorProduct.congr e.toLinearEquiv (smoothContragredientEquiv e.symm).toLinearEquiv

@[simp]
theorem coefficientTensorCongr_tmul (e : A.representation.Equiv B.representation)
    (v : A) (ℓ : SmoothDual A.representation) :
    coefficientTensorCongr e (v ⊗ₜ[R] ℓ) =
      e v ⊗ₜ[R] contragredientMap e.symm.toIntertwiningMap ℓ := rfl

/-- Isomorphism transport preserves the coefficient at every group element. -/
theorem coefficientTensorMap_congr (e : A.representation.Equiv B.representation)
    (t : CoefficientTensor A) :
    coefficientTensorMap B (coefficientTensorCongr e t) = coefficientTensorMap A t := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    ext g
    change ℓ.val (e.symm (B.representation g (e v))) = ℓ.val (A.representation g v)
    have he : e (A.representation g v) = B.representation g (e v) :=
      congrArg (fun T : A →ₗ[R] B => T v) (e.isIntertwining' g)
    rw [← he, e.symm_apply_apply]
  | add t s ht hs => simp only [map_add, ht, hs]

/-- Tensor transport intertwines the actual product-group actions. -/
theorem coefficientTensorCongr_action (e : A.representation.Equiv B.representation)
    (x : G × G) (t : CoefficientTensor A) :
    coefficientTensorCongr e (coefficientTensorAction A x t) =
      coefficientTensorAction B x (coefficientTensorCongr e t) := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    simp only [coefficientTensorAction_tmul, coefficientTensorCongr_tmul]
    have he : e (A.representation x.1 v) = B.representation x.1 (e v) :=
      congrArg (fun T : A →ₗ[R] B => T v) (e.isIntertwining' x.1)
    rw [he,
      (contragredientMap e.symm.toIntertwiningMap).isIntertwining]
  | add t s ht hs => simp only [map_add, ht, hs]

@[simp]
theorem coefficientTensorCongr_refl (t : CoefficientTensor A) :
    coefficientTensorCongr (Representation.Equiv.refl A.representation) t = t := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ => rfl
  | add t s ht hs => simp only [map_add, ht, hs]

/-- Successive changes of representation are the change by the composite equivalence. -/
theorem coefficientTensorCongr_trans (e : A.representation.Equiv B.representation)
    (f : B.representation.Equiv C.representation) (t : CoefficientTensor A) :
    coefficientTensorCongr (e.trans f) t =
      coefficientTensorCongr f (coefficientTensorCongr e t) := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ => rfl
  | add t s ht hs => simp only [map_add, ht, hs]

end Langlands.Plancherel

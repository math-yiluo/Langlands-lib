import Langlands.Global.AdelicBlockFactorInduction
import Langlands.Global.AdelicParabolicInductionTopology
import Langlands.Representation.Smooth.SmallRealizationProof
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Actual normed tensor models for finite-dimensional adelic block coefficients

Choose finite bases of the factors and use the coordinate space of their
genuine tensor basis. The original coefficient modules need no topology.
-/

noncomputable section

universe uF uV uW uX

namespace Langlands.Global.AdelicFiniteDimensionalBlockModel

open NumberField IsDedekindDomain
open Langlands.GeneralLinear AdelicBlockParabolic
open scoped BigOperators

variable {n : ℕ} (B : BlockShape n)
variable (V : Fin B.length → Type uV)
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- Finite multi-indices of the chosen factor bases, in the smallest universe. -/
abbrev Index := ∀ i : Fin B.length, Fin (Module.finrank ℂ (V i))

/-- A genuine finite function space with its usual complex sup norm. -/
abbrev Model := Index B V → ℂ

theorem model_finrank :
    Module.finrank ℂ (Model B V) = ∏ i, Module.finrank ℂ (V i) := by
  simp [Model, Index, Fintype.card_pi]

variable [∀ i, FiniteDimensional ℂ (V i)]

/-- Actual coordinates of the tensor product of Mathlib's chosen finite bases. -/
def tensorEquiv : PiTensorProduct ℂ V ≃ₗ[ℂ] Model B V := by
  classical
  exact (Basis.piTensorProduct (fun i => Module.finBasis ℂ (V i))).equivFun

@[simp]
theorem tensorEquiv_tprod (v : ∀ i, V i) (p : Index B V) :
    tensorEquiv B V (PiTensorProduct.tprod ℂ v) p =
      ∏ i, (Module.finBasis ℂ (V i)).repr (v i) (p i) := by
  classical
  simp [tensorEquiv, Module.Basis.equivFun_apply,
    Basis.piTensorProduct_repr_tprod_apply]

variable (F : Type uF) [Field F] [NumberField F]
variable (σ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (V i))

/-- The actual tensor action in the constructed normed coordinate space. -/
abbrev coefficientAction : Representation ℂ (FullLevi F B) (Model B V) :=
  Langlands.transportRepresentation (B.blockTensor σ) (tensorEquiv B V)

/-- The coordinate map is a genuine equivalence of the tensor representations. -/
abbrev coefficientEquiv : (B.blockTensor σ).Equiv (coefficientAction B V F σ) :=
  Langlands.transportRepresentationEquiv (B.blockTensor σ) (tensorEquiv B V)

@[simp]
theorem coefficientAction_apply (m : FullLevi F B) (v : Model B V) :
    coefficientAction B V F σ m v =
      tensorEquiv B V (B.blockTensor σ m ((tensorEquiv B V).symm v)) := rfl

/-- The constructed coordinate action has the original factorwise tensor formula. -/
theorem coefficientAction_tprod (m : FullLevi F B) (v : ∀ i, V i) (p : Index B V) :
    coefficientAction B V F σ m (tensorEquiv B V (PiTensorProduct.tprod ℂ v)) p =
      ∏ i, (Module.finBasis ℂ (V i)).repr (σ i (m i) (v i)) (p i) := by
  rw [coefficientAction_apply, (tensorEquiv B V).symm_apply_apply,
    BlockShape.blockTensor_tprod, tensorEquiv_tprod]

/-- Actual smooth sections with the constructed finite-dimensional coefficients. -/
abbrev CompactOpenSections :=
  AdelicParabolicInduction.CompactOpenSections F B (coefficientAction B V F σ)

/-- Full adelic right translation on these actual sections. -/
abbrev rightAction : Representation ℂ (AdelicGL F n) (CompactOpenSections B V F σ) :=
  AdelicParabolicInduction.CompactOpenSections.rightAction F B
    (coefficientAction B V F σ)

section Maps

variable {V}
variable {W : Fin B.length → Type uW} {X : Fin B.length → Type uX}
variable [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
variable [∀ i, FiniteDimensional ℂ (W i)] [∀ i, FiniteDimensional ℂ (X i)]
variable {σ}
variable {τ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (W i)}
variable {υ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (X i)}

/-- Transport the actual tensor of block intertwiners between the constructed models. -/
def coefficientMap (T : ∀ i, (σ i).IntertwiningMap (τ i)) :
    (coefficientAction B V F σ).IntertwiningMap (coefficientAction B W F τ) :=
  (coefficientEquiv B W F τ).toIntertwiningMap.comp
    ((FiniteTensor.externalMap T).comp
      (coefficientEquiv B V F σ).symm.toIntertwiningMap)

@[simp]
theorem coefficientMap_apply (T : ∀ i, (σ i).IntertwiningMap (τ i)) (v : Model B V) :
    coefficientMap B F T v =
      tensorEquiv B W (FiniteTensor.externalMap T ((tensorEquiv B V).symm v)) := rfl

@[simp]
theorem coefficientMap_tprod (T : ∀ i, (σ i).IntertwiningMap (τ i))
    (v : ∀ i, V i) (p : Index B W) :
    coefficientMap B F T (tensorEquiv B V (PiTensorProduct.tprod ℂ v)) p =
      ∏ i, (Module.finBasis ℂ (W i)).repr (T i (v i)) (p i) := by
  rw [coefficientMap_apply, (tensorEquiv B V).symm_apply_apply,
    FiniteTensor.externalMap_tprod, tensorEquiv_tprod]

/-- Continuity is proved in the actual finite-dimensional model; T needs no topology. -/
theorem continuous_coefficientMap (T : ∀ i, (σ i).IntertwiningMap (τ i)) :
    Continuous (coefficientMap B F T) :=
  (coefficientMap B F T).toLinearMap.continuous_of_finiteDimensional

@[simp]
theorem coefficientMap_id :
    coefficientMap B F (fun i => Representation.IntertwiningMap.id (σ i)) =
      Representation.IntertwiningMap.id (coefficientAction B V F σ) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  change tensorEquiv B V
    (FiniteTensor.externalMap (fun i => Representation.IntertwiningMap.id (σ i))
      ((tensorEquiv B V).symm v)) = v
  rw [FiniteTensor.externalMap_id]
  exact (tensorEquiv B V).apply_symm_apply v

theorem coefficientMap_comp (T : ∀ i, (σ i).IntertwiningMap (τ i))
    (S : ∀ i, (τ i).IntertwiningMap (υ i)) :
    coefficientMap B F (fun i => (S i).comp (T i)) =
      (coefficientMap B F S).comp (coefficientMap B F T) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  simp only [Representation.IntertwiningMap.toLinearMap_apply,
    Representation.IntertwiningMap.comp_apply, coefficientMap_apply,
    LinearEquiv.symm_apply_apply, FiniteTensor.externalMap_comp]

/-- Every algebraic family of block intertwiners induces an actual continuous section map. -/
def mapCLM (T : ∀ i, (σ i).IntertwiningMap (τ i)) :
    CompactOpenSections B V F σ →L[ℂ] CompactOpenSections B W F τ :=
  AdelicParabolicInduction.CompactOpenSections.mapCLM F B
    (coefficientMap B F T) (continuous_coefficientMap B F T)

@[simp]
theorem mapCLM_apply (T : ∀ i, (σ i).IntertwiningMap (τ i))
    (f : CompactOpenSections B V F σ) (x : AdelicGL F n) :
    AdelicParabolicInduction.CompactOpenSections.toContinuousMap F B
      (coefficientAction B W F τ) (mapCLM B F T f) x =
        tensorEquiv B W
          (FiniteTensor.externalMap T ((tensorEquiv B V).symm
            (AdelicParabolicInduction.CompactOpenSections.toContinuousMap F B
              (coefficientAction B V F σ) f x))) := rfl

@[simp]
theorem mapCLM_id :
    mapCLM B F (fun i => Representation.IntertwiningMap.id (σ i)) =
      ContinuousLinearMap.id ℂ (CompactOpenSections B V F σ) := by
  simp only [mapCLM, coefficientMap_id,
    AdelicParabolicInduction.CompactOpenSections.mapCLM_id]

theorem mapCLM_comp (T : ∀ i, (σ i).IntertwiningMap (τ i))
    (S : ∀ i, (τ i).IntertwiningMap (υ i)) :
    mapCLM B F (fun i => (S i).comp (T i)) =
      (mapCLM B F S).comp (mapCLM B F T) := by
  simpa only [mapCLM, coefficientMap_comp] using
    AdelicParabolicInduction.CompactOpenSections.mapCLM_comp F B
      (coefficientMap B F T) (coefficientMap B F S)
      (continuous_coefficientMap B F T) (continuous_coefficientMap B F S)

theorem mapCLM_rightAction (T : ∀ i, (σ i).IntertwiningMap (τ i))
    (g : AdelicGL F n) (f : CompactOpenSections B V F σ) :
    mapCLM B F T (rightAction B V F σ g f) =
      rightAction B W F τ g (mapCLM B F T f) :=
  AdelicParabolicInduction.CompactOpenSections.mapCLM_rightAction F B
    (coefficientMap B F T) (continuous_coefficientMap B F T) g f

end Maps

section CentralCharacter

variable (c : Fin B.length → HeckeCharacter F)
variable (hσ : ∀ i (z : Ideles F) (v : V i),
  σ i (AdelicGL.scalar F (B.size i) z) v = ((c i).onIdeles z : ℂ) • v)

include hσ

/-- The constructed model retains the unweighted whole-block product central action. -/
theorem coefficientAction_scalar (z : Ideles F) (v : Model B V) :
    coefficientAction B V F σ (AdelicBlockCenter.scalarLevi F B z) v =
      ((AdelicBlockFactorInduction.centralCharacter F B c).onIdeles z : ℂ) • v := by
  rw [coefficientAction_apply, AdelicBlockFactorInduction.blockTensor_scalar F B σ c hσ,
    map_smul, (tensorEquiv B V).apply_symm_apply]

/-- The actual compact-open model sections have the same product central action. -/
theorem rightAction_scalar (z : Ideles F) (f : CompactOpenSections B V F σ) :
    rightAction B V F σ (AdelicGL.scalar F n z) f =
      ((AdelicBlockFactorInduction.centralCharacter F B c).onIdeles z : ℂ) • f :=
  AdelicParabolicInduction.smoothInduced_scalar F B (coefficientAction B V F σ)
    (AdelicBlockFactorInduction.centralCharacter F B c).onIdeles.toMonoidHom
    (coefficientAction_scalar B V F σ c hσ) z f

end CentralCharacter

end Langlands.Global.AdelicFiniteDimensionalBlockModel

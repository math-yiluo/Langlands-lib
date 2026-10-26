import Langlands.Representation.Tensor.Finite
import Langlands.Representation.Tensor.Filtration
import Langlands.Representation.Filtration.ObjectTransport
import Mathlib.LinearAlgebra.PiTensorProduct.Generators

/-! Lift an actual filtration in one slot to the indexed tensor product. -/

noncomputable section

open scoped TensorProduct

namespace Langlands.FiniteTensor

universe uR uI uG uV uW

section Equivalences

variable {R : Type uR} [CommRing R] {ι : Type uI}
  {G : Type uG} [Group G]
  {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
  {W : ι → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
  {ρ : ∀ i, Representation R G (V i)} {σ : ∀ i, Representation R G (W i)}

/-- A family of actual equivalences induces an equivalence of indexed actions. -/
def congrEquiv (e : ∀ i, (ρ i).Equiv (σ i)) : (action ρ).Equiv (action σ) :=
  Representation.Equiv.mk (PiTensorProduct.congr (fun i => (e i).toLinearEquiv))
    (fun g => by
      ext v
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe, action_tprod, PiTensorProduct.congr_tprod]
      congr 1
      funext i
      exact LinearMap.congr_fun ((e i).isIntertwining' g) (v i))

@[simp]
theorem congrEquiv_tprod (e : ∀ i, (ρ i).Equiv (σ i)) (v : ∀ i, V i) :
    congrEquiv e (PiTensorProduct.tprod R v) =
      PiTensorProduct.tprod R (fun i => e i (v i)) :=
  PiTensorProduct.congr_tprod _ _

variable [DecidableEq ι]

/-- Split off any specified tensor slot, intertwining the actual actions. -/
def slotEquiv (ρ : ∀ i, Representation R G (V i)) (j : ι) :
    (action ρ).Equiv
      (Representation.tprod (action (fun i : ({j}ᶜ : Set ι) => ρ i)) (ρ j)) :=
  Representation.Equiv.mk (PiTensorProduct.equivPiTensorComplSingletonTensor R V j)
    (fun g => by
      ext v
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe, action_tprod,
        PiTensorProduct.equivPiTensorComplSingletonTensor_tprod,
        Representation.tprod_apply, TensorProduct.map_tmul]
      rfl)

@[simp]
theorem slotEquiv_tprod (ρ : ∀ i, Representation R G (V i)) (j : ι)
    (v : ∀ i, V i) :
    slotEquiv ρ j (PiTensorProduct.tprod R v) =
      PiTensorProduct.tprod R (fun i : ({j}ᶜ : Set ι) => v i) ⊗ₜ[R] v j :=
  PiTensorProduct.equivPiTensorComplSingletonTensor_tprod R V j v

end Equivalences

section Filtration

variable {k : Type uR} [Field k] {ι : Type uI} [DecidableEq ι]
  {G : Type uG} [Group G]
  {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  (ρ : ∀ i, Representation k G (V i)) (j : ι) {n : ℕ}
  (s : ObjectRepFiltration (Rep.of (ρ j)) n)

/-- Tensor a supplied slot filtration with the complement, then transport it
back to the original indexed tensor product. -/
def slotFiltration : ObjectRepFiltration (Rep.of (action ρ)) n :=
  LengthTwo.transport (slotEquiv ρ j).symm
    (s.tensorLeft (Rep.of (action (fun i : ({j}ᶜ : Set ι) => ρ i))))

/-- The actual graded quotient is the tensor of the complement action with the
original actual slot quotient. -/
def slotFiltrationGradedEquiv (i : Fin n) :
    ((slotFiltration ρ j s).gradedRepresentation i).ρ.Equiv
      (Representation.tprod (action (fun h : ({j}ᶜ : Set ι) => ρ h))
        (s.gradedRepresentation i).ρ) := by
  let C := Rep.of (action (fun h : ({j}ᶜ : Set ι) => ρ h))
  let t := s.tensorLeft C
  let e := (slotEquiv ρ j).symm
  let a := t.equivTransportGradedEquiv (B := Rep.of (action ρ)) e i
  exact a.symm.trans (s.tensorLeftGradedEquiv C i)

variable {W : ι → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]
  (σ : ∀ i, Representation k G (W i))

/-- Replace the graded slot by a supplied actual equivalent factor and the
complement by supplied equivalent factors, then reassemble the indexed tensor. -/
def slotFiltrationGradedEquivOfFamily (i : Fin n)
    (e : ∀ h : ({j}ᶜ : Set ι), (ρ h).Equiv (σ h))
    (f : (s.gradedRepresentation i).ρ.Equiv (σ j)) :
    ((slotFiltration ρ j s).gradedRepresentation i).ρ.Equiv (action σ) :=
  (slotFiltrationGradedEquiv ρ j s i).trans
    ((Representation.Equiv.mk
      (TensorProduct.congr (congrEquiv e).toLinearEquiv f.toLinearEquiv)
      (fun g => ((congrEquiv e).toIntertwiningMap.tensor f.toIntertwiningMap).isIntertwining' g)).trans
        (slotEquiv σ j).symm)

/-- A supplied map from the original slot quotient gives an actual map from the
full tensor filtration quotient to a supplied replacement tensor family. -/
def slotFiltrationGradedMap (i : Fin n)
    (e : ∀ h : ({j}ᶜ : Set ι), (ρ h).Equiv (σ h))
    (f : (s.gradedRepresentation i).ρ.IntertwiningMap (σ j)) :
    ((slotFiltration ρ j s).gradedRepresentation i).ρ.IntertwiningMap (action σ) :=
  (slotEquiv σ j).symm.toIntertwiningMap.comp
    (((congrEquiv e).toIntertwiningMap.tensor f).comp
      (slotFiltrationGradedEquiv ρ j s i).toIntertwiningMap)

/-- Tensor exactness over a field preserves injectivity of the supplied slot map. -/
theorem slotFiltrationGradedMap_injective (i : Fin n)
    (e : ∀ h : ({j}ᶜ : Set ι), (ρ h).Equiv (σ h))
    (f : (s.gradedRepresentation i).ρ.IntertwiningMap (σ j))
    (hf : Function.Injective f) :
    Function.Injective (slotFiltrationGradedMap ρ j s σ i e f) :=
  (slotEquiv σ j).symm.injective.comp
    ((TensorProduct.map_injective_of_flat_flat
      (congrEquiv e).toLinearMap f.toLinearMap (congrEquiv e).injective hf).comp
        (slotFiltrationGradedEquiv ρ j s i).injective)

end Filtration

end Langlands.FiniteTensor

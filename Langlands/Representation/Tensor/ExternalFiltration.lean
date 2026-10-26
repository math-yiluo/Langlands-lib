import Langlands.Representation.Tensor.FiniteFiltration

/-! Lift a supplied factor filtration to the actual external tensor action. -/

noncomputable section

open scoped TensorProduct

namespace Langlands.FiniteTensor

universe uR uI uG uV uW

variable {k : Type uR} [Field k] {ι : Type uI} [DecidableEq ι]
  {H : ι → Type uG} [∀ h, Group (H h)]
  {V : ι → Type uV} [∀ h, AddCommGroup (V h)] [∀ h, Module k (V h)]
  (ρ : ∀ h, Representation k (H h) (V h)) (j : ι) {n : ℕ}
  (s : ObjectRepFiltration (Rep.of (ρ j)) n)

/-- Pull the slot filtration through its coordinate map and lift it to the
original external tensor, retaining its actual invariant subspaces. -/
def externalSlotFiltration : ObjectRepFiltration (Rep.of (external ρ)) n :=
  slotFiltration (fun h => (ρ h).comp (Pi.evalMonoidHom H h)) j
    (s.comp (Pi.evalMonoidHom H j))

/-- The actual external tensor quotient is the complement tensor with the
original slot quotient, all acted on through the original coordinate maps. -/
def externalSlotFiltrationGradedEquiv (i : Fin n) :
    ((externalSlotFiltration ρ j s).gradedRepresentation i).ρ.Equiv
      (Representation.tprod
        (action (fun h : ({j}ᶜ : Set ι) => (ρ h).comp (Pi.evalMonoidHom H h)))
        ((s.gradedRepresentation i).ρ.comp (Pi.evalMonoidHom H j))) :=
  (slotFiltrationGradedEquiv
    (fun h => (ρ h).comp (Pi.evalMonoidHom H h)) j
    (s.comp (Pi.evalMonoidHom H j)) i).trans
    (Representation.Equiv.mk
      (TensorProduct.congr (LinearEquiv.refl k _)
        (s.compGradedEquiv (Pi.evalMonoidHom H j) i).toLinearEquiv)
      (fun g =>
        ((Representation.IntertwiningMap.id _).tensor
          (s.compGradedEquiv (Pi.evalMonoidHom H j) i).toIntertwiningMap).isIntertwining' g))

variable {W : ι → Type uW} [∀ h, AddCommGroup (W h)] [∀ h, Module k (W h)]
  (σ : ∀ h, Representation k (H h) (W h))

/-- Factor equivalences and an equivalence from the actual slot quotient
identify the full actual quotient with the replacement external tensor. -/
def externalSlotFiltrationGradedEquivOfFamily (i : Fin n)
    (e : ∀ h : ({j}ᶜ : Set ι), (ρ h).Equiv (σ h))
    (f : (s.gradedRepresentation i).ρ.Equiv (σ j)) :
    ((externalSlotFiltration ρ j s).gradedRepresentation i).ρ.Equiv
      (external σ) :=
  slotFiltrationGradedEquivOfFamily
    (fun h => (ρ h).comp (Pi.evalMonoidHom H h)) j
    (s.comp (Pi.evalMonoidHom H j))
    (fun h => (σ h).comp (Pi.evalMonoidHom H h)) i
    (fun h => Representation.Equiv.mk (e h).toLinearEquiv
      (fun g => (e h).isIntertwining' (g h)))
    ((s.compGradedEquiv (Pi.evalMonoidHom H j) i).trans
      (Representation.Equiv.mk f.toLinearEquiv
        (fun g => f.isIntertwining' (g j))))

/-- A map from the actual factor quotient gives a map from the full actual
quotient to the replacement external tensor. -/
def externalSlotFiltrationGradedMap (i : Fin n)
    (e : ∀ h : ({j}ᶜ : Set ι), (ρ h).Equiv (σ h))
    (f : (s.gradedRepresentation i).ρ.IntertwiningMap (σ j)) :
    ((externalSlotFiltration ρ j s).gradedRepresentation i).ρ.IntertwiningMap
      (external σ) :=
  slotFiltrationGradedMap
    (fun h => (ρ h).comp (Pi.evalMonoidHom H h)) j
    (s.comp (Pi.evalMonoidHom H j))
    (fun h => (σ h).comp (Pi.evalMonoidHom H h)) i
    (fun h => Representation.Equiv.mk (e h).toLinearEquiv
      (fun g => (e h).isIntertwining' (g h)))
    (({ toLinearMap := f.toLinearMap
        isIntertwining' g := f.isIntertwining' (g j) } :
          Representation.IntertwiningMap
            ((s.gradedRepresentation i).ρ.comp (Pi.evalMonoidHom H j))
            ((σ j).comp (Pi.evalMonoidHom H j))).comp
      (s.compGradedEquiv (Pi.evalMonoidHom H j) i).toIntertwiningMap)

/-- Injectivity of the actual slot map survives the external tensor lift. -/
theorem externalSlotFiltrationGradedMap_injective (i : Fin n)
    (e : ∀ h : ({j}ᶜ : Set ι), (ρ h).Equiv (σ h))
    (f : (s.gradedRepresentation i).ρ.IntertwiningMap (σ j))
    (hf : Function.Injective f) :
    Function.Injective (externalSlotFiltrationGradedMap ρ j s σ i e f) :=
  slotFiltrationGradedMap_injective
    (fun h => (ρ h).comp (Pi.evalMonoidHom H h)) j
    (s.comp (Pi.evalMonoidHom H j))
    (fun h => (σ h).comp (Pi.evalMonoidHom H h)) i
    (fun h => Representation.Equiv.mk (e h).toLinearEquiv
      (fun g => (e h).isIntertwining' (g h)))
    _ (hf.comp (s.compGradedEquiv (Pi.evalMonoidHom H j) i).injective)

end Langlands.FiniteTensor

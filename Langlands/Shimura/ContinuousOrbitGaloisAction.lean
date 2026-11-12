import Langlands.Shimura.ContinuousGaloisAction

/-! # Galois actions with continuous orbits

A Galois action on a module over a topological field `L` has continuous orbits if every orbit map
`g ↦ g · x` is continuous for the module topology. This condition makes sense without any finiteness
assumption on the module; on a finite-dimensional space it makes the representation continuous in
the sense of `Langlands.GaloisRepresentation.IsContinuous`. See `ContinuousOrbitGaloisAction.md`.
-/

noncomputable section

universe uK uL uV

open CategoryTheory

set_option autoImplicit false

namespace Langlands.Shimura.ContinuousGaloisAction

open Langlands.GaloisRepresentation (IsContinuous)

variable {K : Type uK} [Field K] {L : Type uL} [Field L] [TopologicalSpace L]
  (M : Action (ModuleCat.{uV} L) (Field.absoluteGaloisGroup K))

/-- The orbit maps `g ↦ g · x` of a Galois action on an `L`-module are continuous for the module
topology of the space over the topological field `L`. -/
def HasContinuousOrbits : Prop :=
  letI : TopologicalSpace M.V := moduleTopology L M.V
  ∀ x : M.V, Continuous fun g : Field.absoluteGaloisGroup K => (M.ρ g).hom x

/-- On a finite-dimensional space, continuous orbit maps make the Galois representation
continuous for the module topology on its endomorphisms. -/
theorem isContinuous_finiteRepresentation_of_hasContinuousOrbits [IsTopologicalRing L]
    [Module.Finite L M.V] (hM : HasContinuousOrbits M) :
    IsContinuous (finiteRepresentation M) := by
  classical
  let _ : TopologicalSpace M.V := moduleTopology L M.V
  have : IsModuleTopology L M.V := ⟨rfl⟩
  let b := Module.Free.chooseBasis L M.V
  let _ : TopologicalSpace (Module.End L M.V) := moduleTopology L (Module.End L M.V)
  have : IsModuleTopology L (Module.End L M.V) := ⟨rfl⟩
  have : ContinuousAdd (Module.End L M.V) := IsModuleTopology.toContinuousAdd L _
  have : IsModuleTopology L (Matrix (Module.Free.ChooseBasisIndex L M.V)
      (Module.Free.ChooseBasisIndex L M.V) L) :=
    inferInstanceAs (IsModuleTopology L (Module.Free.ChooseBasisIndex L M.V →
      Module.Free.ChooseBasisIndex L M.V → L))
  let e := LinearMap.toMatrix b b
  have hsymm : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  have hentries : Continuous fun g : Field.absoluteGaloisGroup K => e (M.ρ g).hom := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have heq : (fun g : Field.absoluteGaloisGroup K => e (M.ρ g).hom i j) =
        fun g => b.coord i ((M.ρ g).hom (b j)) := by
      funext g
      rw [LinearMap.toMatrix_apply]
      rfl
    rw [heq]
    exact (IsModuleTopology.continuous_of_linearMap (b.coord i)).comp (hM (b j))
  show Continuous ((ModuleCat.endRingEquiv M.V).toMonoidHom.comp M.ρ)
  have hfun : ⇑((ModuleCat.endRingEquiv M.V).toMonoidHom.comp M.ρ) =
      e.symm ∘ fun g => e (M.ρ g).hom := by
    funext g
    simp only [Function.comp_apply, LinearEquiv.symm_apply_apply]
    rfl
  rw [hfun]
  exact hsymm.comp hentries

end Langlands.Shimura.ContinuousGaloisAction

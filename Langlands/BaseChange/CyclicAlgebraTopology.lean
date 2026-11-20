import Langlands.BaseChange.Norm
import Langlands.Group.GL.LocalFieldTopology
import Langlands.Topology.LocallyProfinite
import Mathlib.Topology.Algebra.Module.ModuleTopology

noncomputable section

open Set Topology

namespace Langlands.BaseChange

open Langlands.Topology (IsLocallyProfinite isLocallyProfinite_of_mathlib)

variable {F E : Type*} [Field F] [CommRing E] [Algebra F E]
variable [TopologicalSpace F] [IsTopologicalRing F]
variable [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]

/-- The topology of a finite algebra is the product topology in a vector space basis. -/
def finiteAlgebraCoordinates [Module.Finite F E] :
    E ≃ₜ (Fin (Module.finrank F E) → F) where
  toEquiv := (Module.finBasis F E).equivFun.toEquiv
  continuous_toFun := IsModuleTopology.continuous_of_linearMap
    (Module.finBasis F E).equivFun.toLinearMap
  continuous_invFun := IsModuleTopology.continuous_of_linearMap
    (Module.finBasis F E).equivFun.symm.toLinearMap

theorem generalLinear_isLocallyProfinite_of_finiteAlgebra
    [T2Space F] [LocallyCompactSpace F] [TotallyDisconnectedSpace F]
    [Module.Finite F E] (n : ℕ) : IsLocallyProfinite (GeneralLinear n E) := by
  let e := finiteAlgebraCoordinates (F := F) (E := E)
  let : T2Space E := e.symm.t2Space
  let : LocallyCompactSpace E := e.isClosedEmbedding.locallyCompactSpace
  let : TotallyDisconnectedSpace E := e.symm.totallyDisconnectedSpace
  let : LocallyCompactSpace (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → E))
  let : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → E))
  let : TotallyDisconnectedSpace (GeneralLinear n E) :=
    ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn
      Units.val_injective (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  exact isLocallyProfinite_of_mathlib

theorem generalLinear_secondCountable_of_finiteAlgebra
    [SecondCountableTopology F] [Module.Finite F E] (n : ℕ) :
    SecondCountableTopology (GeneralLinear n E) := by
  let : SecondCountableTopology E :=
    (finiteAlgebraCoordinates (F := F) (E := E)).secondCountableTopology
  let : SecondCountableTopology (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → E))
  let : SecondCountableTopology (Matrix (Fin n) (Fin n) E)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

omit [IsTopologicalRing F] in
theorem continuous_entrywiseAut (σ : E ≃ₐ[F] E) (n : ℕ) :
    Continuous (fun g : GeneralLinear n E => entrywiseAut σ n g) :=
  (IsModuleTopology.continuous_of_linearMap σ.toLinearEquiv.toLinearMap).generalLinearGroup_map

/-- The scalar extension of the general linear group is a closed embedding. -/
theorem IsCyclicAlgebra.isClosedEmbedding_baseChange [T2Space E] {σ : E ≃ₐ[F] E} {l : ℕ}
    (h : IsCyclicAlgebra σ l) (n : ℕ) : IsClosedEmbedding (baseChange F E n) := by
  let : Module.Finite F E := h.1
  let : Nontrivial E := Module.finrank_pos_iff.mp (h.2.1 ▸ h.pos)
  let a : F →ₗ[F] E := Algebra.linearMap F E
  obtain ⟨r, hr⟩ := a.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap F E).injective)
  have hra : Function.LeftInverse r a := DFunLike.congr_fun hr
  have ha : IsClosedEmbedding (algebraMap F E) := by
    refine ⟨hra.isEmbedding (IsModuleTopology.continuous_of_linearMap r)
      (IsModuleTopology.continuous_of_linearMap a), ?_⟩
    have hfixed : range (algebraMap F E) = {e : E | σ e = e} := by
      ext e
      exact ⟨fun ⟨x, hx⟩ => hx ▸ σ.commutes x, h.2.2.2.2 e⟩
    rw [hfixed]
    exact isClosed_eq (IsModuleTopology.continuous_of_linearMap σ.toLinearEquiv.toLinearMap)
      continuous_id
  have hm : IsClosedEmbedding
      (fun M : Matrix (Fin n) (Fin n) F => M.map (algebraMap F E)) :=
    IsClosedEmbedding.piMap fun _ : Fin n => IsClosedEmbedding.piMap fun _ : Fin n => ha
  let : T2Space F := ha.isEmbedding.t2Space
  exact hm.units_map

end Langlands.BaseChange

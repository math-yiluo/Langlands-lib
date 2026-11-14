import Langlands.AllFieldBZ.Representation.Geometric.WeylStatement
import Langlands.AllFieldBZ.Representation.Geometric.WeylUniquenessProof
import Langlands.AllFieldBZ.Representation.Parabolic.RefinementComposition
import Langlands.Representation.Tensor.GLRefinement

/-!
# All-field port of `Langlands.Representation.Tensor.GLRefinement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Tensor.GLRefinement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AllFieldBZ.FiniteTensor
open Langlands.FiniteTensor hiding glRefinementEquiv glRefinementEquiv_symm_tprod glRefinementEquiv_toLinearEquiv glRefinementEquiv_tprod glRefinementLinearEquiv glRefinementLinearEquiv_tprod rankCastLinearEquiv rankCastLinearEquiv_action
open Langlands.GeneralLinear
open Langlands.Geometric hiding PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem
open Langlands.AllFieldBZ.Geometric
universe uF uV

variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)

/-- The carrier equivalence associated to an exact equality of GL ranks. -/
def rankCastLinearEquiv {r s : ℕ} (h : r = s) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear s F.Carrier),
      A ≃ₗ[ℂ] (h.symm ▸ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier)) := by
  letI := T.topology
  cases h
  intro A
  exact LinearEquiv.refl ℂ A

/-- Carrier transport intertwines the actual matrix reindexing by rank equality. -/
theorem rankCastLinearEquiv_action {r s : ℕ} (h : r = s) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear s F.Carrier))
      (g : GeneralLinear r F.Carrier) (v : A),
      rankCastLinearEquiv F T h A
          (A.representation (reindex (R := F.Carrier) (finCongr h) g) v) =
        (h.symm ▸ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier)).representation
          g (rankCastLinearEquiv F T h A v) := by
  let := T.topology
  cases h
  intro A g v
  have hg : reindex (R := F.Carrier) (finCongr (rfl : r = r)) g = g := by
    ext i j
    rfl
  rw [hg]
  rfl

variable {n : ℕ} (B D : BlockShape n) (S : BlockRefinement D)
  (e : ((j : Fin D.length) × Fin (S j).length) ≃ Fin B.length)
  (h : ∀ a, (S a.1).size a.2 = B.size (e a))

/-- Regroup the original tensor and transport every factor's actual carrier. -/
def glRefinementLinearEquiv :
    letI := T.topology
    ∀ σ : ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier),
      PiTensorProduct ℂ (fun i => σ i) ≃ₗ[ℂ]
        PiTensorProduct ℂ (fun j => PiTensorProduct ℂ (fun k =>
          ((h ⟨j,k⟩).symm ▸ σ (e ⟨j,k⟩) :
            SmoothRep.{0,uF,uV} ℂ (GeneralLinear ((S j).size k) F.Carrier)))) := by
  letI := T.topology
  intro σ
  exact (regroupLinearEquiv ℂ (fun i => σ i) e).trans
    (PiTensorProduct.congr (fun j => PiTensorProduct.congr (fun k =>
      rankCastLinearEquiv F T (h ⟨j,k⟩) (σ (e ⟨j,k⟩)))))

theorem glRefinementLinearEquiv_tprod :
    letI := T.topology
    ∀ (σ : ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier))
      (v : ∀ i, σ i),
      glRefinementLinearEquiv F T B D S e h σ (PiTensorProduct.tprod ℂ v) =
        PiTensorProduct.tprod ℂ (fun j => PiTensorProduct.tprod ℂ (fun k =>
          rankCastLinearEquiv F T (h ⟨j,k⟩) (σ (e ⟨j,k⟩)) (v (e ⟨j,k⟩)))) := by
  let := T.topology
  intro σ v
  simp only [glRefinementLinearEquiv, LinearEquiv.trans_apply,
    regroupLinearEquiv_tprod, PiTensorProduct.congr_tprod]

/-- The original external tensor, pulled to the actual refined Levi, is
equivalent to the nested tensor of the exactly rank-transported factors. -/
def glRefinementEquiv :
    letI := T.topology
    ∀ σ : ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier),
      let τ := fun j k => ((h ⟨j,k⟩).symm ▸ σ (e ⟨j,k⟩) :
        SmoothRep.{0,uF,uV} ℂ (GeneralLinear ((S j).size k) F.Carrier))
      Representation.Equiv
        ((external (fun i => (σ i).representation)).comp
          (B.leviRefinementEquiv D S e h F.Carrier).symm.toMonoidHom)
        ((external (fun j => external (fun k => (τ j k).representation))).comp
          (refinedLeviEquiv F.Carrier D S).symm.toMonoidHom) := by
  letI := T.topology
  intro σ
  refine Representation.Equiv.mk (glRefinementLinearEquiv F T B D S e h σ) ?_
  intro m
  ext v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    external_tprod, glRefinementLinearEquiv_tprod]
  congr 1
  funext j
  congr 1
  funext k
  rw [show (B.leviRefinementEquiv D S e h F.Carrier).symm m (e ⟨j,k⟩) =
      reindex (R := F.Carrier) (finCongr (h ⟨j,k⟩))
        ((refinedLeviEquiv F.Carrier D S).symm m j k) from
    B.nestedLeviEquiv_symm_apply D S e h F.Carrier _ j k]
  exact rankCastLinearEquiv_action F T (h ⟨j,k⟩) (σ (e ⟨j,k⟩)) _ _

@[simp] theorem glRefinementEquiv_toLinearEquiv :
    letI := T.topology
    ∀ σ : ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier),
      (glRefinementEquiv F T B D S e h σ).toLinearEquiv =
        glRefinementLinearEquiv F T B D S e h σ := by
  let := T.topology
  intro σ
  rfl

@[simp] theorem glRefinementEquiv_tprod :
    letI := T.topology
    ∀ (σ : ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier))
      (v : ∀ i, σ i),
      glRefinementEquiv F T B D S e h σ (PiTensorProduct.tprod ℂ v) =
        PiTensorProduct.tprod ℂ (fun j => PiTensorProduct.tprod ℂ (fun k =>
          rankCastLinearEquiv F T (h ⟨j,k⟩) (σ (e ⟨j,k⟩)) (v (e ⟨j,k⟩)))) := by
  let := T.topology
  intro σ v
  exact glRefinementLinearEquiv_tprod F T B D S e h σ v

@[simp] theorem glRefinementEquiv_symm_tprod :
    letI := T.topology
    ∀ (σ : ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier))
      (v : ∀ i, σ i),
      (glRefinementEquiv F T B D S e h σ).symm
        (PiTensorProduct.tprod ℂ (fun j => PiTensorProduct.tprod ℂ (fun k =>
          rankCastLinearEquiv F T (h ⟨j,k⟩) (σ (e ⟨j,k⟩)) (v (e ⟨j,k⟩))))) =
        PiTensorProduct.tprod ℂ v := by
  let := T.topology
  intro σ v
  rw [← glRefinementEquiv_tprod F T B D S e h σ v,
    Representation.Equiv.symm_apply_apply]

end Langlands.AllFieldBZ.FiniteTensor

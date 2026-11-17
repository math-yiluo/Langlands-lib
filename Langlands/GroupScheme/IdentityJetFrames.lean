import Langlands.GroupScheme.IdentityJetBasisRestriction
import Langlands.AlgebraicGeometry.Modules.AffineBasisFrames
import Mathlib.LinearAlgebra.Determinant

/-! # Actual jet frames adapted to affine cotangent frames -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.GroupScheme.IdentityJet

open Langlands.Scheme.Modules Algebra.SectionJet.Coordinates
open CoordinateWeights

variable {S : Scheme.{u}} (G : GroupScheme S)
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    {σ : Type u} [Fintype σ] [DecidableEq σ] (U : S.affineOpens)
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U.1) σ ≅
      G.cotangentAtIdentity.over U.1)

attribute [local instance] sectionAlgebra

/-- The actual augmentation-cotangent basis furnished by a specified sheaf
frame on an affine subopen. -/
def cotangentFrameBasis (V : S.affineOpens) (h : V.1 ≤ U.1) :
    Module.Basis σ Γ(S, V) (RingHom.ker (augmentation G V)).Cotangent := by
  let b : Module.Basis σ Γ(S, V) Γ(G.cotangentAtIdentity, V) :=
    localSectionBasis e (Over.mk (homOfLE h : V.1 ⟶ U.1))
  exact b.map (IdentityCotangent.sectionsEquiv G ‹Smooth G.X.hom› V)

omit [DecidableEq σ] in
theorem cotangentFrameBasis_restrict (V : S.affineOpens) (h : V.1 ≤ U.1) (j : σ) :
    IdentityCotangent.restriction G ‹Smooth G.X.hom› h
        (cotangentFrameBasis G U e U le_rfl j) =
      cotangentFrameBasis G U e V h j := by
  change IdentityCotangent.restriction G ‹Smooth G.X.hom› h
      (IdentityCotangent.sectionsEquiv G ‹Smooth G.X.hom› U
        (localSectionBasis e (Over.mk (homOfLE le_rfl)) j)) = _
  rw [IdentityCotangent.sectionsEquiv_restrict]
  exact congrArg (IdentityCotangent.sectionsEquiv G ‹Smooth G.X.hom› V)
    (localSectionBasis_restrict e
      (Over.homMk (homOfLE h) :
        Over.mk (homOfLE h) ⟶ Over.mk (homOfLE (le_refl U.1))) j)

theorem cotangentRestrictionMatrix_frame (V : S.affineOpens) (h : V.1 ≤ U.1) :
    cotangentRestrictionMatrix G h
        (cotangentFrameBasis G U e U le_rfl) (cotangentFrameBasis G U e V h) = 1 := by
  have hv : (fun j => IdentityCotangent.restriction G ‹Smooth G.X.hom› h
      (cotangentFrameBasis G U e U le_rfl j)) =
        (cotangentFrameBasis G U e V h : σ →
          (RingHom.ker (augmentation G V)).Cotangent) :=
    funext (cotangentFrameBasis_restrict G U e V h)
  rw [cotangentRestrictionMatrix, hv, Module.Basis.toMatrix_self]

variable
    (z : σ → Γ(G.X.left, G.X.hom ⁻¹ᵁ U))
    (hz : ∀ i, augmentation G U (z i) = 0)
    (hzb : ∀ i, AugmentedAlgebra.classMap (augmentation G U) (z i) =
      cotangentFrameBasis G U e U le_rfl i)

/-- Actual jet sections in the algebraically adapted basis on the affine chart. -/
def adaptedSectionBasis (n : ℕ) :
    Module.Basis (JetIndex σ n) Γ(S, U) Γ(module G n, U) :=
  (chosenTotalBasis z (cotangentFrameBasis G U e U le_rfl) hz hzb n).map
    (sectionsEquiv G n U).symm

/-- The actual restrictions of the adapted affine jet basis remain a basis on
every affine subopen of the original cotangent frame chart. -/
theorem exists_restricted_adaptedSectionBasis (n : ℕ)
    (V : S.affineOpens) (h : V.1 ≤ U.1) :
    ∃ c : Module.Basis (JetIndex σ n) Γ(S, V) Γ(module G n, V),
      ∀ j, c j = (module G n).presheaf.map (homOfLE h).op
        (adaptedSectionBasis G U e z hz hzb n j) := by
  classical
  obtain ⟨zV, hzV, hzbV⟩ :=
    exists_basis_lifts (ε := augmentation G V) (cotangentFrameBasis G U e V h)
  let b := chosenTotalBasis zV (cotangentFrameBasis G U e V h) hzV hzbV n
  let v : JetIndex σ n → Algebra.SectionJet.Quotient (augmentation G V) n :=
    fun j => restriction G n h
      (chosenTotalBasis z (cotangentFrameBasis G U e U le_rfl) hz hzb n j)
  have hd : (b.toMatrix v).det = 1 := by
    change ((totalBasis zV (cotangentFrameBasis G U e V h) hzV hzbV
      (Algebra.SectionJet.linearSection (augmentation G V))
      (Algebra.SectionJet.truncate_linearSection (augmentation G V)) n).toMatrix
        (fun j => restriction G n h
          (totalBasis z (cotangentFrameBasis G U e U le_rfl) hz hzb
            (Algebra.SectionJet.linearSection (augmentation G U))
            (Algebra.SectionJet.truncate_linearSection (augmentation G U)) n j))).det = 1
    rw [totalBasis_restrictionMatrix_det G h
      (cotangentFrameBasis G U e U le_rfl) (cotangentFrameBasis G U e V h)
      z hz hzb zV hzV hzbV, cotangentRestrictionMatrix_frame, Matrix.det_one, one_pow]
  have hb : LinearIndependent Γ(S, V) v ∧ Submodule.span Γ(S, V) (Set.range v) = ⊤ :=
    b.is_basis_iff_det.mpr (by
      change IsUnit (b.toMatrix v).det
      rw [hd]
      exact isUnit_one)
  let c := Module.Basis.mk hb.1 hb.2.ge
  refine ⟨c.map (sectionsEquiv G n V).symm, fun j => ?_⟩
  apply (sectionsEquiv G n V).injective
  change sectionsEquiv G n V ((sectionsEquiv G n V).symm (c j)) = _
  rw [LinearEquiv.apply_symm_apply]
  rw [show c j = v j from congrFun (Module.Basis.coe_mk hb.1 hb.2.ge) j]
  calc
    v j = restriction G n h
        (sectionsEquiv G n U (adaptedSectionBasis G U e z hz hzb n j)) := by
      rw [adaptedSectionBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply]
    _ = _ := sectionsEquiv_restrict G n h
      (adaptedSectionBasis G U e z hz hzb n j)

/-- The actual free jet frame on the original affine cotangent chart. -/
def adaptedFrame (n : ℕ) :
    SheafOfModules.free (R := S.ringCatSheaf.over U.1) (JetIndex σ n) ≅
      (module G n).over U.1 :=
  affineBasisFrame (module G n) U (JetIndex σ n)
    (adaptedSectionBasis G U e z hz hzb n)
    (fun W hW => exists_restricted_adaptedSectionBasis G U e z hz hzb n
      ⟨W.left, hW⟩ W.hom.le)

/-- The frame's basis on every smaller open consists of actual restrictions of
the originally specified affine adapted basis. -/
theorem adaptedFrame_basis (n : ℕ) (W : Over U.1) (j : JetIndex σ n) :
    localSectionBasis (adaptedFrame G U e z hz hzb n) W j =
      (module G n).presheaf.map W.hom.op
        (adaptedSectionBasis G U e z hz hzb n j) :=
  affineBasisFrame_basis _ _ _ _ _ W j

end Langlands.GroupScheme.IdentityJet

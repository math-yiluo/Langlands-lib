import Langlands.GroupScheme.Reductive.PinningBaseChange
import Langlands.GroupScheme.Reductive.FieldExtensionProof

/-! # Scalar extension of split pinnings along arbitrary field extensions -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.SplitPinning

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (p : SplitPinning G)

local notation "bc" => algebraBaseMap k K
local notation "GK" => Functor.obj (GroupScheme.baseChange bc) G

local instance pinningFieldBaseChangeAffine : IsAffineHom (GK).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom bc)
  infer_instance

/-- The actual supplied split pinning extends along every extension of the base field. -/
def baseChangeField : SplitPinning GK := by
  have := p.isConnectedReductive.smooth
  exact {
    isConnectedReductive := connectedReductiveFieldExtensionStatement k K G p.isConnectedReductive
    torus := (CommGroupScheme.baseChange bc).obj p.torus
    inclusion := (GroupScheme.baseChange bc).map p.inclusion
    isSplitTorus := p.isSplitTorus.baseChange bc
    isMaximalTorus := (maximalTorusBaseChange k K G p.torus p.inclusion
      p.isMaximalTorus.1 p.isMaximalTorus.2.1).mp p.isMaximalTorus
    rootIndex := p.rootIndex
    rootDatum := p.baseChangeRootDatum (F := K)
    isRootDatum := p.isRootDatum.baseChange (K := K) G p.torus p.isSplitTorus p.inclusion
    isReduced := p.isReduced_baseChangeRootDatum (F := K)
    base := p.baseChangeBase (F := K)
    pinning := { trivialization := fun a =>
      (RootPinning.baseChangeTrivialization p.pinning p.isSplitTorus
        ((p.baseChangeSimpleEquiv (F := K)).symm a)) } }

@[simp]
theorem baseChangeField_torus :
    (p.baseChangeField (K := K)).torus = (CommGroupScheme.baseChange bc).obj p.torus := rfl

@[simp]
theorem baseChangeField_inclusion :
    (p.baseChangeField (K := K)).inclusion = (GroupScheme.baseChange bc).map p.inclusion := rfl

/-- The extension retains the actual scalar extension of each chosen root vector. -/
theorem baseChangeField_rootVector (a : p.base.support) :
    haveI := p.isConnectedReductive.smooth
    (p.baseChangeField (K := K)).pinning.rootVector (p.baseChangeSimpleEquiv (F := K) a) =
      Lie.schemeScalarExtension (K := K) G (1 ⊗ₜ[k] p.pinning.rootVector a) := by
  have := p.isConnectedReductive.smooth
  change (RootPinning.baseChangeTrivialization (F := K) p.pinning p.isSplitTorus
    ((p.baseChangeSimpleEquiv (F := K)).symm (p.baseChangeSimpleEquiv (F := K) a)) 1).val = _
  rw [Equiv.symm_apply_apply, RootPinning.baseChangeTrivialization_one]
  rfl

/-- Over algebraic extensions this construction agrees with the published algebraic pullback. -/
theorem baseChangeField_eq_baseChange [Algebra.IsAlgebraic k K] :
    p.baseChangeField (K := K) = p.baseChange (F := K) := rfl

end Langlands.GroupScheme.SplitPinning

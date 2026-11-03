import Langlands.AlgebraicGeometry.ProjectiveBundle.FrameAtlas
import Langlands.AlgebraicGeometry.Modules.CoherentLineBundle
import Langlands.AlgebraicGeometry.Picard.LineBundleTensor

/-! # Genuine frames after tensoring with a line bundle -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Picard

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

variable {S : Scheme.{u}} {M N : S.Modules} {n : ℕ}

namespace LocalFrame

/-- Transport an actual frame along a sheaf isomorphism on the open subscheme. -/
def ofRestrictIso {U : S.Opens} (e : LocalFrame M n U)
    (f : M.restrict U.ι ≅ N.restrict U.ι) : LocalFrame N n U :=
  e ≪≫ (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app M ≪≫ f ≪≫
      ((Scheme.Modules.overFunctorEquiv U).app N).symm)

/-- A frame and a genuine line trivialization give a frame of the sheaf tensor. -/
def tensor {U : S.Opens} (e : LocalFrame M n U)
    (t : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    LocalFrame (tensorObj M N) n U :=
  e.ofRestrictIso (Modules.tensorRestrictionTrivialization M N U t).symm

end LocalFrame

/-- Genuine frames near every point imply the prescribed fixed local rank. -/
lemma isLocallyFreeOfRank_of_localFrames
    (h : ∀ x : S, ∃ U : S.Opens, x ∈ U ∧ Nonempty (LocalFrame M n U)) :
    IsLocallyFreeOfRank M (n + 1) := by
  classical
  choose U hx e using h
  let q : SheafOfModules.LocalGeneratorsData.{u} M :=
    { I := S
      X := U
      coversTop := (_root_.Opens.coversTop_iff S U).mpr (by
        apply top_le_iff.mp
        intro x _
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩)
      generators x :=
        (SheafOfModules.free.generatingSections
          (R := S.ringCatSheaf.over (U x)) (ULift.{u} (Fin (n + 1)))).ofEpi (e x).some.hom }
  have hq : q.IsLocallyFreeData := by
    constructor
    intro x
    change IsIso ((SheafOfModules.free.generatingSections
      (R := S.ringCatSheaf.over (U x)) (ULift.{u} (Fin (n + 1)))).ofEpi (e x).some.hom).π
    rw [SheafOfModules.GeneratingSections.ofEpi_π]
    infer_instance
  exact ⟨q, hq, fun _ => ⟨Equiv.ulift⟩⟩

namespace TensorFrames

variable (M N n)

/-- Opens that carry a genuine frame of the first factor and trivialization of the second. -/
def opens : Set S.Opens :=
  { U | Nonempty (LocalFrame M n U) ∧
    Nonempty (N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) }

variable {M N n}

/-- Joint frames and trivializations remain available on every smaller open. -/
lemma opens_of_le {U V : S.Opens} (hV : V ∈ opens M N n) (h : U ≤ V) :
    U ∈ opens M N n := by
  exact ⟨⟨hV.1.some.restrict h⟩, ⟨
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app N ≪≫
      pullbackTrivializationOfLE h N hV.2.some⟩⟩

/-- A locally free module and a line bundle admit joint frames near every point. -/
lemma exists_open (hM : IsLocallyFreeOfRank M (n + 1))
    (hN : IsLocallyFreeRankOne N) (x : S) :
    ∃ U : S.Opens, x ∈ U ∧ U ∈ opens M N n := by
  obtain ⟨U, hxU⟩ := exists_frameOpen M n hM x
  obtain ⟨V, hxV, ⟨t⟩⟩ := hN x
  refine ⟨U.val ⊓ V, ⟨hxU, hxV⟩, ⟨⟨(frame M n U).restrict inf_le_left⟩, ⟨?_⟩⟩⟩
  exact (Scheme.Modules.restrictFunctorIsoPullback (U.val ⊓ V).ι).app N ≪≫
    pullbackTrivializationOfLE inf_le_right N t

/-- The joint frame and line-trivialization opens form a topological basis. -/
lemma isBasis (hM : IsLocallyFreeOfRank M (n + 1)) (hN : IsLocallyFreeRankOne N) :
    TopologicalSpace.Opens.IsBasis (opens M N n) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨V, hxV, hV⟩ := exists_open hM hN x
  exact ⟨U ⊓ V, opens_of_le hV inf_le_right, ⟨hx, hxV⟩, inf_le_left⟩

/-- The source module has an actual frame atlas on this joint basis. -/
def sourceAtlas (hM : IsLocallyFreeOfRank M (n + 1)) (hN : IsLocallyFreeRankOne N) :
    FrameAtlas M n where
  opens := opens M N n
  isBasis := isBasis hM hN
  frame U := U.property.1.some

/-- Tensor frames give an actual frame atlas on the same basis. -/
def tensorAtlas (hM : IsLocallyFreeOfRank M (n + 1)) (hN : IsLocallyFreeRankOne N) :
    FrameAtlas (tensorObj M N) n where
  opens := opens M N n
  isBasis := isBasis hM hN
  frame U := U.property.1.some.tensor U.property.2.some

/-- Tensoring with a line bundle preserves the specified fixed local rank. -/
lemma isLocallyFreeOfRank_tensor (hM : IsLocallyFreeOfRank M (n + 1))
    (hN : IsLocallyFreeRankOne N) : IsLocallyFreeOfRank (tensorObj M N) (n + 1) := by
  apply isLocallyFreeOfRank_of_localFrames
  intro x
  obtain ⟨U, hx, hU⟩ := exists_open hM hN x
  exact ⟨U, hx, ⟨hU.1.some.tensor hU.2.some⟩⟩

end TensorFrames

end Langlands.AlgebraicGeometry.ProjectiveBundle

import Langlands.AlgebraicGeometry.Picard.LineBundleTensor
import Langlands.AlgebraicGeometry.Modules.SectionLocus
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Common affine trivializing covers for two line bundles -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Langlands.Scheme.Modules Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Picard.LineBundle

variable {X : Scheme.{u}}

/-- A point-indexed affine open cover with actual trivializations of two bundles. -/
structure CommonAffineTrivializingCover (L M : LineBundle X) where
  opens : X → X.Opens
  affine : ∀ x, IsAffineOpen (opens x)
  covers : iSup opens = ⊤
  fstTrivialization : ∀ x, (Scheme.Modules.pullback (opens x).ι).obj L.obj ≅
    structureModule (opens x).toScheme
  sndTrivialization : ∀ x, (Scheme.Modules.pullback (opens x).ι).obj M.obj ≅
    structureModule (opens x).toScheme

/-- Choose an affine refinement of the intersection of the two local frames at
each point. The resulting opens cover the whole scheme. -/
def commonAffineTrivializingCover (L M : LineBundle X) :
    CommonAffineTrivializingCover L M := by
  classical
  choose U hU hxU hle using fun x : X ↦
    (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
      (show x ∈ L.trivializingOpen x ⊓ M.trivializingOpen x from
        ⟨L.mem_trivializingOpen x, M.mem_trivializingOpen x⟩)
  refine
    { opens := U
      affine := hU
      covers := ?_
      fstTrivialization := fun x ↦
        pullbackTrivializationOfLE (le_trans (hle x) inf_le_left)
          L.obj (L.localTrivialization x)
      sndTrivialization := fun x ↦
        pullbackTrivializationOfLE (le_trans (hle x) inf_le_right)
          M.obj (M.localTrivialization x) }
  apply le_antisymm le_top
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, hxU x⟩

/-- Two line bundles on an arbitrary scheme have a common affine trivializing
open cover indexed in the same universe as the scheme's points. -/
theorem exists_commonAffineTrivializingCover (L M : LineBundle X) :
    ∃ (ι : Type u) (U : ι → X.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ iSup U = ⊤ ∧
        ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.obj ≅
          structureModule (U i).toScheme) ∧
          Nonempty ((Scheme.Modules.pullback (U i).ι).obj M.obj ≅
            structureModule (U i).toScheme) := by
  let D := commonAffineTrivializingCover L M
  exact ⟨X, D.opens, D.affine, D.covers,
    fun i ↦ ⟨⟨D.fstTrivialization i⟩, ⟨D.sndTrivialization i⟩⟩⟩

end Langlands.AlgebraicGeometry.Picard.LineBundle

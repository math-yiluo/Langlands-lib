import Langlands.AlgebraicGeometry.Picard.FieldBaseChangeAmpleReflectionStatement
import Langlands.AlgebraicGeometry.Picard.SupportedPullbackPowerSections
import Langlands.AlgebraicGeometry.Picard.ClosedComplementSectionsBaseChange
import Langlands.AlgebraicGeometry.Modules.SupportedSectionCoefficients

/-! # Reflection of ampleness of a fixed line bundle under field extension -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections

namespace Langlands.AlgebraicGeometry.Picard

open FieldAmpleReflection

/-- Ampleness of the actual pullback along an arbitrary morphism of field spectra
reflects to the same specified line bundle. -/
theorem fieldBaseChangeAmpleReflection : FieldBaseChangeAmpleReflectionStatement.{u} := by
  intro k K _ _ b X p L hL
  have htop := compactSpace_and_quasiSeparatedSpace k K b X p L hL
  refine ⟨htop.1, fun x => ?_⟩
  obtain ⟨U, hU, hx, _⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨y, hy, r, hr, t, hyt, htz⟩ :=
    exists_vanishing_upstairs_section k K b X p L hL U x hx
  let M : LineBundle X :=
    ⟨tensorPow L.obj r, tensorPow_isLocallyFreeRankOne X L r⟩
  let q := pullback.fst p b
  let p' := pullback.snd p b
  let i := closedComplementι U
  let i' := pullback.snd i q
  let qZ := pullback.fst i q
  let w := (fieldProjection_isPullback k K b X p).w
  let sq : qZ ≫ i = i' ≫ q := pullback.condition
  let : IsIso (scalarSectionsBaseChangeMap (Spec.preimage b) p p' q w M.obj) := by
    change IsIso (sectionsIsoOfAmpleBaseChange k K b X p L hL M).hom
    infer_instance
  let : IsIso (scalarSectionsBaseChangeMap (Spec.preimage b) (i ≫ p) (i' ≫ p')
      qZ (square_restrict_comm (Spec.preimage b) p p' q w i i' qZ sq)
      ((Scheme.Modules.pullback i).obj M.obj)) := by
    change IsIso (closedComplementSectionsIsoOfAmpleBaseChange k K b X p L hL U M).hom
    infer_instance
  obtain ⟨s, hsz, hxs⟩ :=
    exists_vanishing_coefficient_generating (Spec.preimage b) p p' q w
      i i' qZ sq M t htz y hyt
  have hle : L.sectionOpen s ≤ U :=
    trivializationOpen_le_of_closedComplement_vanishing U M s hsz
  refine ⟨r, hr, s, ?_, isAffineOpen_sectionOpen_of_le L s U hU hle⟩
  change x ∈ trivializationOpen M.obj s
  change pullback.fst p b y ∈ trivializationOpen M.obj s at hxs
  rwa [hy] at hxs

end Langlands.AlgebraicGeometry.Picard

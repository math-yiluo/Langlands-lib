import Langlands.GroupScheme.Reductive.AffinePinnedTransitions
import Langlands.GroupScheme.GroupLikeActionAffine
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.AutomorphicActionPointIso

/-! # Innerness of corrected transitions between pinned affine charts -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- A full-centre quotient remains such a quotient after changing its source
by an actual group-scheme isomorphism. -/
theorem RelativeRoot.IsFppfQuotient.comapIso_center {S : Scheme.{u}}
    {G H Q : GroupScheme S} {q : G ⟶ Q}
    (hq : RelativeRoot.IsFppfQuotient (center G) q) (e : G ≅ H) :
    RelativeRoot.IsFppfQuotient (center H) (e.inv ≫ q) := by
  have hcenter : (center G).comap e.inv = center H := by
    ext T x
    exact mem_center_comp_iso_iff e.symm x
  simpa only [hcenter] using hq.comapIso e

namespace AutomorphicAction

variable {S : Scheme.{u}} {A G H : GroupScheme S}
    (a : AutomorphicAction A G)

/-- Transport of the acted-on group preserves the conjugation restriction
along the correspondingly transported quotient map. -/
theorem transportTarget_restrict_conjugation {p : G ⟶ A}
    (hp : a.restrict p = conjugation (𝟙 G)) (e : H ≅ G) :
    (a.transportTarget e).restrict (e.hom ≫ p) = conjugation (𝟙 H) := by
  apply ext_act
  intro T h g
  rw [restrict_act, transportTarget_act]
  change a.act ((h ≫ e.hom.hom.hom) ≫ p.hom.hom)
    (g ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = _
  rw [← restrict_act, hp]
  simp only [conjugation_act, Grp.id_hom_hom, Category.comp_id,
    MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, ← Grp.comp_hom_hom,
    e.hom_inv_id]

/-- Evaluating a transported action conjugates its actual base-point automorphism. -/
theorem transportTarget_basePointIso (e : H ≅ G)
    (x : Over.mk (𝟙 S) ⟶ A.X) :
    (a.transportTarget e).basePointIso x =
      e ≪≫ a.basePointIso x ≪≫ e.symm := by
  apply Iso.ext
  apply hom_ext_points
  intro T g
  simp only [Iso.trans_hom, Iso.symm_hom, Grp.comp_hom_hom,
    ← Category.assoc, comp_basePointIso_hom, transportTarget_act]
  rw [a.naturality, A.constantPoint_naturality]

end AutomorphicAction

namespace AffinePinnedChart

open Descent

variable {S T : Scheme.{u}} {G : GroupScheme S}

/-- The inverse corrected chart transition is the action of an actual
adjoint point on the common test scheme. -/
theorem exists_basePointIso_transition_symm (P : RelativePinnedComparison.{u})
    (C D : AffinePinnedChart G)
    (f : T ⟶ C.model.base) (g : T ⟶ D.model.base) (k : T ⟶ S)
    (hf : f ≫ C.map = k) (hg : g ≫ D.map = k)
    (Q : GroupScheme T) (q : (baseChange k).obj G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (center ((baseChange k).obj G)) q)
    (a : AutomorphicAction Q ((baseChange k).obj G))
    (ha : a.restrict q = AutomorphicAction.conjugation (𝟙 _)) :
    ∃ x : Over.mk (𝟙 T) ⟶ Q.X,
      a.basePointIso x = (C.transition P D f g k hf hg).symm := by
  let e := C.identify f k hf
  let a' := a.transportTarget e.symm
  have hq' := hq.comapIso_center e
  have ha' := a.transportTarget_restrict_conjugation ha e.symm
  obtain ⟨x, hx⟩ := P.inner C.model D.model T f g
    (C.comparison D f g k hf hg) Q (e.inv ≫ q) hq' a' ha'
  refine ⟨x, ?_⟩
  have he := congrArg (fun E => e ≪≫ E ≪≫ e.symm) hx
  rw [a.transportTarget_basePointIso e.symm x] at he
  apply Iso.ext
  simpa [transition, comparison, correctedComparison, e] using congrArg Iso.hom he

end AffinePinnedChart

end Langlands.GroupScheme

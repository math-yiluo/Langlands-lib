import Langlands.GroupScheme.RelativeLevi.MultiplicationDescent
import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalDescent

/-! # Étale base change of relative Levi subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}} {L P : GroupScheme S} {l : L ⟶ P}

/-- Étale base change preserves a relative Levi inclusion in an affine group. -/
theorem IsRelativeLeviSubgroup.baseChange_etale
    (hl : IsRelativeLeviSubgroup l) [IsAffineHom P.X.hom]
    (b : S' ⟶ S) [Etale b] :
    IsRelativeLeviSubgroup ((GroupScheme.baseChange b).map l) := by
  let : Smooth L.X.hom := hl.smooth
  obtain ⟨U, r, hr, hmul⟩ := hl.exists_unipotentRadical
  let : IsIso (subgroupMultiplication l r) := hmul
  refine ⟨hl.isClosedSubgroup.baseChange b, ?_, ?_⟩
  · change Smooth (CategoryTheory.Limits.pullback.snd L.X.hom b)
    infer_instance
  · exact ⟨(GroupScheme.baseChange b).obj U, (GroupScheme.baseChange b).map r,
      hr.baseChange_etale b,
      RelativeLevi.subgroupMultiplication_isIso_baseChange b l r⟩

namespace RelativeLevi

/-- The actual pulled-back Levi source and inclusion with their full certificate. -/
def etaleBaseChangeLevi
    (hl : IsRelativeLeviSubgroup l) [IsAffineHom P.X.hom]
    (b : S' ⟶ S) [Etale b] :
    Σ M : GroupScheme S',
      {j : M ⟶ (GroupScheme.baseChange b).obj P // IsRelativeLeviSubgroup j} :=
  ⟨(GroupScheme.baseChange b).obj L, (GroupScheme.baseChange b).map l,
    hl.baseChange_etale b⟩

@[simp] theorem etaleBaseChangeLevi_group
    (hl : IsRelativeLeviSubgroup l) [IsAffineHom P.X.hom]
    (b : S' ⟶ S) [Etale b] :
    (etaleBaseChangeLevi hl b).1 = (GroupScheme.baseChange b).obj L := rfl

end RelativeLevi

end Langlands.GroupScheme

import Langlands.GroupScheme.AutomorphicAction.FppfCenterQuotient
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Inner actions of supplied full-centre quotients over arbitrary bases -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot.IsFppfQuotient

variable {S : Scheme.{u}} {G A : GroupScheme S} {q : G ⟶ A}
    (hq : RelativeRoot.IsFppfQuotient (center G) q)

include hq in
/-- The full-centre kernel acts trivially by conjugation, on every relative test. -/
theorem conjugation_kernelActsTrivially :
    (AutomorphicAction.conjugation (𝟙 G)).KernelActsTrivially q := by
  intro T k g
  have hz : k ≫ (kernelι q).hom.hom ∈ (center G).carrier T := by
    rw [← hq.2.2.2]
    exact ⟨k, rfl⟩
  simp only [AutomorphicAction.restrict_act, AutomorphicAction.conjugation_act,
    Grp.id_hom_hom, Category.comp_id]
  rw [(commute_of_mem_center hz g).eq, mul_inv_cancel_right]

variable [IsAffineHom G.X.hom] [IsSeparated A.X.hom]

private theorem quotient_isAffineHom : IsAffineHom q.hom.hom.left := by
  have : IsAffineHom (q.hom.hom.left ≫ A.X.hom) := by
    simpa only [Over.w] using (inferInstance : IsAffineHom G.X.hom)
  exact IsAffineHom.of_comp _ A.X.hom

/-- The actual inner action of a supplied full-centre fppf quotient. The source is
affine over the base, and the quotient is separated over the base. -/
def innerAction : AutomorphicAction A G := by
  letI := quotient_isAffineHom (q := q)
  letI := hq.1
  letI := hq.2.1
  exact (AutomorphicAction.conjugation (𝟙 G)).quotientAction q
    hq.conjugation_kernelActsTrivially

/-- The descended action restricts to conjugation as a bundled action. -/
@[simp]
theorem innerAction_restrict :
    hq.innerAction.restrict q = AutomorphicAction.conjugation (𝟙 G) := by
  let := quotient_isAffineHom (q := q)
  let := hq.1
  let := hq.2.1
  exact AutomorphicAction.quotientAction_restrict _ _ _

/-- On every lifted quotient point the action is conjugation. -/
theorem innerAction_act_lift {T : Over S} (h g : T ⟶ G.X) :
    hq.innerAction.act (h ≫ q.hom.hom) g = h * g * h⁻¹ :=
  AutomorphicAction.act_lift_of_restrict_eq_conjugation
    hq.innerAction hq.innerAction_restrict h g

/-- The full-centre quotient action is faithful on all relative tests. -/
theorem innerAction_isFaithful : hq.innerAction.IsFaithful :=
  AutomorphicAction.isFaithful_of_isFppfQuotient_center
    hq hq.innerAction hq.innerAction_restrict

/-- Its restriction uniquely determines the quotient action. -/
theorem innerAction_unique (a : AutomorphicAction A G)
    (ha : a.restrict q = AutomorphicAction.conjugation (𝟙 G)) :
    a = hq.innerAction := by
  let := quotient_isAffineHom (q := q)
  let := hq.1
  let := hq.2.1
  exact AutomorphicAction.quotientAction_unique _ _ _ a ha

include hq in
/-- A supplied quotient has exactly one compatible inner action. -/
theorem existsUnique_innerAction :
    ∃! a : AutomorphicAction A G,
      a.restrict q = AutomorphicAction.conjugation (𝟙 G) := by
  exact ⟨hq.innerAction, hq.innerAction_restrict,
    fun a ha => hq.innerAction_unique a ha⟩

end Langlands.GroupScheme.RelativeRoot.IsFppfQuotient

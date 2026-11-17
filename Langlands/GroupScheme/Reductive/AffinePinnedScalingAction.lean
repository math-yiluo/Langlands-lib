import Langlands.GroupScheme.Reductive.AffinePinnedModel
import Langlands.GroupScheme.Reductive.GlobalRootAnnihilatorCentrality
import Langlands.GroupScheme.Reductive.RelativeRootScalingTorus
import Langlands.GroupScheme.ActionDescent
import Langlands.GroupScheme.AutomorphicActionPointIso

/-! # Simple-root scaling actions for affine pinned split reductive groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

variable (M : AffinePinnedModel.{u})

/-- The coordinate torus with one coordinate for every chosen simple root. -/
def rootScalingTorus : CommGroupScheme M.base :=
  splitTorus.commGroupScheme M.base M.basis.support

/-- The projection evaluates all chosen simple-root exponent characters. -/
def rootScalingProjection : splitTorus M.base M.coordinates ⟶ M.rootScalingTorus.toGrp :=
  splitTorus.exponentTorusProjection (CommRingCat.of M.ring)
    (fun a : M.basis.support => M.rootDatum.root a)

/-- Each coordinate of the projection is its specified simple-root monomial. -/
theorem rootScalingProjection_points (Z : Over M.base)
    (t : Z ⟶ (splitTorus M.base M.coordinates).X) (a : M.basis.support) :
    splitTorus.pointsEquiv M.basis.support Z
        (t ≫ M.rootScalingProjection.hom.hom) a =
      ∏ j, splitTorus.pointsEquiv M.coordinates Z t j ^ M.rootDatum.root a j :=
  splitTorus.exponentTorusProjection_points (CommRingCat.of M.ring) _ Z t a

/-- The projection is fppf over every commutative ring, including the zero ring. -/
theorem rootScalingProjection_fppf :
    Flat M.rootScalingProjection.hom.hom.left ∧
    Surjective M.rootScalingProjection.hom.hom.left ∧
    LocallyOfFinitePresentation M.rootScalingProjection.hom.hom.left :=
  splitTorus.exponentTorusProjection_fppf (CommRingCat.of M.ring) _
    M.basis.linearIndepOn_root.linearIndependent

/-- A point in the projection kernel annihilates every simple root. -/
theorem rootScalingProjection_simpleRootCharactersOne
    {Z : Over M.base} (x : Z ⟶ (kernel M.rootScalingProjection).X) :
    SimpleRootCharactersOne M.basis (x ≫ (kernelι M.rootScalingProjection).hom.hom) := by
  intro a ha
  rw [Corepresented.charValue_exponentCharacter]
  have hk : (x ≫ (kernelι M.rootScalingProjection).hom.hom) ≫
      M.rootScalingProjection.hom.hom = 1 :=
    (kernelPointsEquiv M.rootScalingProjection Z x).property
  have h := congrArg (fun z => splitTorus.pointsEquiv M.basis.support Z z ⟨a, ha⟩)
    hk
  rw [M.rootScalingProjection_points] at h
  change (↑(∏ j, splitTorus.pointsEquiv M.coordinates Z
    (x ≫ (kernelι M.rootScalingProjection).hom.hom) j ^ M.rootDatum.root a j) :
      Γ(Z.left, ⊤)) = 1
  simpa only [map_one, Pi.one_apply, Units.val_one] using congrArg Units.val h

/-- The full scheme-theoretic kernel acts trivially by conjugation. -/
theorem rootScalingProjection_kernel_trivial :
    (AutomorphicAction.conjugation M.inclusion).KernelActsTrivially
      M.rootScalingProjection := by
  intro Z x g
  rw [AutomorphicAction.restrict_act, AutomorphicAction.conjugation_act]
  have hc := mem_center_of_simpleRootCharacters_one M.reductive M.maximal
    M.fibrewiseRootDatum M.basis (x ≫ (kernelι M.rootScalingProjection).hom.hom)
    (M.rootScalingProjection_simpleRootCharactersOne x)
  have he := hc Z (𝟙 Z) g
  simp only [Category.id_comp, Category.assoc] at he
  simp only [Category.assoc]
  rw [he, mul_inv_cancel_right]

private theorem isSplit_rootScalingTorus : IsSplitTorus M.rootScalingTorus.toGrp :=
  ⟨M.basis.support, inferInstance, ⟨Iso.refl _⟩⟩

/-- Conjugation descends to the simple-root coordinate torus, so its base
points act even when they do not lift to base points of the original torus. -/
def rootScalingAction : AutomorphicAction M.rootScalingTorus.toGrp M.group := by
  letI := (show IsSplitTorus (splitTorus M.base M.coordinates) from
    ⟨M.coordinates, inferInstance, ⟨Iso.refl _⟩⟩).isAffineHom
  letI := M.isSplit_rootScalingTorus.isAffineHom
  letI := isAffine_of_isAffineHom (splitTorus M.base M.coordinates).X.hom
  letI := isAffine_of_isAffineHom M.rootScalingTorus.X.hom
  letI := M.rootScalingProjection_fppf.1
  letI := M.rootScalingProjection_fppf.2.1
  haveI : IsAffineHom M.rootScalingProjection.hom.hom.left := inferInstance
  exact AutomorphicAction.quotientAction (AutomorphicAction.conjugation M.inclusion)
    M.rootScalingProjection M.rootScalingProjection_kernel_trivial

/-- Restriction of the descended action is the original torus conjugation. -/
theorem rootScalingAction_restrict :
    M.rootScalingAction.restrict M.rootScalingProjection =
      AutomorphicAction.conjugation M.inclusion := by
  let := (show IsSplitTorus (splitTorus M.base M.coordinates) from
    ⟨M.coordinates, inferInstance, ⟨Iso.refl _⟩⟩).isAffineHom
  let := M.isSplit_rootScalingTorus.isAffineHom
  let := isAffine_of_isAffineHom (splitTorus M.base M.coordinates).X.hom
  let := isAffine_of_isAffineHom M.rootScalingTorus.X.hom
  let := M.rootScalingProjection_fppf.1
  let := M.rootScalingProjection_fppf.2.1
  unfold rootScalingAction
  exact AutomorphicAction.quotientAction_restrict
    (AutomorphicAction.conjugation M.inclusion) M.rootScalingProjection
    M.rootScalingProjection_kernel_trivial

/-- The descended action fixes the supplied torus on every test scheme. -/
theorem rootScalingAction_act_torus {Z : Over M.base}
    (x : Z ⟶ M.rootScalingTorus.X)
    (t : Z ⟶ (splitTorus M.base M.coordinates).X) :
    M.rootScalingAction.act x (t ≫ M.inclusion.hom.hom) = t ≫ M.inclusion.hom.hom := by
  let := (show IsSplitTorus (splitTorus M.base M.coordinates) from
    ⟨M.coordinates, inferInstance, ⟨Iso.refl _⟩⟩).isAffineHom
  let := M.isSplit_rootScalingTorus.isAffineHom
  let := isAffine_of_isAffineHom (splitTorus M.base M.coordinates).X.hom
  let := isAffine_of_isAffineHom M.rootScalingTorus.X.hom
  let := M.rootScalingProjection_fppf.1
  let := M.rootScalingProjection_fppf.2.1
  apply AutomorphicAction.hom_ext_of_local_quotient_lift M.rootScalingProjection x
  intro V b h hb
  rw [M.rootScalingAction.naturality, hb]
  rw [← AutomorphicAction.restrict_act, M.rootScalingAction_restrict,
    AutomorphicAction.conjugation_act]
  simp only [← Category.assoc]
  apply mul_inv_eq_iff_eq_mul.mpr
  rw [← MonObj.mul_comp, ← MonObj.mul_comp, mul_comm]

/-- A tuple of simple-root units is an actual base point of the quotient torus. -/
def rootScalingPoint (c : M.basis.support → M.ringˣ) :
    Over.mk (𝟙 M.base) ⟶ M.rootScalingTorus.X :=
  (splitTorus.affinePointsEquiv M.basis.support (𝟙 M.base)).symm c

/-- Evaluate the descended action at prescribed simple-root units. -/
def rootScalingIso (c : M.basis.support → M.ringˣ) : M.group ≅ M.group :=
  M.rootScalingAction.basePointIso (M.rootScalingPoint c)

/-- Every resulting automorphism restricts to the identity on the chosen torus. -/
theorem rootScalingIso_inclusion (c : M.basis.support → M.ringˣ) :
    M.inclusion ≫ (M.rootScalingIso c).hom = M.inclusion := by
  apply hom_ext_points
  intro Z t
  rw [Grp.comp_hom_hom, ← Category.assoc]
  change (t ≫ M.inclusion.hom.hom) ≫
    (M.rootScalingAction.basePointIso (M.rootScalingPoint c)).hom.hom.hom = _
  rw [AutomorphicAction.comp_basePointIso_hom, M.rootScalingAction_act_torus]

end Langlands.GroupScheme.AffinePinnedModel

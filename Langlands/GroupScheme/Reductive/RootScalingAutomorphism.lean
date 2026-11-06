import Langlands.GroupScheme.Reductive.RootScalingTorus
import Langlands.GroupScheme.AutomorphicActionPointIso
import Langlands.GroupScheme.Rational.TangentImage
import Langlands.GroupScheme.Lie.ElementCentralizer

/-! # Automorphisms with prescribed simple-root scalings -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

/-- The descended action fixes the supplied torus on every test scheme. -/
theorem rootScalingAction_act_torus {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ p.rootScalingTorus.X) (t : T ⟶ p.torus.X) :
    p.rootScalingAction.act x (t ≫ p.inclusion.hom.hom) = t ≫ p.inclusion.hom.hom := by
  let := p.isSplitTorus.isAffineHom
  let := p.rootScalingTorus_isSplit.isAffineHom
  let := isAffine_of_isAffineHom p.torus.X.hom
  let := isAffine_of_isAffineHom p.rootScalingTorus.X.hom
  let := p.rootScalingProjection_fppf.1
  let := p.rootScalingProjection_fppf.2.1
  apply AutomorphicAction.hom_ext_of_local_quotient_lift
    (CommGroupScheme.groupHom p.rootScalingProjection) x
  intro V b h hb
  rw [p.rootScalingAction.naturality, hb]
  rw [← AutomorphicAction.restrict_act, p.rootScalingAction_restrict,
    AutomorphicAction.conjugation_act]
  simp only [← Category.assoc]
  apply mul_inv_eq_iff_eq_mul.mpr
  rw [← MonObj.mul_comp, ← MonObj.mul_comp, mul_comm]

/-- The chosen simple-root vector has its coordinate weight under the quotient action. -/
theorem rootVector_mem_rootScalingAction_weight (a : p.base.support) :
    p.pinning.rootVector a ∈ RelativeRoot.actionWeightSpace p.rootScalingAction
      (splitTorus.proj _ p.base.support a) := by
  let := p.isConnectedReductive.smooth
  have hw := RelativeRoot.actionWeightSpace_restrict_eq_of_injective
    p.rootScalingAction p.rootScalingTorus_isSplit p.isSplitTorus
    p.rootScalingProjection
    (by
      intro χ ψ h
      apply p.rootScalingCharacterMap_injective
      simpa only [p.rootScalingProjection_character] using h)
    (splitTorus.proj _ p.base.support a)
  rw [p.rootScalingAction_restrict, p.rootScalingProjection_coordinate,
    RelativeRoot.actionWeightSpace_conjugation] at hw
  rw [← hw]
  exact p.pinning.rootVector_mem a

/-- The tuple of units as an actual base point of the simple-root quotient torus. -/
def rootScalingPoint (c : p.base.support → kˣ) :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ p.rootScalingTorus.X :=
  (splitTorus.affinePointsEquiv p.base.support (𝟙 _)).symm c

set_option maxHeartbeats 800000 in
/-- The base point has precisely the supplied coordinate values. -/
theorem rootScalingPoint_coordinate (c : p.base.support → kˣ) (a : p.base.support) :
    Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k)))
      (p.rootScalingPoint c ≫
        (CommGroupScheme.groupHom (splitTorus.proj _ p.base.support a)).hom.hom) = c a := by
  change splitTorus.affinePointsEquiv p.base.support (𝟙 _) (p.rootScalingPoint c) a = c a
  unfold rootScalingPoint
  rw [MulEquiv.apply_symm_apply]

set_option maxHeartbeats 800000 in
/-- At the ground-field test algebra, the coordinate character evaluates to the chosen unit. -/
theorem rootScalingPoint_characterValue (c : p.base.support → kˣ) (a : p.base.support) :
    Lie.characterValue (splitTorus.proj _ p.base.support a)
      (constantPoint p.rootScalingTorus.toGrp (p.rootScalingPoint c)
        ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) k)))) = c a := by
  change Gm.affinePointsEquiv (Spec.map (𝟙 (CommRingCat.of k)))
    (((show Over.mk (Spec.map (𝟙 (CommRingCat.of k))) ⟶
        Over.mk (𝟙 (Spec (CommRingCat.of k))) from
          Over.homMk (Spec.map (𝟙 (CommRingCat.of k))) (by simp)) ≫ p.rootScalingPoint c) ≫
      (CommGroupScheme.groupHom (splitTorus.proj _ p.base.support a)).hom.hom) = _
  apply Units.ext
  have hc := congrArg Units.val (p.rootScalingPoint_coordinate c a)
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom
    (Gm.pointsEquiv _ (Over.mk (𝟙 (Spec (CommRingCat.of k)))) _).val = (c a : k) at hc
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom
    (Gm.pointsEquiv _ (Over.mk (Spec.map (𝟙 (CommRingCat.of k)))) _).val = (c a : k)
  erw [Gm.pointsEquiv_val] at hc ⊢
  simp only [Over.comp_left, Over.homMk_left, Spec.map_id]
  erw [Category.id_comp]
  exact hc

/-- Evaluate the descended conjugation action at the prescribed simple-root scalars. -/
def rootScalingIso (c : p.base.support → kˣ) : G ≅ G :=
  p.rootScalingAction.basePointIso (p.rootScalingPoint c)

/-- The resulting actual automorphism restricts to the identity on the supplied torus. -/
theorem rootScalingIso_inclusion (c : p.base.support → kˣ) :
    p.inclusion ≫ (p.rootScalingIso c).hom = p.inclusion := by
  apply hom_ext_points
  intro T t
  rw [Grp.comp_hom_hom, ← Category.assoc]
  change (t ≫ p.inclusion.hom.hom) ≫
    (p.rootScalingAction.basePointIso (p.rootScalingPoint c)).hom.hom.hom = _
  rw [AutomorphicAction.comp_basePointIso_hom, p.rootScalingAction_act_torus]

/-- The actual differential scales each supplied simple-root vector by its prescribed unit. -/
theorem rootScalingIso_rootVector (c : p.base.support → kˣ) (a : p.base.support) :
    Lie.targetMapLinear (p.rootScalingIso c).hom (CommRingCat.of k)
      (p.pinning.rootVector a) = (c a : k) • p.pinning.rootVector a := by
  have hw := p.rootVector_mem_rootScalingAction_weight a
  rw [RelativeRoot.actionWeightSpace_eq_lieWeightSpace] at hw
  have he := (AutomorphicAction.mem_lieWeightSpace.mp hw) k
    (constantPoint p.rootScalingTorus.toGrp (p.rootScalingPoint c) _)
  have hid : lieKernelMapLinear G (Algebra.ofId (CommRingCat.of k) k)
      (p.pinning.rootVector a) = p.pinning.rootVector a := by
    apply Additive.toMul.injective
    change lieKernelMap G (AlgHom.id (CommRingCat.of k) k) _ = _
    exact lieKernelMap_id G _
  rw [hid, Grp.id_hom_hom, Category.comp_id, p.rootScalingPoint_characterValue] at he
  change Lie.targetMapLinear
    (p.rootScalingAction.basePointIso (p.rootScalingPoint c)).hom (CommRingCat.of k) _ = _
  rw [AutomorphicAction.targetMapLinear_basePointIso]
  exact he

end Langlands.GroupScheme.SplitPinning

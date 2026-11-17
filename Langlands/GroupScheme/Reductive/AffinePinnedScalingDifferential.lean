import Langlands.GroupScheme.Reductive.AffinePinnedScalingAction
import Langlands.GroupScheme.AutomorphicAction.FppfCenterQuotient
import Langlands.GroupScheme.Lie.GroupAlgebraCoefficientMaps
import Langlands.GroupScheme.CocharacterAffineTransport

/-! # Differentials of simple-root scaling automorphisms over arbitrary rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace Lie

attribute [local instance] coordinateOriginAlgebra

/-- Injective coefficient maps reflect equality of actual affine Lie vectors. -/
theorem lieKernelMapLinear_injective_of_injective
    {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]
    {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (hf : Function.Injective f) :
    Function.Injective (lieKernelMapLinear G f) := by
  intro X Y h
  apply (kernelDerivationLinearEquiv G).injective
  apply Derivation.ext
  intro c
  apply hf
  have hc := congrArg (fun Z => kernelDerivationLinearEquiv G Z c) h
  simpa only [kernelDerivationLinearEquiv_map] using hc

end Lie

namespace AutomorphicAction

/-- A point of an affine fppf quotient lifts over a faithfully flat test algebra. -/
theorem exists_faithfullyFlat_affine_quotient_lift
    {R : CommRingCat.{u}} {H Q : GroupScheme (Spec R)}
    [IsAffineHom H.X.hom] [IsAffineHom Q.X.hom]
    (q : H ⟶ Q) [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    (x : Over.mk (𝟙 (Spec R)) ⟶ Q.X) :
    ∃ B : CommAlgCat.{u} R, (algebraMap R B).FaithfullyFlat ∧
      ∃ t : Lie.AffinePoints H B,
        Q.constantPoint x ((algSpec R).obj (op B)) = t ≫ q.hom.hom := by
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  let : IsAffineHom q.hom.hom.left := inferInstance
  let : IsAffine (Over.mk (𝟙 (Spec R))).left := inferInstanceAs (IsAffine (Spec R))
  let L := fppfQuotientPointLift q x
  have hL : IsAffine L.cover.left := by
    change IsAffine (pullback x.left q.hom.hom.left)
    infer_instance
  obtain ⟨⟨B⟩, ⟨e⟩⟩ := (essImage_algSpec (G := L.cover)).mpr hL
  let : Flat L.projection.left := L.flat
  let : Surjective L.projection.left := L.surjective
  have hb : (e.hom ≫ L.projection).left =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    have he := Over.w (e.hom ≫ L.projection)
    change (e.hom ≫ L.projection).left ≫ 𝟙 (Spec R) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) at he
    exact (Category.comp_id _).symm.trans he
  have hf : Flat (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
    rw [← hb, Over.comp_left]
    infer_instance
  have hs : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
    rw [← hb, Over.comp_left]
    infer_instance
  refine ⟨B, (flat_and_surjective_SpecMap_iff _).mp ⟨hf, hs⟩,
    e.hom ≫ L.lift, ?_⟩
  have he : e.hom ≫ L.projection ≫ x = e.hom ≫ L.lift ≫ q.hom.hom :=
    congrArg (fun z => e.hom ≫ z) L.commutes
  have hb' : e.hom ≫ L.projection =
      Over.homMk ((algSpec R).obj (op B)).hom (by simp) := by
    apply Over.OverMorphism.ext
    exact hb
  simpa only [constantPoint, ← Category.assoc, hb'] using he

end AutomorphicAction

namespace AffinePinnedModel

variable (M : AffinePinnedModel.{u})

/-- The simple-root projection evaluates the same monomials in affine coordinates. -/
theorem rootScalingProjection_algebraPoints
    (A : Type u) [CommRing A] [Algebra M.ring A]
    (t : Lie.AffinePoints (splitTorus M.base M.coordinates) A)
    (a : M.basis.support) :
    splitTorus.algebraPointsEquiv M.basis.support A
        (t ≫ M.rootScalingProjection.hom.hom) a =
      ∏ j, splitTorus.algebraPointsEquiv M.coordinates A t j ^ M.rootDatum.root a j := by
  let F := Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom
  change F (splitTorus.pointsEquiv M.basis.support _ (t ≫ _) a) =
    ∏ j, F (splitTorus.pointsEquiv M.coordinates _ t j) ^ M.rootDatum.root a j
  rw [M.rootScalingProjection_points, map_prod]
  simp only [map_zpow]

/-- The prescribed quotient point has the same scalar coordinates after every base change. -/
theorem rootScalingPoint_algebraPoints
    (c : M.basis.support → M.ringˣ)
    (A : Type u) [CommRing A] [Algebra M.ring A] :
    splitTorus.algebraPointsEquiv M.basis.support A
        (constantPoint M.rootScalingTorus.toGrp (M.rootScalingPoint c) _) =
      fun a => Units.map (algebraMap M.ring A).toMonoidHom (c a) := by
  funext a
  change Gm.affinePointsEquiv _
      ((constantPoint M.rootScalingTorus.toGrp (M.rootScalingPoint c) _) ≫
        (CommGroupScheme.groupHom (splitTorus.proj _ M.basis.support a)).hom.hom) = _
  unfold constantPoint
  rw [Category.assoc]
  erw [Gm.affinePointsEquiv_naturality_of_left
    (CommRingCat.ofHom (algebraMap M.ring A)) _ rfl]
  change Units.map _ (splitTorus.affinePointsEquiv M.basis.support
    (𝟙 M.base) (M.rootScalingPoint c) a) = _
  rw [rootScalingPoint, MulEquiv.apply_symm_apply]
  rfl

/-- The actual automorphism scales each pinning vector by its prescribed simple-root unit. -/
theorem rootScalingIso_rootVector
    (c : M.basis.support → M.ringˣ) (a : M.basis.support) :
    Lie.targetMapLinear (M.rootScalingIso c).hom (CommRingCat.of M.ring)
      (M.pinning a 1).val = (c a : M.ring) • (M.pinning a 1).val := by
  let : IsAffineHom (splitTorus M.base M.coordinates).X.hom :=
    (isSplitTorus_splitTorus (S := M.base) M.coordinates).isAffineHom
  let : IsAffineHom M.rootScalingTorus.X.hom :=
    (isSplitTorus_splitTorus (S := M.base) M.basis.support).isAffineHom
  let := M.rootScalingProjection_fppf.1
  let := M.rootScalingProjection_fppf.2.1
  let := M.rootScalingProjection_fppf.2.2
  obtain ⟨B, hB, t, ht⟩ :=
    AutomorphicAction.exists_faithfullyFlat_affine_quotient_lift
      M.rootScalingProjection (M.rootScalingPoint c)
  apply Lie.lieKernelMapLinear_injective_of_injective M.group
    (Algebra.ofId (CommRingCat.of M.ring) B) hB.injective
  rw [← lieKernelTargetLinear_map, LinearMap.map_smulₛₗ]
  change Lie.targetMapLinear
    (M.rootScalingAction.basePointIso (M.rootScalingPoint c)).hom B _ = _
  rw [AutomorphicAction.targetMapLinear_basePointIso]
  erw [ht]
  rw [← AutomorphicAction.differential_restrict, M.rootScalingAction_restrict,
    AutomorphicAction.differential_conjugation]
  have hx := (M.pinning a 1).property B (splitTorus.algebraPointsEquiv M.coordinates B t)
  rw [MulEquiv.symm_apply_apply] at hx
  have he : splitTorus.exponentValue M.coordinates
      (splitTorus.algebraPointsEquiv M.coordinates B t)
      (Multiplicative.ofAdd (M.rootDatum.root a)) =
      Units.map (algebraMap M.ring B).toMonoidHom (c a) := by
    change (∏ j, splitTorus.algebraPointsEquiv M.coordinates B t j ^
      M.rootDatum.root a j) = _
    rw [← M.rootScalingProjection_algebraPoints, ← ht]
    exact congrFun (M.rootScalingPoint_algebraPoints c B) a
  rw [he] at hx
  exact hx

/-- The actual scaling automorphism together with its torus and pinning equations. -/
def rootScalingAutomorphism (c : M.basis.support → M.ringˣ) :
    { phi : M.group ≅ M.group //
      M.inclusion ≫ phi.hom = M.inclusion ∧
      ∀ a : M.basis.support,
        Lie.targetMapLinear phi.hom (CommRingCat.of M.ring) (M.pinning a 1).val =
          (c a : M.ring) • (M.pinning a 1).val } :=
  ⟨M.rootScalingIso c, M.rootScalingIso_inclusion c, M.rootScalingIso_rootVector c⟩

end AffinePinnedModel

end Langlands.GroupScheme

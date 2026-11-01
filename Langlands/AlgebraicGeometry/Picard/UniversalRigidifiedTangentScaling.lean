import Langlands.AlgebraicGeometry.Picard.UniversalRigidifiedTangentDeformation
import Langlands.AlgebraicGeometry.Picard.DualNumberScaling

/-! # Actual epsilon pullback for the universal tangent comparison -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.GroupScheme.GeneralLinear.DualNumber

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

variable {k : Type u} [Field k]

/-- Epsilon scaling as an actual endomorphism of the dual-number test over the field. -/
def dualNumberTestScale (c : k) : dualNumberTest k ⟶ dualNumberTest k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (epsilonScale c).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (epsilonScale c).commutes a)

/-- The actual slice-valued point of a scalar multiple is precomposition by epsilon scaling. -/
lemma rationalStalkDerivationPoint_smul
    (P : Over (Spec (CommRingCat.of k)))
    (e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P) :
    letI := stalkAlgebraOver P.hom (e.left (IsLocalRing.closedPoint k))
    letI := (rationalStalkAugmentation P.hom e.left (Over.w e)).toRingHom.toAlgebra
    ∀ c D, rationalStalkDerivationPoint P e (c • D) =
      dualNumberTestScale c ≫ rationalStalkDerivationPoint P e D := by
  let := stalkAlgebraOver P.hom (e.left (IsLocalRing.closedPoint k))
  let := (rationalStalkAugmentation P.hom e.left (Over.w e)).toRingHom.toAlgebra
  intro c D
  apply Over.OverMorphism.ext
  exact rationalStalkDerivationTangentEquiv_smul P.hom e.left (Over.w e) c D

namespace DualNumberThickening

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- Fibre-product symmetry commutes with actual epsilon scaling. -/
lemma relativeSpaceSymmetry_scale (c : k) :
    (relativeSpaceSymmetry f (dualNumberTest k)).inv ≫
        (relativeSpace f).map (dualNumberTestScale c) =
      scale f c ≫ (relativeSpaceSymmetry f (dualNumberTest k)).inv := by
  apply pullback.hom_ext
  · simp [relativeSpaceSymmetry, relativeSpace, Over.pullback, dualNumberTestScale,
      dualNumberTest, scale, pullback.map]
  · simp [relativeSpaceSymmetry, relativeSpace, Over.pullback, dualNumberTestScale,
      dualNumberTest, scale, pullback.map]

end DualNumberThickening

namespace RigidifiedLineBundle

open Langlands.SchemeModule Langlands.Scheme.Modules DualNumberThickening

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _)

/-- Forgetting rigidification carries test-scheme scaling to pullback by the actual
scaling endomorphism of the ordinary thickening. -/
lemma underlyingDualNumberClassEquiv_scale (c : k)
    (q : Classes f ε hε (dualNumberTest k)) :
    underlyingDualNumberClassEquiv preservation f ε hε
        (classesPullback f ε hε (dualNumberTestScale c) q) =
      LineBundle.pullbackHom preservation (scale f c)
        (underlyingDualNumberClassEquiv preservation f ε hε q) := by
  simp only [underlyingDualNumberClassEquiv_apply, forgetClass_pullback]
  exact (LineBundle.pullbackHom_comp_eq preservation _ _
    (relativeSpaceSymmetry_scale f c) _).trans
      (LineBundle.pullbackHom_comp preservation _ _ _).symm

variable {P : Over (Spec (CommRingCat.of k))}
  (L : relative f ε hε P) (hL : IsUniversal f ε hε L)

/-- Scalar multiplication in the actual tangent module is actual epsilon-scaling
pullback on its ordinary first-order line-bundle class. -/
lemma tangentDeformationEquiv_smul_val (c : k)
    (t : Langlands.Scheme.tangentSpaceAtPoint P (trivialParameter f ε hε L hL)) :
    (tangentDeformationEquiv preservation f ε hε L hL (c • t)).val =
      LineBundle.pullbackHom preservation (scale f c)
        (tangentDeformationEquiv preservation f ε hε L hL t).val := by
  let e := trivialParameter f ε hε L hL
  let := stalkAlgebraOver P.hom (e.left (IsLocalRing.closedPoint k))
  let := (rationalStalkAugmentation P.hom e.left (Over.w e)).toRingHom.toAlgebra
  simp only [tangentDeformationEquiv_val]
  rw [map_smul (tangentSpaceAtPointDerivationEquiv P e),
    rationalStalkDerivationPoint_smul,
    classifyingMap_comp f ε hε RigidifiedModule.pullbackCoherence,
    underlyingDualNumberClassEquiv_scale]

end RigidifiedLineBundle

end Langlands.AlgebraicGeometry.Picard

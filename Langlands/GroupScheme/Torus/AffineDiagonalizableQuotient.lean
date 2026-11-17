import Langlands.GroupScheme.Torus.AffineDiagonalizableGraph
import Langlands.GroupScheme.Torus.DiagonalizableGeometry
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Langlands.GroupScheme.NormalQuotientGroup
import Mathlib.AlgebraicGeometry.Noetherian

/-! # The degree-zero quotient of an affine diagonalizable translation action -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.CharacterAction

open Langlands.CommutativeAlgebra.StronglyGraded

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
variable {B : CommAlgCat.{u} R} (a : Action (M := M) B)

/-- Scalars belong to the actual degree-zero ring. -/
def invariantScalar : R →+* degreeZero (c := (coaction a).hom.toRingHom) :=
  (algebraMap R B).codRestrict _ (fun r => by
    change (coaction a).hom (algebraMap R B r) =
      AddMonoidAlgebra.single 0 (algebraMap R B r)
    rw [AlgHom.commutes]
    rfl)

instance invariantAlgebraStructure :
    Algebra R (degreeZero (c := (coaction a).hom.toRingHom)) :=
  (invariantScalar a).toAlgebra

instance invariantScalarTower :
    IsScalarTower R (degreeZero (c := (coaction a).hom.toRingHom)) B :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The degree-zero ring with its inherited original scalar algebra. -/
abbrev invariantAlgebra : CommAlgCat.{u} R :=
  CommAlgCat.of R (degreeZero (c := (coaction a).hom.toRingHom))

/-- The inclusion of the actual invariants into the coordinate ring. -/
def invariantInclusion : invariantAlgebra a ⟶ B :=
  CommAlgCat.ofHom
    { __ := (degreeZero (c := (coaction a).hom.toRingHom)).subtype
      commutes' := fun _ => rfl }

/-- The affine spectrum of the actual degree-zero ring. -/
def quotientScheme : Over (Spec R) := (algSpec R).obj (op (invariantAlgebra a))

/-- The quotient morphism on the coordinate spectrum. -/
def spectrumProjection : (algSpec R).obj (op B) ⟶ quotientScheme a :=
  (algSpec R).map (invariantInclusion a).op

/-- The strong canonical comparison presents the two coaction maps as a pushout. -/
theorem invariant_isPushout (hs : IsStrong (c := (coaction a).hom.toRingHom)) :
    IsPushout (CommRingCat.ofHom (invariantInclusion a).hom.toRingHom)
      (CommRingCat.ofHom (invariantInclusion a).hom.toRingHom)
      (CommRingCat.ofHom (constant (M := M) B).hom.toRingHom)
      (CommRingCat.ofHom (coaction a).hom.toRingHom) := by
  let e := (canonicalIso (isGrading_coaction a) hs).toRingEquiv.toCommRingCatIso
  refine (CommRingCat.isPushout_tensorProduct
    (degreeZero (c := (coaction a).hom.toRingHom)) B B).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    change canonical (c := (coaction a).hom.toRingHom) (b ⊗ₜ 1) = _
    rw [canonical_tmul, map_one, mul_one]
    rfl
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    change canonical (c := (coaction a).hom.toRingHom) (1 ⊗ₜ b) = _
    rw [canonical_tmul]
    change 1 * _ = _
    rw [one_mul]
    rfl

/-- The quotient spectrum has the expected coaction fiber square. -/
theorem spectrumProjection_isPullback
    (hs : IsStrong (c := (coaction a).hom.toRingHom)) :
    IsPullback ((algSpec R).map (constant (M := M) B).op)
      ((algSpec R).map (coaction a).op) (spectrumProjection a) (spectrumProjection a) := by
  apply IsPullback.of_map_of_faithful (F := Over.forget (Spec R))
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (invariant_isPushout a hs)

/-- Strong grading makes the spectrum projection faithfully flat. -/
theorem spectrumProjection_flat_surjective
    (hs : IsStrong (c := (coaction a).hom.toRingHom)) :
    Flat (spectrumProjection a).left ∧ Surjective (spectrumProjection a).left := by
  have : Module.FaithfullyFlat (degreeZero (c := (coaction a).hom.toRingHom)) B :=
    faithfullyFlat (isGrading_coaction a) hs
  apply (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (invariantInclusion a).hom.toRingHom)).mpr
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance

end Langlands.GroupScheme.CharacterAction

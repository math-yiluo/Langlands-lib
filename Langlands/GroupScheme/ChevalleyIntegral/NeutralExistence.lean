import Langlands.GroupScheme.ChevalleyIntegral.NeutralFieldComparison
import Langlands.GroupScheme.IntegralModel.DedekindNeutralModel

/-! # Integral existence from smooth closures and full-fibre opens -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.ChevalleyIntegral

open SplitExistence SplitExistence.ChevalleyData

variable {I J : Type u} [Fintype I] [DecidableEq I]
  {P : RootDatum J (I → ℤ) (I → ℤ)} {b : P.Base}
  (D : ChevalleyData P b)
  (R K : Type u) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (C : D.ChevGroup K)

local instance : Smooth C.H.X.hom := C.smooth
local instance : IsAffineHom C.H.X.hom := C.affine
local instance : ConnectedSpace C.H.X.left := C.connected
local instance : GeometricallyConnected C.H.X.hom :=
  C.H.geometricallyConnected_of_connected
local instance : GeometricallyIntegral C.H.X.hom :=
  smoothConnectedAffineGeometry.1 K C.H inferInstance inferInstance inferInstance
local instance : IsIntegral C.H.X.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton C.H.X.hom

variable (hsm : (genericModel D R K C).IsSmooth)

/-- Choose one affine smooth neutral model of the integral closure. The choice
depends only on the integral closure and its smoothness, before any field algebra. -/
def neutralModelOfSmoothClosure : IntegralModel R K C.H :=
  Classical.choose ((genericModel D R K C).exists_dedekindNeutralModel hsm)

/-- The chosen neutral model maps to the full closure and extends the generic identity. -/
def neutralInclusionOfSmoothClosure :
    (neutralModelOfSmoothClosure D R K C hsm).Hom (genericModel D R K C) (𝟙 C.H) :=
  Classical.choose (Classical.choose_spec
    ((genericModel D R K C).exists_dedekindNeutralModel hsm))

omit [Fintype I] [DecidableEq I] in
/-- The chosen model is the actual relative identity component, is smooth, and has
geometrically connected fibres. -/
theorem neutralModelOfSmoothClosure_spec :
    IsRelativeIdentityComponent (genericModel D R K C).group
        (neutralInclusionOfSmoothClosure D R K C hsm).hom ∧
      (neutralModelOfSmoothClosure D R K C hsm).IsSmooth ∧
      GeometricallyConnected (neutralModelOfSmoothClosure D R K C hsm).group.X.hom :=
  Classical.choose_spec (Classical.choose_spec
    ((genericModel D R K C).exists_dedekindNeutralModel hsm))

/-- The full coordinate torus in the fixed neutral model. -/
def neutralTorusOfSmoothClosure :
    splitTorus (Spec (CommRingCat.of R)) I ⟶
      (neutralModelOfSmoothClosure D R K C hsm).group :=
  neutralCoordinateTorus D R K C (neutralModelOfSmoothClosure_spec D R K C hsm).1

theorem neutralTorusOfSmoothClosure_closed :
    IsClosedSubgroup (neutralTorusOfSmoothClosure D R K C hsm) :=
  neutralCoordinateTorus_closed D R K C
    (neutralModelOfSmoothClosure_spec D R K C hsm).1

/-- Nonempty opens in the full fibres supply comparisons for the single chosen
neutral model and its full coordinate torus. -/
theorem hasFieldComparisons_neutralModelOfSmoothClosure [Finite J]
    (h : ∀ (k : Type u) [Field k] [Algebra R k],
      ∃ (H : D.ChevGroup k)
        (U : (fieldModel D R K C k (CommRingCat.ofHom (algebraMap R k))).X.left.Opens),
        U.1.Nonempty ∧ U.1 ⊆ Set.range
          (fieldEmbedding D R K C k (CommRingCat.ofHom (algebraMap R k)) H).hom.hom.left) :
    HasFieldComparisons D (neutralModelOfSmoothClosure D R K C hsm).group
      (neutralTorusOfSmoothClosure D R K C hsm) := by
  obtain ⟨hi, hNsm, hNgc⟩ := neutralModelOfSmoothClosure_spec D R K C hsm
  let : Smooth (neutralModelOfSmoothClosure D R K C hsm).group.X.hom := hNsm
  let := hNgc
  exact hasFieldComparisons_of_fullFieldOpen D R K C hi h

include hsm in
/-- Smoothness of the full closure and nonempty full-fibre opens yield the precise
single-family input to the integral-existence reduction. -/
theorem exists_neutralRealization_of_fullFieldOpen [Finite J]
    (h : ∀ (k : Type u) [Field k] [Algebra R k],
      ∃ (H : D.ChevGroup k)
        (U : (fieldModel D R K C k (CommRingCat.ofHom (algebraMap R k))).X.left.Opens),
        U.1.Nonempty ∧ U.1 ⊆ Set.range
          (fieldEmbedding D R K C k (CommRingCat.ofHom (algebraMap R k)) H).hom.hom.left) :
    ∃ (G : GroupScheme (Spec (CommRingCat.of R)))
      (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
      IsAffineHom G.X.hom ∧ Flat G.X.hom ∧ LocallyOfFinitePresentation G.X.hom ∧
        IsClosedSubgroup i ∧ HasFieldComparisons D G i := by
  let N := neutralModelOfSmoothClosure D R K C hsm
  let : Smooth N.group.X.hom := (neutralModelOfSmoothClosure_spec D R K C hsm).2.1
  exact ⟨N.group, neutralTorusOfSmoothClosure D R K C hsm, inferInstance, inferInstance,
    inferInstance, neutralTorusOfSmoothClosure_closed D R K C hsm,
    hasFieldComparisons_neutralModelOfSmoothClosure D R K C hsm h⟩

/-- It remains to prove smoothness and the nonempty full-fibre open-image condition
for the chosen integer closure of every full coordinate Chevalley datum. -/
theorem integralExistence_of_smoothClosure_fullFieldOpen
    (h : ∀ (I J : Type u) [Fintype I] [DecidableEq I] [Finite J]
      (P : RootDatum J (I → ℤ) (I → ℤ)) [P.IsReduced] (b : P.Base)
      (D : ChevalleyData P b),
      (integerModel D).IsSmooth ∧
        ∀ (k : Type u) [Field k] [Algebra (ULift.{u} ℤ) k],
          ∃ (H : D.ChevGroup k)
            (U : (fieldModel D (ULift.{u} ℤ) (FractionRing (ULift.{u} ℤ))
              (integerGenericGroup D) k
              (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) k))).X.left.Opens),
            U.1.Nonempty ∧ U.1 ⊆ Set.range
              (fieldEmbedding D (ULift.{u} ℤ) (FractionRing (ULift.{u} ℤ))
                (integerGenericGroup D) k
                (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) k)) H).hom.hom.left) :
    ChevalleyIntegralExistenceStatement.{u} := by
  apply integralExistence_of_comparisons
  intro I J _ _ _ P _ b D _
  obtain ⟨hsm, hopen⟩ := h I J P b D
  exact exists_neutralRealization_of_fullFieldOpen D (ULift.{u} ℤ)
    (FractionRing (ULift.{u} ℤ)) (integerGenericGroup D) hsm hopen

end Langlands.GroupScheme.ChevalleyIntegral

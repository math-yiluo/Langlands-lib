import Langlands.BruhatTits.IntegralModels.IncidentCentralizerComparison
import Langlands.GroupScheme.Unipotent.KernelCoordinateTransport

/-! # Full kernels of incident centralizer composites -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom

section General

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {source target : RelativeComponentModelData R K G}
    (φ : RelativeComponentModelHom source target)
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    (T : IntegralTorusData source S i) (hT : IsSplitTorus T.torus.toGrp)
    {Z : GroupScheme (Spec (CommRingCat.of K))}
    (j : Z ⟶ G) (hj : (torusCentralizer i).IsRepresentedBy j)
    (Q : SpecialFibreQuotientData target)

/-- The original source centralizer inclusion followed by the incident
special-fibre map and the target radical projection. -/
def centralizerTargetReductiveQuotientMap :
    ((T.toIntegralSplitTorusData hT).centralizerModel j hj).specialFibre ⟶ Q.quotient :=
  ((T.toIntegralSplitTorusData hT).centralizerModelMap j hj).specialFibreMap ≫
    φ.neutralSpecialFibreMap ≫ Q.projection

end General

section Unramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    {source target :
      RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G}
    (φ : RelativeComponentModelHom source target)
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (T : IntegralTorusData source C.S C.i) (hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData target)
    (Ω Ω' : Set C.Apartment)
    (hsource : source.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω'))
    (htarget : target.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (hne : Ω.Nonempty) (hne' : Ω'.Nonempty)

private instance neutral_smooth
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G) :
    Smooth D.neutral.group.X.hom := D.neutral_smooth

/-- The actual integral centralizer comparison identifies the full original
source-composite kernel with the same-model target-composite kernel. -/
def centralizerTargetReductiveQuotientKernelIso :
    kernel (φ.centralizerTargetReductiveQuotientMap T hT
      C.centralizer.j C.centralizer.isRepresentedBy Q) ≅
      kernel ((((φ.mapIntegralTorus T).toIntegralSplitTorusData hT).centralizerModelMap
        C.centralizer.j C.centralizer.isRepresentedBy).specialFibreMap ≫ Q.projection) := by
  let A := T.toIntegralSplitTorusData hT
  let B := (φ.mapIntegralTorus T).toIntegralSplitTorusData hT
  let e := (UnramifiedCentralizerComparison.modelIso C E A B Ω Ω'
    hsource htarget hne hne').specialFibreIso
  apply kernelCoordinateIso _ _ e
  dsimp only [e]
  rw [← Category.assoc,
    UnramifiedCentralizerComparison.specialFibreIso_comp C E A B Ω Ω'
      hsource htarget hne hne' φ.neutral]
  rfl

include hsource htarget hne hne' in
/-- Smoothness concerns the full scheme-theoretic kernel of the original
source centralizer composite, with no smoothness premise on the incident map. -/
theorem centralizerTargetReductiveQuotientMap_smooth_kernel (hQ : Q.IsReductiveQuotient) :
    Smooth (kernel (φ.centralizerTargetReductiveQuotientMap T hT
      C.centralizer.j C.centralizer.isRepresentedBy Q)).X.hom := by
  let B := (φ.mapIntegralTorus T).toIntegralSplitTorusData hT
  let q := (B.centralizerModelMap C.centralizer.j
    C.centralizer.isRepresentedBy).specialFibreMap ≫ Q.projection
  let e := φ.centralizerTargetReductiveQuotientKernelIso C E T hT Q Ω Ω'
    hsource htarget hne hne'
  let eo := (Grp.forget (Over
    (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))).mapIso e
  have : IsIso eo.hom.left := (Over.forget
    (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F))))).map_isIso eo.hom
  let : Smooth ((Grp.forget (Over
    (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))).obj
      (kernel q)).hom :=
    B.centralizerReductiveQuotientMap_smooth_kernel C.centralizer.j
      C.centralizer.isRepresentedBy Q hQ
  change Smooth ((Grp.forget (Over
    (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))).obj
      (kernel (φ.centralizerTargetReductiveQuotientMap T hT
        C.centralizer.j C.centralizer.isRepresentedBy Q))).hom
  rw [← eo.hom.w]
  infer_instance

end Unramified

end Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom

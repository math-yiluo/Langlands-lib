import Langlands.BruhatTits.IntegralModels.UnramifiedZeroFixerCentralizerImage
import Langlands.BruhatTits.IntegralModels.IntegralRootModelMap
import Langlands.GroupScheme.Torus.SmoothQuotientCentralizer
import Langlands.GroupScheme.IntegralModel.SpecialFibreKernelIso

/-! # Actual centralizer comparisons for zero-fixer models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.BruhatTits.IntegralModels

section Residue

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {D : RelativeComponentModelData R K G}
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    (A : IntegralSplitTorusData D.neutral i)
    {Z : GroupScheme (Spec (CommRingCat.of K))}
    (j : Z ⟶ G) (hj : (torusCentralizer i).IsRepresentedBy j)
    (Q : SpecialFibreQuotientData D)

private instance neutral_smooth : Smooth D.neutral.group.X.hom := D.neutral_smooth

private instance modelSpecialFibre_affine
    {H : GroupScheme (Spec (CommRingCat.of K))} (P : IntegralModel R K H) :
    IsAffineHom P.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd
    P.group.X.hom (IntegralModel.residueBaseMap R))
  infer_instance

private instance modelSpecialFibre_smooth
    {H : GroupScheme (Spec (CommRingCat.of K))} (P : IntegralModel R K H)
    [Smooth P.group.X.hom] : Smooth P.specialFibre.X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd
    P.group.X.hom (IntegralModel.residueBaseMap R))
  infer_instance

namespace IntegralSplitTorusData

/-- The original residue centralizer inclusion followed by the actual radical
projection has smooth full scheme-theoretic kernel. -/
theorem centralizerReductiveQuotientMap_smooth_kernel (hQ : Q.IsReductiveQuotient) :
    Smooth (kernel ((A.centralizerModelMap j hj).specialFibreMap ≫ Q.projection)).X.hom := by
  let : Smooth (A.centralizerModel j hj).group.X.hom :=
    A.centralizerModel_isSmooth j hj
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  let : IsAffine Q.quotient.X.left := isAffine_of_isAffineHom Q.quotient.X.hom
  obtain ⟨V, l, hlc, hls, hl⟩ :=
    splitTorusCentralizer_hasSmoothClosedRepresentative_overRing
      (A.specialFibreInclusion ≫ Q.projection) A.specialFibreTorus_isSplit inferInstance
  let : Smooth V.X.hom := hls
  let : IsClosedImmersion l.hom.hom.left := hlc
  let : IsAffineHom V.X.hom := by
    rw [← Over.w l.hom.hom]
    infer_instance
  exact TorusSmoothQuotient.smooth_kernel_comp A.specialFibreTorus_isSplit
    A.specialFibreInclusion Q.projection
    (A.centralizerModelMap j hj).specialFibreMap l
    (A.centralizerModelMap_specialFibre_isCentralizer j hj) hl
    (Q.projection_smooth hQ)

end IntegralSplitTorusData

end Residue

namespace UnramifiedCentralizerComparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    {N M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G}
    [Smooth N.group.X.hom] [Smooth M.group.X.hom]
    (A : IntegralSplitTorusData N C.i) (B : IntegralSplitTorusData M C.i)
    (Ω Ω' : Set C.Apartment)
    (hN : N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω'))
    (hM : M.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (hne : Ω.Nonempty) (hne' : Ω'.Nonempty)

include hN hM hne hne' in
/-- Every nonempty apartment subset gives the same integral-point subgroup
inside the specified full generic centralizer. -/
theorem integralPoints_eq :
    (A.centralizerModel C.centralizer.j C.centralizer.isRepresentedBy).integralPoints =
      (B.centralizerModel C.centralizer.j C.centralizer.isRepresentedBy).integralPoints := by
  rw [A.centralizerModel_integralPoints_eq_comap,
    B.centralizerModel_integralPoints_eq_comap, hN, hM,
    Subgroup.comap_inf, Subgroup.comap_inf,
    C.comap_pointwiseFixer_centralizer_eq Ω' Ω hne' hne]

/-- The actual smooth integral centralizers are compatibly isomorphic. This
requires neither incidence nor smoothness of an ambient comparison map. -/
def modelIso :
    (A.centralizerModel C.centralizer.j C.centralizer.isRepresentedBy).Iso
      (B.centralizerModel C.centralizer.j C.centralizer.isRepresentedBy)
      (CategoryTheory.Iso.refl C.centralizer.Z) :=
  IntegralModel.isoOfIntegralPointsEq _ _
    (IntegralModel.fixedField_hasSmoothHomExtension IntegralModel.smoothHomExtension F)
    (A.centralizerModel_isSmooth C.centralizer.j C.centralizer.isRepresentedBy)
    (B.centralizerModel_isSmooth C.centralizer.j C.centralizer.isRepresentedBy)
    (integralPoints_eq C E A B Ω Ω' hN hM hne hne')

/-- Generic rigidity identifies the actual centralizer isomorphism with the
restriction of any compatible ambient comparison homomorphism. -/
theorem modelIso_comp (φ : N.Hom M (𝟙 G)) :
    (modelIso C E A B Ω Ω' hN hM hne hne').iso.hom ≫
        (B.centralizerModelMap C.centralizer.j C.centralizer.isRepresentedBy).hom =
      (A.centralizerModelMap C.centralizer.j C.centralizer.isRepresentedBy).hom ≫ φ.hom := by
  apply IntegralModel.hom_eq_of_generic
  apply (cancel_mono M.genericIso.hom).mp
  simp only [Functor.map_comp, Category.assoc,
    (B.centralizerModelMap C.centralizer.j C.centralizer.isRepresentedBy).generic_comm,
    φ.generic_comm, Category.comp_id]
  rw [← Category.assoc, (modelIso C E A B Ω Ω' hN hM hne hne').generic_comm,
    CategoryTheory.Iso.refl_hom, Category.comp_id]
  exact (A.centralizerModelMap C.centralizer.j C.centralizer.isRepresentedBy).generic_comm.symm

/-- The same comparison on the original residue schemes. -/
theorem specialFibreIso_comp (φ : N.Hom M (𝟙 G)) :
    (modelIso C E A B Ω Ω' hN hM hne hne').specialFibreIso.hom ≫
        (B.centralizerModelMap C.centralizer.j C.centralizer.isRepresentedBy).specialFibreMap =
      (A.centralizerModelMap C.centralizer.j C.centralizer.isRepresentedBy).specialFibreMap ≫
        φ.specialFibreMap := by
  simpa only [IntegralModel.Iso.specialFibreIso, Functor.mapIso_hom,
    IntegralModel.Hom.specialFibreMap, Functor.map_comp] using
    congrArg (GroupScheme.baseChange (IntegralModel.residueBaseMap (fixedFieldIntegers F))).map
      (modelIso_comp C E A B Ω Ω' hN hM hne hne' φ)

end UnramifiedCentralizerComparison

end Langlands.BruhatTits.IntegralModels

import Langlands.GroupScheme.Reductive.StrictHenselianDVRIsogenyRigidityStatement
import Langlands.GroupScheme.Reductive.SpecialFibreCommonTorus
import Langlands.GroupScheme.Reductive.FibrewiseIsogenyBaseChange
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Lie.LocalSpecialization
import Langlands.GroupScheme.Lie.SurjectiveDifferentialLifting
import Langlands.GroupScheme.CentralIsogeny.SmoothFiniteKernel
import Langlands.GroupScheme.CentralIsogeny.RestrictionIsomorphism
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof

/-! # Rigidity of a specified fibrewise isogeny with isomorphic special fibre -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

namespace Langlands.GroupScheme

/-- A specified fibrewise isogeny of reductive groups over a strictly Henselian
local ring is an isomorphism on every algebra-valued field fibre once its special
fibre is an isomorphism. -/
theorem isIso_fieldFibre_of_specialFibreIso
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    (hG : IsReductive G) (hH : IsReductive H) (f : G ⟶ H)
    (hf : IsFibrewiseIsogeny f)
    (hs : TorusLocalSpecialization.IsSpecialFibreIsomorphism f)
    (K : Type u) [Field K] [Algebra R K] :
    IsIso ((GroupScheme.baseChange (Spec.algebraMap R K)).map f) := by
  classical
  let b := algebraBaseMap R K
  let B := GroupScheme.baseChange b
  let GK := B.obj G
  let HK := B.obj H
  have hGK : IsConnectedReductive GK := hG.isConnectedReductive_algebraMap K
  have hHK : IsConnectedReductive HK := hH.isConnectedReductive_algebraMap K
  let := hG.smooth
  let := hG.isAffineHom
  let := hH.smooth
  let := hH.isAffineHom
  have : Smooth GK.X.hom := hGK.smooth
  have : IsAffineHom GK.X.hom := hGK.isAffineHom
  have : ConnectedSpace GK.X.left := hGK.connectedSpace
  have : Smooth HK.X.hom := hHK.smooth
  have : IsAffineHom HK.X.hom := hHK.isAffineHom
  have hdiff : Function.Surjective (Lie.targetMapLinear (B.map f) K) := by
    intro y
    obtain ⟨x, hx⟩ := Lie.hasSurjectiveDifferential_of_specialFibreIso f hs K
      (Lie.kernelBaseChangeLinearEquiv R K H K y)
    refine ⟨(Lie.kernelBaseChangeLinearEquiv R K G K).symm x, ?_⟩
    apply (Lie.kernelBaseChangeLinearEquiv R K H K).injective
    rw [Lie.kernelBaseChangeLinearEquiv_target R K K,
      LinearEquiv.apply_symm_apply, hx]
  have : Smooth (B.map f).hom.hom.left :=
    Lie.smooth_of_surjective_differential (B.map f) hGK.smooth hdiff
  have hfin : IsIsogeny (B.map f) := hf.isFieldwiseIsogeny K b
  have : IsFinite (B.map f).hom.hom.left := hfin.1
  have hcent : IsCentralIsogeny (B.map f) :=
    ⟨hfin, inferInstance, isCentral_kernelι_of_smooth_finite (B.map f)⟩
  obtain ⟨I, hI, i, _hi, hmax, hic, _hmaxc⟩ :=
    hasCommonCoordinateMaximalTorus_of_specialFibreIso hG hH f hs
  let : Fintype I := hI
  let T := (CommGroupScheme.baseChange b).obj
    (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I)
  let j := B.map i
  let j' := B.map (i ≫ f)
  have hmaxK : IsMaximalTorus (T := T) j := hmax.fieldPoint b
  have : IsClosedImmersion j'.hom.hom.left := hic.baseChange b
  have : Mono j'.hom.hom := Over.mono_of_mono_left _
  have ht : j ≫ B.map f = CommGroupScheme.groupHom (𝟙 T) ≫ j' := by
    change B.map i ≫ B.map f = 𝟙 _ ≫ B.map (i ≫ f)
    rw [Category.id_comp, Functor.map_comp]
  exact hcent.isIso_of_selfCentralizing_restriction ht
    (maximalTorusCentralizer K GK hGK T j hmaxK)

/-- The actual field-fibre isomorphism with the prescribed base-changed
homomorphism as its forward map. -/
def fieldFibreIsoOfSpecialFibreIso
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    (hG : IsReductive G) (hH : IsReductive H) (f : G ⟶ H)
    (hf : IsFibrewiseIsogeny f)
    (hs : TorusLocalSpecialization.IsSpecialFibreIsomorphism f)
    (K : Type u) [Field K] [Algebra R K] :
    (GroupScheme.baseChange (Spec.algebraMap R K)).obj G ≅
      (GroupScheme.baseChange (Spec.algebraMap R K)).obj H :=
  haveI := isIso_fieldFibre_of_specialFibreIso hG hH f hf hs K
  asIso ((GroupScheme.baseChange (Spec.algebraMap R K)).map f)

@[simp]
theorem fieldFibreIsoOfSpecialFibreIso_hom
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    (hG : IsReductive G) (hH : IsReductive H) (f : G ⟶ H)
    (hf : IsFibrewiseIsogeny f)
    (hs : TorusLocalSpecialization.IsSpecialFibreIsomorphism f)
    (K : Type u) [Field K] [Algebra R K] :
    (fieldFibreIsoOfSpecialFibreIso hG hH f hf hs K).hom =
      (GroupScheme.baseChange (Spec.algebraMap R K)).map f := rfl

/-- The exact prescribed-map rigidity interface over a strictly Henselian DVR. -/
theorem strictHenselianDVRIsogenyRigidity :
    StrictHenselianDVRIsogenyRigidityStatement.{u} := by
  intro R _ _ _ _ _ K _ _ _ G H hG hH f hf hs
  exact isIso_fieldFibre_of_specialFibreIso hG hH f hf hs K

end Langlands.GroupScheme

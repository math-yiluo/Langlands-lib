import Langlands.GroupScheme.Reductive.AffineOpenRootDatumCharacterCover
import Langlands.GroupScheme.Reductive.AffineRootDatumTransport
import Langlands.GroupScheme.Reductive.IsogenyTorusRigidityCoordinates
import Langlands.GroupScheme.Reductive.SuppliedRootIsogenyConjugacy

/-! # Assembling coordinate-torus conjugators over affine open covers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

namespace Langlands.GroupScheme

section CoverDescent

variable {S : Scheme.{u}} {I : Type u} [Fintype I]
  {G H : GroupScheme S}

/-- On an actual affine open cover, the canonically coordinated pullbacks
admit fppf local conjugators in the target coordinate torus. -/
def HasAffineOpenCoordinateTorusConjugacy
    (j : splitTorus S I ⟶ H) (f F : G ⟶ H) : Prop :=
  ∃ U : Scheme.AffineOpenCover.{u} S,
    ∀ a : U.I₀, FppfLocallyTorusConjugate
      (T := splitTorus.commGroupScheme _ I)
      ((splitTorus.baseChangeIso (U.f a) I).inv ≫ (baseChange (U.f a)).map j)
      ((baseChange (U.f a)).map f) ((baseChange (U.f a)).map F)

/-- Coordinate conjugators on an affine open cover give an actual fppf
conjugating cover over the original scheme. -/
theorem HasAffineOpenCoordinateTorusConjugacy.fppfLocallyTorusConjugate
    {j : splitTorus S I ⟶ H} {f F : G ⟶ H}
    (h : HasAffineOpenCoordinateTorusConjugacy j f F) :
    FppfLocallyTorusConjugate (T := splitTorus.commGroupScheme S I) j f F := by
  obtain ⟨U, hU⟩ := h
  let C : Scheme.Cover.{u} Scheme.fppfPrecoverage S :=
    U.openCover.changeProp (fun a => ⟨inferInstance, inferInstance⟩)
  apply fppfLocallyTorusConjugate_of_cover
    (S := S) (G := G) (H := H) (T := splitTorus.commGroupScheme S I) j f F C
  intro a
  exact (fppfLocallyTorusConjugate_torusIso_iff
    (S := Spec (U.X a))
    (G := (baseChange (U.f a)).obj G)
    (H := (baseChange (U.f a)).obj H)
    (T := (CommGroupScheme.baseChange (U.f a)).obj (splitTorus.commGroupScheme S I))
    (U := splitTorus.commGroupScheme _ I)
    (splitTorus.baseChangeIso (U.f a) I).symm
    ((baseChange (U.f a)).map j)
    ((baseChange (U.f a)).map f) ((baseChange (U.f a)).map F)).mp (hU a)

end CoverDescent

/-- The intrinsic root-datum compatibility proposition supplies coordinate
isogeny conjugacy over arbitrary commutative rings. -/
theorem coordinateSplitIsogenyTorusConjugacy_of_affineSplitSurjectionRootDatum
    (hAffine : AffineSplitSurjectionRootDatumStatement.{u}) :
    CoordinateSplitIsogenyTorusConjugacyStatement.{u} := by
  intro R _ G H hG hH I I' _ _ i j J J' P Q
  let := hG.isAffineHom
  let := hH.isAffineHom
  intro hi hmaxG hP hfreeP hj hmaxH hQ hfreeQ phi Phi hphi hPhi htorus heq
  classical
  let := hG.smooth
  let := hH.smooth
  let := hP.finite
  let := hQ.finite
  let := hP.isReduced
  let := hQ.isReduced
  let := hphi.1
  let := hPhi.1
  obtain ⟨tau, htau⟩ := htorus
  let tauC : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
      splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I' := Additive.ofMul tau
  have hphiT : i ≫ phi = CommGroupScheme.groupHom tauC ≫ j := htau
  have hPhiT : i ≫ Phi = CommGroupScheme.groupHom tauC ≫ j := heq.symm.trans htau
  have hcharacters :=
    hasZariskiLocalRootDatumTorusCharacterMap_of_affineSplitSurjectionRootDatum
      hAffine hG hH i j hi hmaxG hj hmaxH hP hQ hfreeP hfreeQ
      phi inferInstance hphi.2.2 tauC hphiT
  obtain ⟨U, hU⟩ := hcharacters.common_torusSquares i j phi Phi hphiT hPhiT
  apply HasAffineOpenCoordinateTorusConjugacy.fppfLocallyTorusConjugate
  refine ⟨U, fun a => ?_⟩
  let b := U.f a
  let hGAff : IsAffineHom ((baseChange b).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b))
  let hHAff : IsAffineHom ((baseChange b).obj H).X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd H.X.hom b))
  let hfinphiA : IsFinite ((baseChange b).map phi).hom.hom.left :=
    MorphismProperty.of_isPullback (P := @IsFinite)
      (baseChange_map_isPullback b phi).flip inferInstance
  let hfinPhiA : IsFinite ((baseChange b).map Phi).hom.hom.left :=
    MorphismProperty.of_isPullback (P := @IsFinite)
      (baseChange_map_isPullback b Phi).flip inferInstance
  have hPA := hP.affineBaseChange b
  have hQA := hQ.affineBaseChange b
  have hmaxGA := splitTorus.isFibrewiseMaximalTorus_affineBaseChangedTorusHom I G i b hmaxG
  have hmaxHA := splitTorus.isFibrewiseMaximalTorus_affineBaseChangedTorusHom I' H j b hmaxH
  have hiA := splitTorus.isClosedSubgroup_affineBaseChangedTorusHom I G i b hi
  have hjA := splitTorus.isClosedSubgroup_affineBaseChangedTorusHom I' H j b hj
  have hfreePA := fun α =>
    splitTorus.exponentWeightLine_affineBaseChange I G i b (P.root α) (hfreeP α)
  have hfreeQA := fun α =>
    splitTorus.exponentWeightLine_affineBaseChange I' H j b (Q.root α) (hfreeQ α)
  exact @SuppliedRootIsogeny.fppfLocallyTorusConjugate_of_commonRootDatumTorusMap
    (U.X a) _ I I' J J' _ _ _ _
    ((baseChange b).obj G) ((baseChange b).obj H) hGAff hHAff P Q _ _
    ((splitTorus.baseChangeIso b I).inv ≫ (baseChange b).map i)
    ((splitTorus.baseChangeIso b I').inv ≫ (baseChange b).map j)
    hPA hQA ((baseChange b).map phi) ((baseChange b).map Phi) hfinphiA hfinPhiA
    (hH.baseChange b) hmaxHA (hG.baseChange b) hiA hjA hmaxGA hfreePA hfreeQA (hU a)

/-- The unchanged general-base rigidity proposition follows from the
explicit intrinsic compatibility proposition. -/
theorem reductiveIsogenyTorusRigidity_of_affineSplitSurjectionRootDatum
    (hAffine : AffineSplitSurjectionRootDatumStatement.{u}) :
    ReductiveIsogenyTorusRigidityStatement.{u} :=
  reductiveIsogenyTorusRigidity_of_coordinateSplit
    (coordinateSplitIsogenyTorusConjugacy_of_affineSplitSurjectionRootDatum hAffine)

end Langlands.GroupScheme

import Langlands.Representation.Aubert.General.RationalCorrectedOrbitConditionalBalance
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Langlands.GroupScheme.Rational.SplitTorusFactorization

/-! # Squared intersection modulus for corrected Aubert orbits -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme

namespace CorrectedOrbitCocharacterRealization

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] {i : T.toGrp ⟶ G}
    {ν : cocharacterLattice T} {I K : Finset (SimpleRoot i ν)}
    {m : rationalPoints G} (r : CorrectedOrbitCocharacterRealization i ν I K m)

local instance correctedOrbitModulusProofAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

local instance correctedOrbitModulusProofActingAffineHom :
    IsAffineHom r.actingScheme.X.hom :=
  (Dynamic.Affine.isClosedSubgroup_centralizerHom
    (CommGroupScheme.groupHom r.zeta ≫ i)).isAffineHom

/-- Restriction of rational characters from the represented common Levi to the
original maximal split torus is injective. -/
theorem characterRestrict_torusHom_injective (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) :
    Function.Injective (characterRestrict r.torusHom) := by
  have hj : IsClosedSubgroup r.actingHom :=
    Dynamic.Affine.isClosedSubgroup_centralizerHom (CommGroupScheme.groupHom r.zeta ≫ i)
  have hM : IsConnectedReductive r.actingScheme :=
    dynamicCentralizerReductive k G hG (CommGroupScheme.groupHom r.zeta ≫ i)
      r.actingScheme r.actingHom hj
      (Dynamic.Affine.isRepresentedBy_centralizerHom (CommGroupScheme.groupHom r.zeta ≫ i))
  have ht : IsMaximalSplitTorus (r.torusHom ≫ r.actingHom) := by
    rw [r.torusHom_comp]
    exact hi
  rw [injective_iff_map_eq_zero]
  intro χ hχ
  by_contra hne
  obtain ⟨A, a, ha, hχa⟩ := centralSplitTorusCharacter k r.actingScheme hM χ hne
  obtain ⟨g, hg⟩ := ha.exists_factor_of_isMaximalSplitTorus hj ht
  apply hχa
  rw [← hg, characterRestrict_comp, AddMonoidHom.comp_apply, hχ, map_zero]

end CorrectedOrbitCocharacterRealization

/-- The actual rational squared intersection-modulus identity `hD07`. -/
theorem rationalCorrectedOrbitSquaredModulus :
    RationalCorrectedOrbitSquaredModulusStatement.{u} := by
  intro k _ _ _ _ G hG T i hi _ _ _ ν hν hStandard _hOrder _hInter hRoots hN _hZ hU _hM _hUc
    _ _ CM cs _ _ _ I j hj m hm K hK l
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  have := hG.smooth
  let r := correctedOrbitCocharacterRealization i ν hStandard hG hi hν hN I K m hK
  exact r.squared_modulus_of_characterRestrict_injective hRoots hi.isSplitSubtorus.1
    (hU I) (hU K)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν K)
    hK (r.characterRestrict_torusHom_injective hG hi) l

end Langlands.Aubert.General.RationalPointFamily

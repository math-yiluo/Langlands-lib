import Langlands.BruhatTits.SpecialCompact.GeneralLinearIntegralParabolicsStatement
import Langlands.BruhatTits.SpecialCompact.ParabolicCompactFactorization
import Langlands.GroupScheme.IntegralModel.DynamicCentralizer
import Langlands.GroupScheme.IntegralModel.GeneralLinearStandardPoints
import Langlands.GroupScheme.IntegralModel.MaximalCompact
import Langlands.GroupScheme.IntegralModel.SchematicClosure
import Langlands.GroupScheme.Rational.GeneralLinearIndexing
import Langlands.GroupScheme.Rational.GeneralLinearProof
import Langlands.GroupScheme.Rational.RelativeWeylFaithfulness

/-! # Proof of integral Weyl representatives and standard parabolic factorization for `GL_N` -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme

namespace Langlands.BruhatTits.SpecialCompact

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (N : ℕ)

local notation "𝔾" => GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)
local notation "𝕋" => splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin N))
local notation "i" => GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of F)
local notation "M" => GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem integral_weyl_representatives : HasWeylRepresentatives i (M).integralPoints := by
  intro w
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective w
  obtain ⟨σ, hσ⟩ := GeneralLinear.exists_permutationAction_eq_weylAction F m
  refine ⟨GeneralLinear.permNormalizer F σ, ?_, ?_⟩
  · rw [GeneralLinear.mem_standardIntegralModel_integralPoints_iff]
    refine ⟨GeneralLinear.permGL ↥𝒪[F] σ, ?_⟩
    rw [GeneralLinear.map_permGL]
    change GeneralLinear.permGL F σ =
      GeneralLinear.rationalPointsEquiv N (CommRingCat.of F)
        (GeneralLinear.permPoint (CommRingCat.of F) σ)
    simp only [GeneralLinear.rationalPointsEquiv, MulEquiv.trans_apply,
      GeneralLinear.permPoint, MulEquiv.apply_symm_apply, GeneralLinear.glRingEquiv]
    exact (GeneralLinear.map_permGL (GeneralLinear.globalSectionsEquiv (CommRingCat.of F)).toRingHom
      σ).symm
  · apply (isSplitTorus_splitTorus _).relativeWeylLatticeAction_injective i
    rw [relativeWeylLatticeAction_mk, relativeWeylLatticeAction_mk,
      GeneralLinear.weylAction_permNormalizer, hσ]

private theorem integral_standardLevi_compact_open_maximal
    (ν : cocharacterLattice 𝕋) (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice 𝕋)) (hJ : J ⊆ simpleRelativeRoots i ν) :
    haveI : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
      (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
    IsCompactOpenMaximal F ((M).integralPoints.comap (rationalPoints.map (Standard.leviHom i ν J))) := by
  let L := Standard.leviScheme i ν J
  let j := Standard.leviHom i ν J
  have hj : IsClosedSubgroup j := Standard.isClosedSubgroup_leviHom i ν J
  let : IsAffineHom L.X.hom := hj.isAffineHom
  let : IsAffine (GeneralLinear.groupScheme (Fin N) (CommRingCat.of ↥𝒪[F])).X.left :=
    isAffine_of_isAffineHom
      (GeneralLinear.groupScheme (Fin N) (CommRingCat.of ↥𝒪[F])).X.hom
  have hG : IsConnectedReductive 𝔾 := isConnectedReductive_generalLinear F (Fin N)
  have hi : IsMaximalSplitTorus i := GeneralLinear.isMaximalSplitTorus_diagonalTorus F
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ := standardCocharacter F 𝔾 hG 𝕋 i hi ν hν J hJ
  let weights := GeneralLinear.cocharacterCoordEquiv (Fin N) F ζ
  let χ := GeneralLinear.diagonalCocharacter (Fin N) (CommRingCat.of ↥𝒪[F]) weights
  have hχ : (M).genericCocharacter χ = CommGroupScheme.groupHom ζ ≫ i := by
    dsimp only [χ, IntegralModel.genericCocharacter, GeneralLinear.standardIntegralModel]
    rw [GeneralLinear.baseChangeCocharacter_diagonalCocharacter]
    simpa only [weights, GeneralLinear.cocharacterOfWeights, LinearEquiv.symm_apply_apply] using
      (GeneralLinear.cocharacterOfWeights_comp_diagonalTorus F weights).symm
  have hrep : (Dynamic.centralizer ((M).genericCocharacter χ)).IsRepresentedBy j := by
    rw [hχ, ← (hcompare ζ hζ).2.1]
    exact Standard.isRepresentedBy_leviHom i ν J
  have hgeneric : SubgroupFunctor.range (j ≫ (M).genericIso.inv) =
      Dynamic.centralizer (Dynamic.baseChangeCocharacter (Spec.algebraMap ↥𝒪[F] F) χ) :=
    (hrep.comp_iso (M).genericIso.symm).2.trans (Dynamic.centralizer_eq_comap_of_iso _ (M).genericIso).symm
  let : Smooth (M).group.X.hom := GeneralLinear.standardIntegralModel_isSmooth 𝒪[F] F (Fin N)
  let Z := IntegralModel.DynamicCentralizer.model M χ j hj hgeneric
  let inclusion := IntegralModel.DynamicCentralizer.inclusion M χ j hj hgeneric
  have hpoints : Z.integralPoints = (M).integralPoints.comap (rationalPoints.map j) :=
    inclusion.integralPoints_eq_comap
      (IntegralModel.DynamicCentralizer.isClosedSubgroup_inclusion M χ j hj hgeneric)
  have hL : IsConnectedReductive L := dynamicCentralizerReductive F 𝔾 hG
    ((M).genericCocharacter χ) L j hj hrep
  let b := Spec.algebraMap ↥𝒪[F] 𝓀[F]
  have hspecial : IsConnectedReductive ((GroupScheme.baseChange b).obj (M).group) :=
    IsConnectedReductive.of_iso (GeneralLinear.baseChangeIso (Fin N) b)
      (isConnectedReductive_generalLinear 𝓀[F] (Fin N))
  have hZspecial : IsConnectedReductive ((GroupScheme.baseChange b).obj Z.group) :=
    dynamicCentralizerReductive 𝓀[F] _ hspecial (Dynamic.baseChangeCocharacter b χ) _ _
      ((Dynamic.Affine.isClosedSubgroup_centralizerHom χ).baseChange b)
      (Dynamic.isRepresentedBy_centralizer_baseChange b χ
        (Dynamic.Affine.isRepresentedBy_centralizerHom χ))
  change IsCompactOpenMaximal F ((M).integralPoints.comap (rationalPoints.map j))
  rw [← hpoints]
  let : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  obtain ⟨hK, hmax⟩ := IntegralModel.maximalCompactStatement F L hL Z hZspecial
  exact ⟨hK, Z.isOpen_integralPoints_localField, hK, fun C hC hle => (hmax C hC hle).le⟩

/-- The standard integral subgroup meets the Weyl classes and admits all of
Renard's standard parabolic factorizations. -/
theorem generalLinearIntegralParabolics : GeneralLinearIntegralParabolicsStatement.{u} := by
  intro F _ _ _ _ N ν
  dsimp only
  intro hν
  refine ⟨integral_weyl_representatives F N, ?_⟩
  let G := GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)
  let T := GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of F)
  let model := GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact hasParabolicFactorization_of_maximal_compact_levis
    (isConnectedReductive_generalLinear F (Fin N)) T
    (GeneralLinear.isMaximalSplitTorus_diagonalTorus F) ν hν model.integralPoints
    model.isCompact_integralPoints_localField (integral_standardLevi_compact_open_maximal F N ν hν)

end Langlands.BruhatTits.SpecialCompact

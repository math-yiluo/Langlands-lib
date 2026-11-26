import Langlands.BruhatTits.SpecialCompact.GeneralLinearIntegralLeviIwasawaStatement
import Langlands.GroupScheme.IntegralModel.DynamicCentralizer
import Langlands.GroupScheme.IntegralModel.MaximalCompact
import Langlands.GroupScheme.IntegralModel.SchematicClosure
import Langlands.GroupScheme.Dynamic.PresentationComparison
import Langlands.GroupScheme.Rational.GeneralLinearIndexing
import Langlands.GroupScheme.Rational.GeneralLinearProof
import Langlands.GroupScheme.Rational.MinimalStandardDynamicComparison
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Rational.StandardLeviNestedTransport

/-! # Iwasawa decomposition for the inherited compact in a standard Levi of `GL_N` -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise ValuativeRel
open Langlands.GroupScheme

namespace Langlands.BruhatTits.SpecialCompact

/-- The inherited compact is maximal and open, and it supplies both Iwasawa
products for the minimal standard parabolic of the Levi. -/
theorem generalLinearIntegralLeviIwasawa : GeneralLinearIntegralLeviIwasawaStatement.{u} := by
  intro F _ _ _ _ N ν
  dsimp only
  intro hν J hJ
  let G := GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)
  let T := splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin N))
  let i := GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of F)
  let M := GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)
  let L := Standard.leviScheme i ν J
  let j := Standard.leviHom i ν J
  have hj : IsClosedSubgroup j := Standard.isClosedSubgroup_leviHom i ν J
  let : IsAffineHom L.X.hom := hj.isAffineHom
  let : IsAffine (GeneralLinear.groupScheme (Fin N) (CommRingCat.of ↥𝒪[F])).X.left :=
    isAffine_of_isAffineHom
      (GeneralLinear.groupScheme (Fin N) (CommRingCat.of ↥𝒪[F])).X.hom
  have hG : IsConnectedReductive G := isConnectedReductive_generalLinear F (Fin N)
  have hi : IsMaximalSplitTorus i := GeneralLinear.isMaximalSplitTorus_diagonalTorus F
  let lift (c : cocharacterLattice T) :=
    GeneralLinear.diagonalCocharacter (Fin N) (CommRingCat.of ↥𝒪[F])
      (GeneralLinear.cocharacterCoordEquiv (Fin N) F c)
  have hlift (c : cocharacterLattice T) :
      M.genericCocharacter (lift c) = CommGroupScheme.groupHom c ≫ i := by
    dsimp only [M, lift, IntegralModel.genericCocharacter, GeneralLinear.standardIntegralModel]
    rw [GeneralLinear.baseChangeCocharacter_diagonalCocharacter]
    simpa only [i, GeneralLinear.cocharacterOfWeights, LinearEquiv.symm_apply_apply] using
      (GeneralLinear.cocharacterOfWeights_comp_diagonalTorus F
        (GeneralLinear.cocharacterCoordEquiv (Fin N) F c)).symm
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ := standardCocharacter F G hG T i hi ν hν J hJ
  let weights := GeneralLinear.cocharacterCoordEquiv (Fin N) F ζ
  let χ := lift ζ
  have hrep : (Dynamic.centralizer (M.genericCocharacter χ)).IsRepresentedBy j := by
    rw [hlift ζ, ← (hcompare ζ hζ).2.1]
    exact Standard.isRepresentedBy_leviHom i ν J
  have hgeneric : SubgroupFunctor.range (j ≫ M.genericIso.inv) =
      Dynamic.centralizer (Dynamic.baseChangeCocharacter (Spec.algebraMap ↥𝒪[F] F) χ) :=
    (hrep.comp_iso M.genericIso.symm).2.trans (Dynamic.centralizer_eq_comap_of_iso _ M.genericIso).symm
  let : Smooth M.group.X.hom := GeneralLinear.standardIntegralModel_isSmooth 𝒪[F] F (Fin N)
  let Z := IntegralModel.DynamicCentralizer.model M χ j hj hgeneric
  let inclusion : Z.Hom M j := IntegralModel.DynamicCentralizer.inclusion M χ j hj hgeneric
  have hpoints : Z.integralPoints = M.integralPoints.comap (rationalPoints.map j) :=
    inclusion.integralPoints_eq_comap
      (IntegralModel.DynamicCentralizer.isClosedSubgroup_inclusion M χ j hj hgeneric)
  have hL : IsConnectedReductive L := dynamicCentralizerReductive F G hG
    (M.genericCocharacter χ) L j hj hrep
  let b := Spec.algebraMap ↥𝒪[F] 𝓀[F]
  have hspecial : IsConnectedReductive ((GroupScheme.baseChange b).obj M.group) :=
    IsConnectedReductive.of_iso (GeneralLinear.baseChangeIso (Fin N) b)
      (isConnectedReductive_generalLinear 𝓀[F] (Fin N))
  have hZspecial : IsConnectedReductive ((GroupScheme.baseChange b).obj Z.group) :=
    dynamicCentralizerReductive 𝓀[F] _ hspecial (Dynamic.baseChangeCocharacter b χ) _ _
      ((Dynamic.Affine.isClosedSubgroup_centralizerHom χ).baseChange b)
      (Dynamic.isRepresentedBy_centralizer_baseChange b χ
        (Dynamic.Affine.isRepresentedBy_centralizerHom χ))
  let iL := Standard.leviTorusHom i ν J
  let P := standardParabolicPoints iL ν ∅
  change IsCompactOpenMaximal F (M.integralPoints.comap (rationalPoints.map j)) ∧
    Iwasawa.PointProductEqualities P (M.integralPoints.comap (rationalPoints.map j))
  rw [← hpoints]
  let : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  obtain ⟨hK, hmax⟩ := IntegralModel.maximalCompactStatement F L hL Z hZspecial
  refine ⟨⟨hK, Z.isOpen_integralPoints_localField, hK, fun C hC hle => (hmax C hC hle).le⟩, ?_⟩
  let χν := lift ν
  have hfactor : SubgroupFunctor.range χν ≤ Dynamic.centralizer χ := by
    change SubgroupFunctor.range χν ≤ Dynamic.centralizer
      (GeneralLinear.diagonalCocharacter (Fin N) (CommRingCat.of ↥𝒪[F]) weights)
    rw [GeneralLinear.centralizer_diagonalCocharacter]
    intro U g hg
    obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
    apply (GeneralLinear.mem_blockLevi (e := weights)).mpr
    intro a b hab
    dsimp only [χν, lift]
    rw [GeneralLinear.pointsEquiv_diagonalCocharacter, GeneralLinear.coe_diagonalUnits,
      Matrix.diagonal_apply_ne _ (fun e => hab (congrArg weights e))]
  let hrepχ := Dynamic.Affine.isRepresentedBy_centralizerHom χ
  let χL : (Gm (Spec (CommRingCat.of ↥𝒪[F]))).toGrp ⟶ Z.group :=
    hrepχ.factorHom χν hfactor
  have hχL : χL ≫ inclusion.hom = χν := hrepχ.factorHom_comp χν hfactor
  have hgencomp : Z.genericCocharacter χL ≫ j = M.genericCocharacter χν := by
    unfold IntegralModel.genericCocharacter
    rw [Category.assoc, ← inclusion.generic_comm, ← Category.assoc,
      ← Dynamic.baseChangeCocharacter_comp_hom, hχL]
  have hgen : Z.genericCocharacter χL = CommGroupScheme.groupHom ν ≫ iL := by
    have : Mono j.hom.hom := hrep.1
    apply Grp.hom_ext
    apply (cancel_mono j.hom.hom).mp
    rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, hgencomp, hlift ν, Category.assoc]
    exact congrArg (fun f : T.toGrp ⟶ G => (CommGroupScheme.groupHom ν ≫ f).hom.hom)
      (Standard.leviTorusHom_comp i ν J).symm
  obtain ⟨-, hiL, hνL, -⟩ := StandardLeviNested.leviScheme_rankPackage hG i hi ν hν J hJ
  have hP : P = (rationalPoints.map (Z.cellParabolicHom χL)).range := by
    change (standardParabolic iL ν ∅).rationalPoints = _
    rw [standardParabolic_empty_eq_dynamic_of_generic iL ν hL hiL hνL, ← hgen]
    exact SubgroupFunctor.rationalPoints_eq_range (Z.isRepresentedBy_cellParabolicHom χL)
  have hproduct : (P : Set (rationalPoints L)) *
      (Z.integralPoints : Set (rationalPoints L)) = Set.univ := by
    rw [hP]
    exact Z.cellIwasawa χL hL hZspecial
  refine ⟨hproduct.symm, Set.Subset.antisymm (fun g _ => ?_) (Set.subset_univ _)⟩
  obtain ⟨p, hp, k, hk, heq⟩ := Set.mem_mul.mp
    (hproduct.symm ▸ Set.mem_univ (g⁻¹))
  have hg : g = k⁻¹ * p⁻¹ := by rw [← mul_inv_rev, heq, inv_inv]
  rw [hg]
  exact Set.mul_mem_mul (Z.integralPoints.inv_mem hk) (P.inv_mem hp)

end Langlands.BruhatTits.SpecialCompact

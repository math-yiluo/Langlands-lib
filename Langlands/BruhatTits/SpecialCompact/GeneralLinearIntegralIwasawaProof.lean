import Langlands.BruhatTits.SpecialCompact.GeneralLinearIntegralIwasawaStatement
import Langlands.GroupScheme.IntegralModel.IwasawaCellDynamic
import Langlands.GroupScheme.IntegralModel.MaximalCompact
import Langlands.GroupScheme.Rational.GeneralLinearIndexing
import Langlands.GroupScheme.Rational.GeneralLinearProof
import Langlands.GroupScheme.Rational.MinimalStandardDynamicComparison
import Langlands.GroupScheme.Rational.ParabolicPointConjugation

/-! # Proof of Iwasawa decomposition at the standard integral subgroup of `GL_N` -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise ValuativeRel
open Langlands.GroupScheme

namespace Langlands.BruhatTits.SpecialCompact

/-- The standard integral subgroup is maximal compact and supplies the two minimal
Iwasawa products. -/
theorem generalLinearIntegralIwasawa : GeneralLinearIntegralIwasawaStatement.{u} := by
  intro F _ _ _ _ N ν
  dsimp only
  intro hν
  let G := GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)
  let i := GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of F)
  let M := GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)
  change IsCompactOpenMaximal F M.integralPoints ∧
    Iwasawa.PointProductEqualities (standardParabolicPoints i ν ∅) M.integralPoints
  have hG : IsConnectedReductive G := isConnectedReductive_generalLinear F (Fin N)
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hspecial : IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group) :=
    IsConnectedReductive.of_iso (GeneralLinear.baseChangeIso (Fin N) _)
      (isConnectedReductive_generalLinear 𝓀[F] (Fin N))
  obtain ⟨hK, hmax⟩ := IntegralModel.maximalCompactStatement F G hG M hspecial
  refine ⟨⟨hK, M.isOpen_integralPoints_localField, hK, fun L hL hle => (hmax L hL hle).le⟩, ?_⟩
  let w := GeneralLinear.cocharacterCoordEquiv (Fin N) F ν
  let χ := GeneralLinear.diagonalCocharacter (Fin N) (CommRingCat.of ↥𝒪[F]) w
  have hχ : M.genericCocharacter χ = CommGroupScheme.groupHom ν ≫ i := by
    dsimp only [M, χ, IntegralModel.genericCocharacter, GeneralLinear.standardIntegralModel]
    rw [GeneralLinear.baseChangeCocharacter_diagonalCocharacter]
    simpa only [i, w, GeneralLinear.cocharacterOfWeights, LinearEquiv.symm_apply_apply] using
      (GeneralLinear.cocharacterOfWeights_comp_diagonalTorus F w).symm
  have hi : IsMaximalSplitTorus i := GeneralLinear.isMaximalSplitTorus_diagonalTorus F
  let P := standardParabolicPoints i ν ∅
  have hP : P = (rationalPoints.map (M.cellParabolicHom χ)).range := by
    change (standardParabolic i ν ∅).rationalPoints = _
    rw [standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν, ← hχ]
    exact SubgroupFunctor.rationalPoints_eq_range (M.isRepresentedBy_cellParabolicHom χ)
  have hproduct :
      (P : Set (rationalPoints G)) * (M.integralPoints : Set (rationalPoints G)) = Set.univ := by
    rw [hP]
    exact M.cellIwasawa χ hG hspecial
  refine ⟨hproduct.symm, Set.Subset.antisymm (fun g _ => ?_) (Set.subset_univ _)⟩
  obtain ⟨p, hp, k, hk, heq⟩ := Set.mem_mul.mp
    (hproduct.symm ▸ Set.mem_univ (g⁻¹))
  have hg : g = k⁻¹ * p⁻¹ := by rw [← mul_inv_rev, heq, inv_inv]
  rw [hg]
  exact Set.mul_mem_mul (M.integralPoints.inv_mem hk) (P.inv_mem hp)

end Langlands.BruhatTits.SpecialCompact

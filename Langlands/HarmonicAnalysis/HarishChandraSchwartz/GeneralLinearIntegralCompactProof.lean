import Langlands.HarmonicAnalysis.HarishChandraSchwartz.GeneralLinearIntegralCompactStatement
import Langlands.BruhatTits.SpecialCompact.AvailableCompactCore
import Langlands.GroupScheme.IntegralModel.GeneralLinearStandardPoints
import Langlands.GroupScheme.IntegralModel.MaximalCompact
import Langlands.GroupScheme.Rational.GeneralLinearGenericCentralizer
import Langlands.GroupScheme.Rational.GeneralLinearProof
import Langlands.GroupScheme.Rational.GeneralLinearStandardParabolicProof
import Langlands.GroupScheme.Reductive.GeneralLinearIsConnectedReductiveProof
import Langlands.Group.GL.ParabolicModularCharacter

/-! # Standard integral compact and Iwasawa factorization on actual GL points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel Pointwise
open Langlands.GroupScheme Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

open GroupScheme.GeneralLinear
open Langlands.GeneralLinear

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (N : ℕ)

local notation "G" => groupScheme (Fin N) (CommRingCat.of F)
local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin N))
local notation "iD" => diagonalTorus (Fin N) (CommRingCat.of F)
set_option quotPrecheck false in
local notation "𝓜" => standardIntegralModel ↥𝒪[F] F (Fin N)
local notation "K₀" => IntegralModel.integralPoints 𝓜
local notation "eG" => rationalPointsEquiv N (CommRingCat.of F)
local notation "Kmat" => Iwasawa.integralRange (ValuativeRel.valuation F) N

private theorem integralCompactMaximal : IsCompactOpenMaximal F K₀ := by
  have hG : IsConnectedReductive G :=
    GroupScheme.GeneralLinear.isConnectedReductiveStatement F (Fin N)
  have hspecial : IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj (𝓜).group) :=
    IsConnectedReductive.of_iso (baseChangeIso (Fin N) (Spec.algebraMap ↥𝒪[F] 𝓀[F]))
      (GroupScheme.GeneralLinear.isConnectedReductiveStatement 𝓀[F] (Fin N))
  obtain ⟨hc, hmax⟩ := IntegralModel.maximalCompactStatement F G hG 𝓜 hspecial
  refine ⟨hc, (𝓜).isOpen_integralPoints_localField, hc, fun L hL hKL => ?_⟩
  exact (hmax L hL hKL).le

set_option maxHeartbeats 800000 in
omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem integralWeylRepresentatives : HasWeylRepresentatives iD K₀ := by
  intro w
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective w
  obtain ⟨s, hs⟩ := exists_permutationAction_eq_weylAction F m
  refine ⟨permNormalizer F s, ?_, ?_⟩
  · apply (mem_standardIntegralModel_integralPoints_iff ↥𝒪[F] F _).mpr
    refine ⟨GroupScheme.GeneralLinear.permGL ↥𝒪[F] s, ?_⟩
    change Matrix.GeneralLinearGroup.map _ (GroupScheme.GeneralLinear.permGL ↥𝒪[F] s) =
      eG (permPoint (CommRingCat.of F) s)
    rw [map_permGL]
    change GroupScheme.GeneralLinear.permGL F s = (eG).toMonoidHom _
    rw [rationalPointsEquiv_toMonoidHom, MonoidHom.comp_apply, permPoint,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact (map_permGL _ s).symm
  · apply relativeWeylAction_diagonalTorus_injective F
    apply LinearEquiv.ext
    intro x
    apply spanCoord_injective F
    rw [spanCoord_relativeWeylAction_mk F (weylAction_permNormalizer F s).symm,
      spanCoord_relativeWeylAction_mk F hs]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem singletonRoots :
    blockSimpleRoots F (BlockShape.singletons N) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro _ ⟨j, hj, rfl⟩
  have h := (blockIndex_adjacent_eq_iff (BlockShape.singletons N) j).mpr
    ((BlockShape.mem_uncuts_iff _ _).mp hj)
  have hsingle (i : Fin N) : Langlands.Geometric.blockIndex (BlockShape.singletons N) i = i := by
    have hi := Langlands.Geometric.blockIndex_index (BlockShape.singletons N) i (0 : Fin 1)
    rw [BlockShape.singletons_index (n := N) i (0 : Fin 1)] at hi
    exact hi
  rw [hsingle, hsingle] at h
  exact (adjacentRootPair j).property h

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem integralIwasawa (ν : cocharacterLattice 𝔻)
    (hν : StrictAnti (cocharacterCoordEquiv (Fin N) F ν)) :
    IsIwasawaPair (standardParabolicPoints iD ν ∅) K₀ := by
  have hgeneric := (isGenericCocharacter_diagonalTorus_iff F ν).mpr hν.injective
  have hP := ((generalLinearStandardParabolic F N ν hgeneric hν).2.1
    (BlockShape.singletons N)).2.2.2.1
  rw [singletonRoots, ← rationalPointsEquiv_toMonoidHom] at hP
  intro g
  obtain ⟨k, hk, hb⟩ := Iwasawa.exists_mul_upperTriangular (ValuativeRel.valuation F) N (eG g)
  refine ⟨(eG).symm (eG g * k), ?_, (eG).symm k⁻¹, ?_, ?_⟩
  · rw [hP]
    change eG ((eG).symm _) ∈ (BlockShape.singletons N).parabolic F
    exact (by rwa [MulEquiv.apply_symm_apply, BlockShape.singletons_mem_parabolic_iff])
  · apply (mem_standardIntegralModel_integralPoints_iff ↥𝒪[F] F _).mpr
    rw [MulEquiv.apply_symm_apply]
    exact (Kmat).inv_mem hk
  · apply (eG).injective
    rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, mul_inv_cancel_right]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem blockProjection_integral (B : BlockShape N) (p : B.parabolic F)
    (hp : (p : Langlands.GeneralLinear N F) ∈ Kmat) :
    B.leviEmbedding F (B.leviProjection F p) ∈ Kmat := by
  cases N with
  | zero =>
    have h : B.leviEmbedding F (B.leviProjection F p) = 1 := by
      apply Units.ext
      ext i
      exact Fin.elim0 i
    rw [h]
    exact one_mem _
  | succ n =>
    rw [Iwasawa.integralRange_succ, ← Conductor.levelSubgroup_zero] at hp ⊢
    exact B.leviEmbedding_leviProjection_mem p hp

set_option maxHeartbeats 1000000 in
omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem integralParabolicFactorization (ν : cocharacterLattice 𝔻)
    (hν : StrictAnti (cocharacterCoordEquiv (Fin N) F ν)) :
    HasParabolicFactorization iD ν K₀ := by
  have hgeneric := (isGenericCocharacter_diagonalTorus_iff F ν).mpr hν.injective
  obtain ⟨_, hmatrix, hshapes⟩ := generalLinearStandardParabolic F N ν hgeneric hν
  intro J hJ
  obtain ⟨B, rfl, -⟩ := hshapes J hJ
  obtain ⟨_, _, _, hP, hM, hU⟩ := hmatrix B
  rw [← rationalPointsEquiv_toMonoidHom] at hP hM hU
  apply Set.Subset.antisymm
  · intro g hg
    obtain ⟨hgK, hgP⟩ := Subgroup.mem_inf.mp hg
    have hgP' : eG g ∈ B.parabolic F := by rwa [hP] at hgP
    let p : B.parabolic F := ⟨eG g, hgP'⟩
    let m := B.leviInParabolic F (B.leviProjection F p)
    let v := m⁻¹ * p
    have hvU : v ∈ B.unipotentRadical F := by
      change B.leviProjection F (m⁻¹ * p) = 1
      rw [map_mul, map_inv, show B.leviProjection F m = B.leviProjection F p from
        B.leviProjection_section F _, inv_mul_cancel]
    have hpK : (p : Langlands.GeneralLinear N F) ∈ Kmat :=
      (mem_standardIntegralModel_integralPoints_iff ↥𝒪[F] F _).mp hgK
    have hmK : (m : Langlands.GeneralLinear N F) ∈ Kmat :=
      blockProjection_integral F N B p hpK
    have hvK : (v : Langlands.GeneralLinear N F) ∈ Kmat :=
      (Kmat).mul_mem ((Kmat).inv_mem hmK) hpK
    have hcompact {x : Langlands.GeneralLinear N F} (hx : x ∈ Kmat) : (eG).symm x ∈ K₀ :=
      (mem_standardIntegralModel_integralPoints_iff ↥𝒪[F] F _).mpr
        (by simpa only [MulEquiv.apply_symm_apply])
    apply Set.mem_mul.mpr
    refine ⟨(eG).symm m, ⟨hcompact hmK, ?_⟩, (eG).symm v, ⟨hcompact hvK, ?_⟩, ?_⟩
    · rw [hM]
      change eG ((eG).symm m) ∈ B.leviSubgroup F
      rw [MulEquiv.apply_symm_apply]
      exact ⟨B.leviProjection F p, rfl⟩
    · rw [hU]
      change eG ((eG).symm v) ∈ B.unipotentSubgroup F
      rw [MulEquiv.apply_symm_apply]
      exact ⟨v, hvU, rfl⟩
    · apply (eG).injective
      simp only [map_mul, MulEquiv.apply_symm_apply, v, Subgroup.coe_mul, Subgroup.coe_inv]
      exact mul_inv_cancel_left _ _
  · intro g hg
    obtain ⟨m, hm, v, hv, rfl⟩ := Set.mem_mul.mp hg
    exact ⟨(K₀).mul_mem hm.1 hv.1,
      (standardParabolicPoints iD ν (blockSimpleRoots F B)).mul_mem
        (standardLevi_le_standardParabolic iD ν (blockSimpleRoots F B) _ hm.2)
        (standardUnipotent_le_standardParabolic iD ν (blockSimpleRoots F B) _ hv.2)⟩

/-- The integral-model subgroup has the standard compact and Iwasawa properties. -/
theorem generalLinearIntegralCompact : GeneralLinearIntegralCompactStatement.{u} := by
  intro F _ _ _ _ N
  dsimp only
  intro ν hν
  have hG := GroupScheme.GeneralLinear.isConnectedReductiveStatement F (Fin N)
  have hi := isMaximalSplitTorus_diagonalTorus (n := Fin N) F
  have hgeneric := (isGenericCocharacter_diagonalTorus_iff F ν).mpr hν.injective
  have hK := integralCompactMaximal F N
  have hpar := integralParabolicFactorization F N ν hν
  have hI := integralIwasawa F N ν hν
  exact ⟨⟨isBoundedOpenMaximal_of_isCompactOpenMaximal hG hK, hK,
      integralWeylRepresentatives F N, hpar⟩, hI,
    standardLeviIwasawaFactorsAt_of_factorization hG hi hgeneric _ hI hpar⟩

end Langlands.HarishChandraSchwartz

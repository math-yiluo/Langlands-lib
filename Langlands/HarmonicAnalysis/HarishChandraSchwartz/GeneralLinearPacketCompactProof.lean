import Langlands.HarmonicAnalysis.HarishChandraSchwartz.GeneralLinearPacketCompactStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.GeneralLinearCartanCoveringProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.GeneralLinearIntegralCompactProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.GeneralLinearSimultaneousBasisProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.GeneralLinearSourceCompactProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiChangeMinimal

/-! # The common standard compact for general linear wave packets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel Pointwise
open Langlands.GroupScheme Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact Langlands.BruhatTits.Iwasawa

namespace Langlands.HarishChandraSchwartz

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace

private theorem products_of_pair {F : Type u} [Field F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    {P K : Subgroup (rationalPoints G)} (h : IsIwasawaPair P K) :
    PointProductEqualities P K := by
  constructor
  · apply Set.Subset.antisymm (fun g _ => ?_) (Set.subset_univ _)
    obtain ⟨p, hp, k, hk, rfl⟩ := h g
    exact Set.mul_mem_mul hp hk
  · apply Set.Subset.antisymm (fun g _ => ?_) (Set.subset_univ _)
    obtain ⟨p, hp, k, hk, heq⟩ := h g⁻¹
    have hg : g = k⁻¹ * p⁻¹ := by rw [← mul_inv_rev, ← heq, inv_inv]
    rw [hg]
    exact Set.mul_mem_mul (K.inv_mem hk) (P.inv_mem hp)

set_option maxHeartbeats 1000000 in
private theorem products_of_minimalPair {F : Type u} [Field F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
    {K : Subgroup (rationalPoints G)}
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K) :
    ParabolicPointProductFamily i ν K := by
  let : Smooth G.X.hom := hG.smooth
  have hMin : IsMinimalParabolicFunctor (standardParabolic i ν ∅) := by
    rw [standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν]
    exact genericMinimalParabolic F G hG S i hi ν hν
  have algProducts : AlgebraicParabolicProducts K := by
    intro P j hj
    have hP : IsParabolicFunctor (SubgroupFunctor.range j) :=
      (isParabolicFunctor_range_iff hj.isClosedSubgroup).mpr hj
    obtain ⟨Q, hQ, hle⟩ := IsParabolicFunctor.exists_minimal_le_of_statement
      parabolicContainsMinimalStatement hG hP
    obtain ⟨g, hg⟩ := IsMinimalParabolicFunctor.isRationallyConjugate_of_statement
      minimalParabolicConjugacy hG hMin hQ
    have hconj (x : rationalPoints G) :
        x ∈ standardParabolicPoints i ν ∅ ↔ g * x * g⁻¹ ∈ Q.rationalPoints := by
      change x ∈ (standardParabolic i ν ∅).rationalPoints ↔ _
      rw [hg]
      exact SubgroupFunctor.mem_rationalPoints_comap_innerIso_hom Q g x
    obtain ⟨k, hk, hconjK⟩ := hPK.exists_mem_conjugator ⟨g, hconj⟩
    exact products_of_pair ((hPK.of_mem_conjugator hk hconjK).mono (hle (Over.mk (𝟙 _))))
  have dynProducts : DynamicParabolicProducts K := by
    intro χ
    have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    have hp := Dynamic.Affine.isParabolicSubgroup_parabolicHom_of_parabolicDynamic
      parabolicDynamic hG χ
    change PointProductEqualities (Dynamic.parabolic χ).rationalPoints K
    rw [SubgroupFunctor.rationalPoints_eq_range (Dynamic.Affine.isRepresentedBy_parabolicHom χ)]
    exact algProducts _ _ hp
  have stdPair (J : Set (characterLattice S)) (hJ : J ⊆ simpleRelativeRoots i ν) :
      IsIwasawaPair (standardParabolicPoints i ν J) K :=
    hPK.mono (standardParabolicPoints_empty_le hG hi hν hJ)
  refine ⟨algProducts, dynProducts, fun J hJ => products_of_pair (stdPair J hJ),
    fun P j hj g => algProducts P _ (hj.comp_iso (G.innerIso g)), fun χ g => dynProducts _, ?_⟩
  intro J hJ g
  change PointProductEqualities ((standardParabolic i ν J).comap (G.innerIso g).inv).rationalPoints K
  rw [standardParabolicPoints_comap_innerIso_inv]
  have hconj (x : rationalPoints G) :
      x ∈ standardParabolicPoints i ν J ↔
        MulAut.conj g x ∈ (standardParabolicPoints i ν J).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  obtain ⟨k, hk, hconjK⟩ := (stdPair J hJ).exists_mem_conjugator ⟨g, hconj⟩
  exact products_of_pair ((stdPair J hJ).of_mem_conjugator hk hconjK)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1600000 in
/-- The standard integral subgroup supplies the packet compact for the general linear group. -/
theorem generalLinearPacketCompact : GeneralLinearPacketCompactStatement.{u} := by
  intro F _ _ _ _ N
  dsimp only
  intro ν hν
  let G := GroupScheme.GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)
  let S := splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin N))
  let i := GroupScheme.GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of F)
  let M := GroupScheme.GeneralLinear.standardIntegralModel ↥𝒪[F] F (Fin N)
  have hG : IsConnectedReductive G :=
    GroupScheme.GeneralLinear.isConnectedReductiveStatement F (Fin N)
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have hi : IsMaximalSplitTorus (T := S) i :=
    GroupScheme.GeneralLinear.isMaximalSplitTorus_diagonalTorus (n := Fin N) F
  have hgen : IsGenericCocharacter i ν :=
    (GroupScheme.GeneralLinear.isGenericCocharacter_diagonalTorus_iff F ν).mpr hν.injective
  obtain ⟨hprops, hPK, _⟩ := generalLinearIntegralCompact F N ν hν
  obtain ⟨hC, hLeviC⟩ := generalLinearCartanCovering F N ν hν
  obtain ⟨hK, _, C, D, x, hA, hB, hx, hstab⟩ := generalLinearSourceCompactGeometry F N
  let L : OpenSubgroup (rationalPoints G) := ⟨M.integralPoints, hK.2.1⟩
  have hspecial : WeakExpansion.IsSpecialVertexCompact ν hi L :=
    ⟨C, D, hA, hB, x, hx, hstab.symm ▸ hprops, hstab⟩
  exact ⟨L, rfl, hK.1, hspecial, products_of_minimalPair hG hi hgen hPK,
    generalLinearSimultaneousBasis F N ν hgen, hC, hLeviC⟩

end Langlands.HarishChandraSchwartz

import Langlands.HarmonicAnalysis.HarishChandraSchwartz.GeneralLinearGenericCartanCoveringStatement
import Langlands.BruhatTits.SpecialCompact.GeneralLinearIntegralCartanProof
import Langlands.BruhatTits.SpecialCompact.GeneralLinearIntegralLeviCartanProof
import Langlands.Representation.Aubert.General.RationalCartanLatticeModel
import Langlands.Representation.Aubert.General.RationalIwasawaCartan

/-! # Cartan coverings for any generic diagonal cocharacter of `GL_n` -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.Plancherel.RenardCartan
open scoped CategoryTheory.MonObj ValuativeRel

namespace Langlands.HarishChandraSchwartz

open BruhatTits.SpecialCompact
open Aubert.General.RationalPointFamily (rationalPoints_map_comp_apply)

universe u

private theorem uniformizerSection_mem_CAplus {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    {J : Set (characterLattice T)} {c : cocharacterLattice T}
    (hc : ∀ α ∈ J, 0 ≤ latticePairing T α c) :
    uniformizerSection T (Multiplicative.ofAdd c) ∈ CocharacterUniformizer.CAplus F T J := by
  refine ⟨⟨Multiplicative.ofAdd c, rfl⟩, fun α hα => ?_⟩
  rw [uniformizerSection_eq_latticeSection, CocharacterUniformizer.characterNorm_latticeSection]
  have hq : (1 : ℝ) ≤ LocalField.residueCardinality F := by
    exact_mod_cast (LocalField.residueCardinality_gt_one F).le
  exact zpow_le_one_of_nonpos₀ hq (neg_nonpos.mpr (hc α hα))

/-- The two Cartan bijections give the coverings at the same integral subgroup. -/
theorem generalLinearGenericCartanCovering : GeneralLinearGenericCartanCoveringStatement.{u} := by
  intro F _ _ _ _ N i K ν hν
  classical
  let T := splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift.{u} (Fin N))
  let G := GroupScheme.GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)
  let : Smooth G.X.hom := GroupScheme.GeneralLinear.smoothStatement (Fin N) (CommRingCat.of F)
  constructor
  · refine ⟨{1}, fun g => ?_⟩
    obtain ⟨x, hx⟩ := (generalLinearIntegralCartan F N ν hν).2 (DoubleCoset.mk K K g)
    obtain ⟨k₁, hk₁, k₂, hk₂, hg⟩ := DoubleCoset.eq.mp hx
    obtain ⟨c, hc, hcx⟩ := (mem_C0Plus T i _ x.val).mp x.property
    let a := uniformizerSection T (Multiplicative.ofAdd c)
    refine ⟨k₁, k₂, 1, a, hk₁, hk₂, Finset.mem_singleton_self _, ?_, ?_⟩
    · exact uniformizerSection_mem_CAplus
        (fun α hα => hc α (simpleRelativeRoots_subset_positive i ν hα))
    · rw [show rationalPoints.map i a = x.val from hcx]
      simpa only [Subgroup.coe_one, mul_one] using hg
  · intro J hJ
    refine ⟨{1}, fun m hm => ?_⟩
    let j := Standard.leviHom i ν J
    let iJ := Standard.leviTorusHom i ν J
    let KJ := K.comap (rationalPoints.map j)
    let : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
      (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
    have hj := Standard.isRepresentedBy_leviHom i ν J
    have hm' : m ∈ (SubgroupFunctor.range j).carrier (Over.mk (𝟙 _)) := by
      rw [show SubgroupFunctor.range j = standardLevi i ν J from hj.2]
      exact hm
    obtain ⟨m', hm'⟩ := SubgroupFunctor.mem_range.mp hm'
    obtain ⟨x, hx⟩ :=
      (generalLinearIntegralLeviCartan F N ν hν J hJ).2 (DoubleCoset.mk KJ KJ m')
    obtain ⟨k₁, hk₁, k₂, hk₂, hg⟩ := DoubleCoset.eq.mp hx
    obtain ⟨c, hc, hcx⟩ := (mem_C0Plus T iJ _ x.val).mp x.property
    let a := uniformizerSection T (Multiplicative.ofAdd c)
    have hk (k : rationalPoints (Standard.leviScheme i ν J)) (h : k ∈ KJ) :
        rationalPoints.map j k ∈ K ⊓ standardLeviPoints i ν J := by
      refine ⟨h, ?_⟩
      change rationalPoints.map j k ∈ (standardLevi i ν J).carrier (Over.mk (𝟙 _))
      rw [← hj.2]
      exact SubgroupFunctor.mem_range.mpr ⟨k, rfl⟩
    refine ⟨rationalPoints.map j k₁, rationalPoints.map j k₂, 1, a,
      hk k₁ hk₁, hk k₂ hk₂, Finset.mem_singleton_self _, ?_, ?_⟩
    · exact uniformizerSection_mem_CAplus
        (fun α hα => hc α (Aubert.General.mem_positiveRelativeRoots_leviTorusHom i ν hJ hα))
    · have ha : rationalPoints.map j x.val = rationalPoints.map i a := by
        rw [← hcx, ← rationalPoints_map_comp_apply, Standard.leviTorusHom_comp]
      have h := congrArg (rationalPoints.map j) hg
      change rationalPoints.map j m' = _ at h
      rw [show rationalPoints.map j m' = m from hm', map_mul, map_mul, ha] at h
      simpa only [Subgroup.coe_one, mul_one] using h

end Langlands.HarishChandraSchwartz

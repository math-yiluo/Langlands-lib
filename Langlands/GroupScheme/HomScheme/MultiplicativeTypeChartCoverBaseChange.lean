import Langlands.GroupScheme.HomScheme.MultiplicativeTypeChartCoverTransport
import Langlands.GroupScheme.HomScheme.ChartCoverBaseChange
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Isomorphisms and base changes of actual multiplicative-type chart covers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.MultiplicativeTypeSubgroupModuli

open TorusSubgroupModuli

variable {S S' : Scheme.{u}} {G H : GroupScheme S}

/-- Ambient isomorphisms preserve actual open charts. -/
theorem isOpenChart_iso (e : G ≅ H) {U : Over S} {K : GroupScheme U.left}
    (j : K ⟶ (baseChange U.hom).obj G) (hj : IsOpenChart j) :
    IsOpenChart (j ≫ (baseChange U.hom).map e.hom) where
  isClosedSubgroup := hj.isClosedSubgroup.comp_iso ((baseChange U.hom).mapIso e)
  isMultiplicativeType := hj.isMultiplicativeType
  smooth := hj.smooth
  injective := by
    intro T a b h
    apply hj.injective T a b
    apply (range_postcomp_eq_iff ((baseChange T.hom).mapIso e)
      (familyHom j a) (familyHom j b)).mp
    simpa only [evaluate, familyHom_postcomp, Functor.mapIso_hom] using h
  isOpen := by
    intro T L i hi hL
    obtain ⟨V, hV⟩ := hj.isOpen T L (i ≫ (baseChange T.hom).map e.inv)
      (hi.comp_iso ((baseChange T.hom).mapIso e.symm)) hL
    refine ⟨V, fun T' b => ?_⟩
    exact (exists_congr (fun a => evaluate_postcomp_iso_iff e j a i b)).trans (hV T' b)

/-- A chart cover is invariant under an actual ambient group-scheme isomorphism. -/
theorem hasChartCover_iso (e : G ≅ H) (hG : HasChartCover G) : HasChartCover H := by
  obtain ⟨I, U, K, j, hj, hc⟩ := hG
  refine ⟨I, U, K, fun k => j k ≫ (baseChange (U k).hom).map e.hom,
    fun k => isOpenChart_iso e (j k) (hj k), ?_⟩
  intro F _ x L i hi hL
  obtain ⟨k, a, ha⟩ := hc F x L (i ≫ (baseChange (Over.mk x).hom).map e.inv)
    (hi.comp_iso ((baseChange (Over.mk x).hom).mapIso e.symm)) hL
  refine ⟨k, a, ?_⟩
  have h := range_postcomp_congr (familyHom (j k) a)
    (i ≫ (baseChange (Over.mk x).hom).map e.inv)
    ((baseChange (Over.mk x).hom).map e.hom) ha
  simpa only [evaluate, familyHom_postcomp, Category.assoc, Iso.map_inv_hom_id,
    Category.comp_id] using h

/-- Arbitrary change of base preserves the actual open-chart predicate. -/
theorem isOpenChart_baseChange (f : S' ⟶ S) {U : Over S}
    {K : GroupScheme U.left} (j : K ⟶ (baseChange U.hom).obj G)
    (hj : IsOpenChart j) :
    IsOpenChart (S := S') (G := (baseChange f).obj G)
      (U := (Over.pullback f).obj U)
      (K := (baseChange (pullParameter f U).left).obj K)
      (pullFamily (G := G) f j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact isClosedSubgroup_pullFamily f j hj.isClosedSubgroup
  · exact hj.isMultiplicativeType.baseChange (pullParameter f U).left
  ·
    let : Smooth U.hom := hj.smooth
    change Smooth (pullback.snd U.hom f)
    infer_instance
  ·
    intro T a b h
    apply ((Over.mapPullbackAdj f).homEquiv T U).symm.injective
    let K' := (baseChange (pullParameter f U).left).obj K
    let fa : (baseChange a.left).obj K' ⟶
        (baseChange T.hom).obj ((baseChange f).obj G) :=
      familyHom (S := S') (G := (baseChange f).obj G)
        (M := (Over.pullback f).obj U) (T := T) (K := K') (pullFamily f j) a
    let fb : (baseChange b.left).obj K' ⟶
        (baseChange T.hom).obj ((baseChange f).obj G) :=
      familyHom (S := S') (G := (baseChange f).obj G)
        (M := (Over.pullback f).obj U) (T := T) (K := K') (pullFamily f j) b
    have hpost := range_postcomp_congr (S := T.left)
      (G := (baseChange T.hom).obj ((baseChange f).obj G))
      (H := (baseChange (T.hom ≫ f)).obj G) fa fb
      (Descent.pullbackComparison f T.hom (T.hom ≫ f) rfl G).hom h
    dsimp only [fa, fb] at hpost
    rw [range_pullFamily f j a, range_pullFamily f j b] at hpost
    exact hj.injective ((Over.map f).obj T) (baseParameter f a) (baseParameter f b) hpost
  ·
    intro T L i hi hL
    obtain ⟨V, hV⟩ := hj.isOpen ((Over.map f).obj T) L (pushFamily (G := G) f i)
      (isClosedSubgroup_pushFamily (G := G) (U := T) (K := L) f i hi) hL
    refine ⟨V, fun T' b => ?_⟩
    have hev :
        (∃ a : T' ⟶ (Over.pullback f).obj U,
          evaluate (pullFamily (G := G) f j) a = evaluate i b) ↔
        (∃ a₀ : (Over.map f).obj T' ⟶ U,
          evaluate j a₀ = evaluate (pushFamily (G := G) f i) ((Over.map f).map b)) := by
      constructor
      · rintro ⟨a, ha⟩
        exact ⟨baseParameter f a, (evaluate_pullFamily_iff f j i a b).mp ha⟩
      · rintro ⟨a₀, ha⟩
        refine ⟨(Over.mapPullbackAdj f).homEquiv T' U a₀,
          (evaluate_pullFamily_iff f j i _ b).mpr ?_⟩
        simpa only [baseParameter, Equiv.symm_apply_apply] using ha
    exact hev.trans (hV ((Over.map f).obj T') ((Over.map f).map b))

/-- Arbitrary change of base preserves coverage of actual closed multiplicative-type subgroups
at every field point. -/
theorem coversFieldPoints_baseChange (f : S' ⟶ S) {I : Type u}
    {U : I → Over S} {K : ∀ k, GroupScheme (U k).left}
    (j : ∀ k, K k ⟶ (baseChange (U k).hom).obj G)
    (hc : CoversFieldPoints j) :
    CoversFieldPoints (S := S') (G := (baseChange f).obj G)
      (U := fun k => (Over.pullback f).obj (U k))
      (K := fun k => (baseChange (pullParameter f (U k)).left).obj (K k))
      (fun k => pullFamily f (j k)) := by
  intro F _ x L i hi hL
  obtain ⟨k, a₀, ha⟩ := hc F (x ≫ f) L (pushFamily (G := G) (U := Over.mk x) (K := L) f i)
    (isClosedSubgroup_pushFamily (G := G) (U := Over.mk x) (K := L) f i hi) hL
  let a : Over.mk x ⟶ (Over.pullback f).obj (U k) :=
    (Over.mapPullbackAdj f).homEquiv (Over.mk x) (U k) a₀
  refine ⟨k, a, ?_⟩
  apply (range_postcomp_eq_iff
    (Descent.pullbackComparison f (Over.mk x).hom ((Over.mk x).hom ≫ f) rfl G)
    (familyHom (pullFamily f (j k)) a) i).mp
  rw [range_pullFamily f (j k) a]
  change evaluate (j k) (baseParameter f a) =
    SubgroupFunctor.range (pushFamily (G := G) f i)
  simpa only [a, baseParameter, Equiv.symm_apply_apply] using ha

/-- Chart covers pull back along every morphism of bases. -/
theorem hasChartCover_baseChange (f : S' ⟶ S) (hG : HasChartCover G) :
    HasChartCover ((baseChange f).obj G) := by
  obtain ⟨I, U, K, j, hj, hc⟩ := hG
  exact ⟨I, fun k => (Over.pullback f).obj (U k),
    fun k => (baseChange (pullParameter f (U k)).left).obj (K k),
    fun k => pullFamily f (j k), fun k => isOpenChart_baseChange f (j k) (hj k),
    coversFieldPoints_baseChange f j hc⟩

end Langlands.GroupScheme.MultiplicativeTypeSubgroupModuli

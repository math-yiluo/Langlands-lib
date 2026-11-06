import Langlands.GroupScheme.HomScheme.ChartCoverTransport
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Isomorphisms and base changes of actual chart covers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S S' : Scheme.{u}} {G H : GroupScheme S}

/-- Equality of evaluated families is transported through an ambient isomorphism. -/
theorem evaluate_postcomp_iso_iff (e : G ≅ H) {U V T : Over S}
    {K : GroupScheme U.left} {L : GroupScheme V.left}
    (j : K ⟶ (baseChange U.hom).obj G) (a : T ⟶ U)
    (i : L ⟶ (baseChange V.hom).obj H) (b : T ⟶ V) :
    evaluate (j ≫ (baseChange U.hom).map e.hom) a = evaluate i b ↔
      evaluate j a = evaluate (i ≫ (baseChange V.hom).map e.inv) b := by
  simp only [evaluate, familyHom_postcomp]
  simpa only [Functor.mapIso_hom, Category.assoc, Iso.map_inv_hom_id,
    Category.comp_id] using
    (range_postcomp_eq_iff ((baseChange T.hom).mapIso e)
      (familyHom j a) (familyHom i b ≫ (baseChange T.hom).map e.inv))

/-- Ambient isomorphisms preserve actual open charts. -/
theorem isOpenChart_iso (e : G ≅ H) {U : Over S} {K : GroupScheme U.left}
    (j : K ⟶ (baseChange U.hom).obj G) (hj : IsOpenChart j) :
    IsOpenChart (j ≫ (baseChange U.hom).map e.hom) where
  isClosedSubgroup := hj.isClosedSubgroup.comp_iso ((baseChange U.hom).mapIso e)
  isTorus := hj.isTorus
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

/-- The actual parameter projection, viewed over the original base. -/
def pullParameter (f : S' ⟶ S) (U : Over S) :
    (Over.map f).obj ((Over.pullback f).obj U) ⟶ U :=
  Over.homMk (pullback.fst U.hom f) pullback.condition

/-- A parameter over the changed base viewed as a parameter over the original base. -/
def baseParameter (f : S' ⟶ S) {U : Over S} {T : Over S'}
    (a : T ⟶ (Over.pullback f).obj U) : (Over.map f).obj T ⟶ U :=
  ((Over.mapPullbackAdj f).homEquiv T U).symm a

theorem baseParameter_eq (f : S' ⟶ S) {U : Over S} {T : Over S'}
    (a : T ⟶ (Over.pullback f).obj U) :
    baseParameter f a =
      (Over.map f).map a ≫ pullParameter f U := by
  apply Over.OverMorphism.ext
  rfl

/-- Pull an actual family to the changed parameter base. -/
def pullFamily (f : S' ⟶ S) {U : Over S} {K : GroupScheme U.left}
    (j : K ⟶ (baseChange U.hom).obj G) :
    (baseChange (pullParameter f U).left).obj K ⟶
      (baseChange ((Over.pullback f).obj U).hom).obj ((baseChange f).obj G) :=
  familyHom j (pullParameter f U) ≫
    (Descent.pullbackComparison f ((Over.pullback f).obj U).hom
      (((Over.pullback f).obj U).hom ≫ f) rfl G).inv

/-- Pushing the pulled family recovers evaluation along the pullback projection. -/
theorem pushFamily_pullFamily (f : S' ⟶ S) {U : Over S} {K : GroupScheme U.left}
    (j : K ⟶ (baseChange U.hom).obj G) :
    pushFamily f (pullFamily (G := G) f j) =
      familyHom j (pullParameter f U) := by
  simp only [pushFamily, pullFamily, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The evaluated pulled family has exactly the original evaluated range under
the ambient comparison. -/
theorem range_pullFamily (f : S' ⟶ S) {U : Over S} {K : GroupScheme U.left}
    (j : K ⟶ (baseChange U.hom).obj G) {T : Over S'}
    (a : T ⟶ (Over.pullback f).obj U) :
    SubgroupFunctor.range (familyHom (pullFamily (G := G) f j) a ≫
      (Descent.pullbackComparison f T.hom (T.hom ≫ f) rfl G).hom) =
      evaluate j (baseParameter f a) := by
  rw [← familyHom_pushFamily, pushFamily_pullFamily]
  change evaluate (familyHom j (pullParameter f U))
    ((Over.map f).map a) = _
  rw [evaluate_comp, baseParameter_eq]

/-- The adjunction identifies all evaluations used to test the chart's open locus. -/
theorem evaluate_pullFamily_iff (f : S' ⟶ S) {U : Over S}
    {K : GroupScheme U.left} (j : K ⟶ (baseChange U.hom).obj G)
    {T T' : Over S'} {L : GroupScheme T.left}
    (i : L ⟶ (baseChange T.hom).obj ((baseChange f).obj G))
    (a : T' ⟶ (Over.pullback f).obj U) (b : T' ⟶ T) :
    evaluate (pullFamily (G := G) f j) a = evaluate i b ↔
      evaluate j (baseParameter f a) =
        evaluate (pushFamily (G := G) f i) ((Over.map f).map b) := by
  have he := range_postcomp_eq_iff
    (Descent.pullbackComparison f T'.hom (T'.hom ≫ f) rfl G)
    (familyHom (pullFamily (G := G) f j) a) (familyHom i b)
  rw [range_pullFamily f j a, ← familyHom_pushFamily f i b] at he
  exact he.symm

/-- The pulled actual inclusion remains a closed subgroup. -/
theorem isClosedSubgroup_pullFamily (f : S' ⟶ S) {U : Over S}
    {K : GroupScheme U.left} (j : K ⟶ (baseChange U.hom).obj G)
    (hj : IsClosedSubgroup j) : IsClosedSubgroup (pullFamily (G := G) f j) := by
  have hc := isClosedSubgroup_familyHom (S := S) (G := G) (M := U)
    (T := (Over.map f).obj ((Over.pullback f).obj U)) (K := K) j hj (pullParameter f U)
  let : IsClosedImmersion (familyHom (S := S) (G := G) (M := U)
    (T := (Over.map f).obj ((Over.pullback f).obj U)) (K := K)
    j (pullParameter f U)).hom.hom.left := hc
  change IsClosedImmersion
    ((familyHom (S := S) (G := G) (M := U)
      (T := (Over.map f).obj ((Over.pullback f).obj U)) (K := K)
      j (pullParameter f U)).hom.hom.left ≫
      (Descent.pullbackComparison f ((Over.pullback f).obj U).hom
        (((Over.pullback f).obj U).hom ≫ f) rfl G).inv.hom.hom.left)
  infer_instance

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
  · exact hj.isTorus.baseChange (pullParameter f U).left
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

/-- Arbitrary change of base preserves coverage of actual closed torus subgroups
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

end Langlands.GroupScheme.TorusSubgroupModuli

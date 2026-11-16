import Langlands.GroupScheme.Torus.MaximalModuliUniqueness
import Langlands.GroupScheme.HomScheme.ChartCoverBaseChange

/-! # Base change of supplied universal maximal-torus families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S S' : Scheme.{u}} {G : GroupScheme S}
  {M : Over S} {K : CommGroupScheme M.left}

/-- Evaluation of a pulled family classifies the same actual subgroup after
the canonical ambient comparison to the original base. -/
theorem evaluate_pullFamily_range_iff
    (f : S' ⟶ S) (j : K.toGrp ⟶ (baseChange M.hom).obj G)
    {T : Over S'} {L : CommGroupScheme T.left}
    (i : L.toGrp ⟶ (baseChange T.hom).obj ((baseChange f).obj G))
    (a : T ⟶ (Over.pullback f).obj M) :
    evaluate (pullFamily f j) a = SubgroupFunctor.range i ↔
      evaluate j (baseParameter f a) = SubgroupFunctor.range (pushFamily f i) := by
  have h := range_postcomp_eq_iff
    (Descent.pullbackComparison f T.hom (T.hom ≫ f) rfl G)
    (familyHom (pullFamily f j) a) i
  rw [range_pullFamily f j a] at h
  exact h.symm

/-- The adjoint classifier of a maximal-torus family on the changed base. -/
def pullMaximalClassifier
    {j : K.toGrp ⟶ (baseChange M.hom).obj G}
    (huni : IsUniversalMaximal j) (f : S' ⟶ S)
    {T : Over S'} {L : CommGroupScheme T.left}
    (i : L.toGrp ⟶ (baseChange T.hom).obj ((baseChange f).obj G))
    (hL : RelativeTorus.IsTorus L.toGrp) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus i) :
    T ⟶ (Over.pullback f).obj M :=
  (Over.mapPullbackAdj f).homEquiv T M
    (Classical.choose (huni ((Over.map f).obj T) L (pushFamily f i)
      hL (isClosedSubgroup_pushFamily f i hi)
      (hmax.comp_iso (Descent.pullbackComparison f T.hom (T.hom ≫ f) rfl G))))

/-- The adjoint classifier evaluates to the supplied subgroup on the new base. -/
theorem evaluate_pullMaximalClassifier
    {j : K.toGrp ⟶ (baseChange M.hom).obj G}
    (huni : IsUniversalMaximal j) (f : S' ⟶ S)
    {T : Over S'} {L : CommGroupScheme T.left}
    (i : L.toGrp ⟶ (baseChange T.hom).obj ((baseChange f).obj G))
    (hL : RelativeTorus.IsTorus L.toGrp) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus i) :
    evaluate (pullFamily f j) (pullMaximalClassifier huni f i hL hi hmax) =
      SubgroupFunctor.range i := by
  apply (evaluate_pullFamily_range_iff f j i _).mpr
  simpa only [pullMaximalClassifier, baseParameter, Equiv.symm_apply_apply] using
    (Classical.choose_spec (huni ((Over.map f).obj T) L (pushFamily f i)
      hL (isClosedSubgroup_pushFamily f i hi)
      (hmax.comp_iso (Descent.pullbackComparison f T.hom (T.hom ≫ f) rfl G)))).1

/-- Universality for actual maximal-torus families is preserved by every
change of base. -/
theorem IsUniversalMaximal.pullFamily
    {j : K.toGrp ⟶ (baseChange M.hom).obj G}
    (huni : IsUniversalMaximal j) (f : S' ⟶ S) :
    IsUniversalMaximal
      (S := S') (G := (baseChange f).obj G) (M := (Over.pullback f).obj M)
      (K := (CommGroupScheme.baseChange (pullParameter f M).left).obj K)
      (pullFamily f j) := by
  intro T L i hL hi hmax
  obtain ⟨a, ha, hua⟩ := huni ((Over.map f).obj T) L (pushFamily f i)
    hL (isClosedSubgroup_pushFamily f i hi)
    (hmax.comp_iso (Descent.pullbackComparison f T.hom (T.hom ≫ f) rfl G))
  refine ⟨(Over.mapPullbackAdj f).homEquiv T M a, ?_, ?_⟩
  · apply (evaluate_pullFamily_range_iff f j i _).mpr
    simpa only [baseParameter, Equiv.symm_apply_apply] using ha
  · intro c hc
    apply ((Over.mapPullbackAdj f).homEquiv T M).symm.injective
    rw [Equiv.symm_apply_apply]
    exact hua (baseParameter f c) ((evaluate_pullFamily_range_iff f j i c).mp hc)

/-- The pulled universal inclusion remains fibrewise maximal in a smooth
affine ambient group. -/
theorem isFibrewiseMaximalTorus_pullFamily
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (f : S' ⟶ S) (j : K.toGrp ⟶ (baseChange M.hom).obj G)
    (hm : IsFibrewiseMaximalTorus j) :
    IsFibrewiseMaximalTorus
      (T := (CommGroupScheme.baseChange (pullParameter f M).left).obj K)
      (pullFamily f j) :=
  (isFibrewiseMaximalTorus_familyHom j hm (pullParameter f M)).comp_iso
    (Descent.pullbackComparison f ((Over.pullback f).obj M).hom
      (((Over.pullback f).obj M).hom ≫ f) rfl G).symm

end Langlands.GroupScheme.TorusSubgroupModuli

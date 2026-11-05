import Langlands.AlgebraicGeometry.NoetherianDvrSpecialization
import Langlands.AlgebraicGeometry.SectionComponentGenerization
import Mathlib.Topology.ContinuousMap.Basic

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.SectionComponent

/-- Restricting the source of a geometrically reduced morphism to an open
subscheme preserves geometric reducedness. -/
theorem geometricallyReduced_comp_of_isOpenImmersion
    {U F S : Scheme.{u}} (j : U ⟶ F) (p : F ⟶ S)
    [IsOpenImmersion j] [GeometricallyReduced p] : GeometricallyReduced (j ≫ p) := by
  refine ⟨fun K _ k Z a b hZ => ?_⟩
  let m : Z ⟶ pullback p k :=
    pullback.lift (a ≫ j) b (by simpa only [Category.assoc] using hZ.w)
  have hbig : IsPullback a (m ≫ pullback.snd p k) (j ≫ p) k := by
    simpa only [m, pullback.lift_snd] using hZ
  have hm : IsPullback a m j (pullback.fst p k) :=
    hbig.of_bot (by simp [m]) (.of_hasPullback p k)
  let : IsOpenImmersion m :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hm inferInstance
  let : AlgebraicGeometry.IsReduced (pullback p k) :=
    GeometricallyReduced.geometrically_isReduced (f := p) k _ _ (.of_hasPullback p k)
  exact isReduced_of_isOpenImmersion m

/-- Every generization of a point of the selected-component union still lies
in that union when its indexed selected component is geometrically reduced. -/
theorem mem_componentSet_of_specializes
    {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f]
    (e : Y ⟶ X) (he : e ≫ f = 𝟙 _)
    (x : X)
    [GeometricallyReduced
      ((fiberComponentOpen f e he (f x)).ι ≫ f.fiberToSpecResidueField (f x))]
    (hx : x ∈ componentSet f e he) {η : X} (hη : η ⤳ x) :
    η ∈ componentSet f e he := by
  classical
  by_cases hne : η = x
  · simpa only [hne] using hx
  obtain ⟨M⟩ := nonempty_dvrSpecialization X η x hη hne
  let : GeometricallyReduced
      ((fiberComponentOpen f e he (f (M.map (IsLocalRing.closedPoint M.ring)))).ι ≫
        f.fiberToSpecResidueField (f (M.map (IsLocalRing.closedPoint M.ring)))) := by
    rw [M.closed_image]
    infer_instance
  have hc : M.map (IsLocalRing.closedPoint M.ring) ∈ componentSet f e he := by
    rwa [M.closed_image]
  have hg := dvr_generic_mem_componentSet f e he M.ring M.map hc
  rwa [M.generic_image] at hg

/-- Whole-fibre geometric reducedness supplies the pointwise generization
conclusion, with no condition on the other fibres. -/
theorem mem_componentSet_of_specializes_of_geometricallyReduced_fiber
    {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f]
    (e : Y ⟶ X) (he : e ≫ f = 𝟙 _) (x : X)
    [GeometricallyReduced (f.fiberToSpecResidueField (f x))]
    (hx : x ∈ componentSet f e he) {η : X} (hη : η ⤳ x) :
    η ∈ componentSet f e he := by
  let : GeometricallyReduced
      ((fiberComponentOpen f e he (f x)).ι ≫ f.fiberToSpecResidueField (f x)) :=
    geometricallyReduced_comp_of_isOpenImmersion _ _
  exact mem_componentSet_of_specializes f e he x hx hη

/-- The inclusion of all generizations of a selected point factors continuously
through the relative selected-component union. -/
def componentGenerizationMap
    {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f]
    (e : Y ⟶ X) (he : e ≫ f = 𝟙 _) (x : X)
    [GeometricallyReduced
      ((fiberComponentOpen f e he (f x)).ι ≫ f.fiberToSpecResidueField (f x))]
    (hx : x ∈ componentSet f e he) :
    C({η : X // η ⤳ x}, componentSet f e he) where
  toFun η := ⟨η.val, mem_componentSet_of_specializes f e he x hx η.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp]
theorem componentGenerizationMap_coe
    {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f]
    (e : Y ⟶ X) (he : e ≫ f = 𝟙 _) (x : X)
    [GeometricallyReduced
      ((fiberComponentOpen f e he (f x)).ι ≫ f.fiberToSpecResidueField (f x))]
    (hx : x ∈ componentSet f e he) (η : {η : X // η ⤳ x}) :
    (componentGenerizationMap f e he x hx η : X) = η.val := rfl

end Langlands.AlgebraicGeometry.SectionComponent

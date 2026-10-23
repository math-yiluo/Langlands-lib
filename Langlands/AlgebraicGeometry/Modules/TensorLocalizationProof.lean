import Langlands.AlgebraicGeometry.Modules.TensorLocalizationStatement
import Langlands.Algebra.Modules.TensorColimit
import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import Mathlib.Topology.Sheaves.Points

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace Langlands.Scheme.Modules

/-- Local equivalences of module presheaves on a scheme are stable under
sectionwise tensoring on either side. -/
theorem tensorLocalEquivalencesIsMonoidal
    (X : AlgebraicGeometry.Scheme.{u}) :
    tensorLocalEquivalencesIsMonoidalStatement X := by
  let J := Opens.grothendieckTopology X
  let W : MorphismProperty (PresheafOfModulesOfCommRing.{u} X.presheaf) :=
    J.W.inverseImage (PresheafOfModules.toPresheaf.{u} X.ringCatSheaf.obj)
  change W.IsMonoidal
  have : (J.W (A := AddCommGrpCat.{u})).IsMultiplicative := inferInstance
  have : W.IsMultiplicative := by
    refine { id_mem := ?_, comp_mem := ?_ }
    · intro M
      change J.W ((PresheafOfModules.toPresheaf _).map (𝟙 M))
      rw [CategoryTheory.Functor.map_id]
      exact J.W.id_mem _
    · intro M N P f g hf hg
      change J.W ((PresheafOfModules.toPresheaf _).map (f ≫ g))
      rw [CategoryTheory.Functor.map_comp]
      exact J.W.comp_mem _ _ hf hg
  refine MorphismProperty.IsMonoidal.mk' W ?_
  intro M₁ M₂ N₁ N₂ f g hf hg
  change J.W ((PresheafOfModules.toPresheaf _).map (f ⊗ₘ g))
  rw [Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology X |>.W_iff]
  intro Φ
  have hf' := (Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology X).W_iff
    ((PresheafOfModules.toPresheaf _).map f) |>.mp hf Φ
  have hg' := (Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology X).W_iff
    ((PresheafOfModules.toPresheaf _).map g) |>.mp hg Φ
  let π := Functor.Elements.π Φ.obj.fiber
  let P := PresheafOfModules.pushforward₀OfCommRingCat π X.presheaf
  let L := PresheafOfModules.toPresheaf.{u}
    ((π.op ⋙ X.presheaf) ⋙ forget₂ CommRingCat RingCat) ⋙ colim
  have hf'' : IsIso (L.map (P.map f)) := hf'
  have hg'' : IsIso (L.map (P.map g)) := hg'
  have hfg : IsIso (L.map (P.map f ⊗ₘ P.map g)) :=
    Langlands.Algebra.Modules.tensorColimitIsIso _
      (π.op ⋙ X.presheaf) _ _ _ _ (P.map f) (P.map g) hf'' hg''
  change IsIso (L.map (P.map (f ⊗ₘ g)))
  rw [Functor.Monoidal.map_tensor, L.map_comp, L.map_comp]
  infer_instance

end Langlands.Scheme.Modules

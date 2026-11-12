import Langlands.Global.AdelicSpaceSmoothModelGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteTypeMorphismAtlas
import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeDiagonalCharts
import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemePointsComparison

/-! # Automatic morphism properties of smooth connected-fibre stage models -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A separated source makes every arrow separated over the same base. -/
theorem isSeparatedMorphism_of_isSeparated_source
    (hX : IsSeparated X) (f : X ⟶ Y) : IsSeparatedMorphism f := by
  apply MorphismProperty.of_postcomp
    (W := (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (Over.forget S)).relative (schemeYoneda S))
    (W' := MorphismProperty.monomorphisms (Presheaf S))
    (pullback.diagonal (hom f)) (relativeDiagonalTargetMap (hom f))
    (by change Mono (relativeDiagonalTargetMap (hom f)); infer_instance)
  rw [relativeDiagonalTargetMap_fac]
  exact hX

/-- The nonemptiness in the geometric connected-fibre predicate forces
surjectivity on the actual point quotient. -/
theorem HasGeometricallyConnectedFibres.isSurjectiveMorphism
    {f : X ⟶ Y} (hf : HasGeometricallyConnectedFibres f) : IsSurjectiveMorphism f := by
  intro p
  induction p using Quot.ind with
  | _ p =>
    let T : Over S := Over.mk p.base
    let y : (schemeYoneda S).obj T ⟶ Y.presheaf := uliftYonedaEquiv.{u + 1}.symm p.val
    let : TopologicalSpace (Points (Limits.pullback (hom f) y)) := pointTopology _
    let := hf p.field p.base y
    obtain ⟨q⟩ := (inferInstance : Nonempty (Points (Limits.pullback (hom f) y)))
    let r : Points ((schemeYoneda S).obj T) := Quot.mk _
      (⟨p.field, p.base, ULift.up (𝟙 T)⟩ : FieldPoint ((schemeYoneda S).obj T))
    have hr : Points.map (pullback.snd (hom f) y) q = r := by
      apply (schemePointsEquiv T).injective
      exact Subsingleton.elim (α := PrimeSpectrum p.field) _ _
    refine ⟨Points.map (pullback.fst (hom f) y) q, ?_⟩
    rw [← Points.map_comp, pullback.condition, Points.map_comp, hr]
    change Quot.mk _ (FieldPoint.map y
      (⟨p.field, p.base, ULift.up (𝟙 T)⟩ : FieldPoint ((schemeYoneda S).obj T))) = Quot.mk _ p
    congr 1
    change (⟨p.field, p.base, y.app (op T) (ULift.up (𝟙 T))⟩ : FieldPoint Y.presheaf) = p
    have hy : y.app (op T) (ULift.up (𝟙 T)) = p.val := by
      exact uliftYonedaEquiv.{u + 1}.apply_symm_apply p.val
    cases p
    simp_all

/-- The auxiliary arrow geometry consumed by uniform finite-field lifting. -/
structure AuxiliaryMorphismGeometry (f : X ⟶ Y) : Type u where
  separated : IsSeparatedMorphism f
  quasiCompact : IsQuasiCompactMorphism f
  surjective : IsSurjectiveMorphism f

/-- All three auxiliary morphism hypotheses follow from the existing stage
geometry; the relative dimension and uniform estimate are not used. -/
theorem smoothConnectedModel_morphismProperties [IsAffine S]
    (hX : IsSeparated X) (hXqc : HasAtlasProperty (@QuasiCompact.{u}) X)
    (hY : IsQuasiSeparated Y) (f : X ⟶ Y)
    (hf : HasGeometricallyConnectedFibres f) :
    IsSeparatedMorphism f ∧ IsQuasiCompactMorphism f ∧ IsSurjectiveMorphism f :=
  ⟨isSeparatedMorphism_of_isSeparated_source hX f,
    isQuasiCompactMorphism_of_atlas hXqc hY f, hf.isSurjectiveMorphism⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Global.AdelicSpaceSmoothModelGeometry

open Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Construct the auxiliary arrow-geometry bundle from the existing stage model. -/
def SmoothConnectedStageModel.auxiliaryGeometry
    {I : Type u} [SmallCategory I] {D : I ⥤ Scheme.{u}} [∀ i, IsAffine (D.obj i)]
    {c : Cone D} {Y W : AlgebraicSpace c.pt} {g : Y ⟶ W}
    (m : SmoothConnectedStageModel D c g) : AuxiliaryMorphismGeometry m.map :=
  ⟨isSeparatedMorphism_of_isSeparated_source m.source_separated m.map,
    isQuasiCompactMorphism_of_atlas
      (m.source_atlas.mono (fun _ _ _ h => h.2))
      (AdelicSpaceProperModelReduction.quasiSeparated_of_separated m.target_separated) m.map,
    m.map_connected.isSurjectiveMorphism⟩

/-- Every constructed stage arrow already satisfies all the auxiliary morphism
properties needed by the uniform Lang-Weil lifting argument. -/
theorem SmoothConnectedStageModel.morphismProperties
    {I : Type u} [SmallCategory I] {D : I ⥤ Scheme.{u}} [∀ i, IsAffine (D.obj i)]
    {c : Cone D} {Y W : AlgebraicSpace c.pt} {g : Y ⟶ W}
    (m : SmoothConnectedStageModel D c g) :
    IsSeparatedMorphism m.map ∧ IsQuasiCompactMorphism m.map ∧ IsSurjectiveMorphism m.map :=
  smoothConnectedModel_morphismProperties m.source_separated
    (m.source_atlas.mono (fun _ _ _ h => h.2))
    (AdelicSpaceProperModelReduction.quasiSeparated_of_separated m.target_separated)
    m.map m.map_connected

end Langlands.Global.AdelicSpaceSmoothModelGeometry

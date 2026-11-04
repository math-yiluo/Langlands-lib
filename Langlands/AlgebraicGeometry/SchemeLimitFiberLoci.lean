import Langlands.AlgebraicGeometry.SchemeFiberGeometryLoci
import Langlands.AlgebraicGeometry.SchemeLimitModelMaps
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Actual model diagrams and their geometric fibre loci -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel.Geometry

open AffineLimit EtaleEquivalenceRelation.Action.TargetLimit SchemeFiberGeometry

variable {S X Y T : Scheme.{u}}
  (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (w : f ≫ b = a)

/-- The map of the two actual base changes is itself a cartesian base change. -/
theorem baseChangeMap_cartesian (p : T ⟶ S) :
    IsPullback (baseChangeMap a b f w p) (pullback.snd p a)
      (pullback.snd p b) f := by
  apply IsPullback.of_right
    (h₁₂ := pullback.fst p b) (h₂₂ := b) (v₁₃ := p)
  · simpa only [baseChangeMap_fst, w] using IsPullback.of_hasPullback p a
  · exact baseChangeMap_snd a b f w p
  · exact IsPullback.of_hasPullback p b

/-- The nonempty locus of an actual base change is the actual inverse image. -/
theorem nonemptyFiberLocus_baseChangeMap (p : T ⟶ S) :
    nonemptyFiberLocus (baseChangeMap a b f w p) =
      (pullback.snd p b) ⁻¹' nonemptyFiberLocus f :=
  nonemptyFiberLocus_baseChange (baseChangeMap_cartesian a b f w p).flip

/-- The same comparison for geometrically connected actual fibres. -/
theorem geometricallyConnectedFiberLocus_baseChangeMap (p : T ⟶ S) :
    geometricallyConnectedFiberLocus (baseChangeMap a b f w p) =
      (pullback.snd p b) ⁻¹' geometricallyConnectedFiberLocus f :=
  geometricallyConnectedFiberLocus_baseChange (baseChangeMap_cartesian a b f w p).flip

variable {I : Type u} [Category.{u} I]
  (D : I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const I).obj S)

/-- The fixed relative morphism induces a natural transformation of actual
base-changed model diagrams. -/
def morphismDiagram : diagram D t a ⟶ diagram D t b where
  app i := baseChangeMap a b f w (t.app i)
  naturality _ _ r := baseChangeMap_naturality D t a b f w r

/-- The transition maps in a model diagram are actual base changes of the
original base transitions. -/
theorem transition_cartesian {i j : I} (r : i ⟶ j) :
    IsPullback ((diagram D t a).map r) (pullback.fst (t.app i) a)
      (pullback.fst (t.app j) a) (D.map r) := by
  apply IsPullback.of_right
    (h₁₂ := pullback.snd (t.app j) a) (h₂₂ := t.app j) (v₁₃ := a)
  · have e : D.map r ≫ t.app j = t.app i := by simp
    simpa only [diagram_map_snd, e] using
      (IsPullback.of_hasPullback (t.app i) a).flip
  · exact diagram_map_fst D t a r
  · exact (IsPullback.of_hasPullback (t.app j) a).flip

/-- Affine transitions remain affine for arbitrary fixed models. -/
instance transition_isAffineHom
    [∀ {i j} (r : i ⟶ j), IsAffineHom (D.map r)] {i j : I} (r : i ⟶ j) :
    IsAffineHom ((diagram D t a).map r) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom)
    (transition_cartesian a D t r).flip inferInstance

/-- A quasi-compact model over a compact stage is compact. -/
instance model_compactSpace [QuasiCompact a] (i : I) [CompactSpace (D.obj i)] :
    CompactSpace ((diagram D t a).obj i) := by
  change CompactSpace ↑(pullback (t.app i) a : Scheme.{u})
  infer_instance

/-- A quasi-separated model over a quasi-separated stage is quasi-separated. -/
instance model_quasiSeparatedSpace [QuasiSeparated a] (i : I)
    [QuasiSeparatedSpace (D.obj i)] :
    QuasiSeparatedSpace ((diagram D t a).obj i) :=
  quasiSeparatedSpace_of_quasiSeparated (pullback.fst (t.app i) a)

/-- Each transition naturality square is cartesian, including for
nonaffine and nonseparated models. -/
theorem morphismDiagram_cartesian {i j : I} (r : i ⟶ j) :
    IsPullback (baseChangeMap a b f w (t.app i)) ((diagram D t a).map r)
      ((diagram D t b).map r) (baseChangeMap a b f w (t.app j)) := by
  apply IsPullback.of_right
    (h₁₂ := pullback.fst (t.app i) b) (h₂₂ := pullback.fst (t.app j) b)
    (v₁₃ := D.map r)
  · simpa only [baseChangeMap_fst] using (transition_cartesian a D t r).flip
  · exact (baseChangeMap_naturality D t a b f w r).symm
  · exact (transition_cartesian b D t r).flip

variable (c : Cone D) (p : c.pt ⟶ S)
  (hp : ∀ i, c.π.app i ≫ t.app i = p)

/-- The canonical comparison to a stage is cartesian over the actual cone leg. -/
theorem coneLeg_cartesian (i : I) :
    IsPullback ((cone D t a c p hp).π.app i) (pullback.fst p a)
      (pullback.fst (t.app i) a) (c.π.app i) := by
  apply IsPullback.of_right
    (h₁₂ := pullback.snd (t.app i) a) (h₂₂ := t.app i) (v₁₃ := a)
  · simpa only [cone_π_snd, hp] using (IsPullback.of_hasPullback p a).flip
  · exact cone_π_fst D t a c p hp i
  · exact (IsPullback.of_hasPullback (t.app i) a).flip

/-- The limit-model map and any stage-model map form the actual cartesian square. -/
theorem coneMorphism_cartesian (i : I) :
    IsPullback (baseChangeMap a b f w p) ((cone D t a c p hp).π.app i)
      ((cone D t b c p hp).π.app i) (baseChangeMap a b f w (t.app i)) := by
  apply IsPullback.of_right
    (h₁₂ := pullback.fst p b) (h₂₂ := pullback.fst (t.app i) b)
    (v₁₃ := c.π.app i)
  · simpa only [baseChangeMap_fst] using (coneLeg_cartesian a D t c p hp i).flip
  · exact (cone_baseChangeMap D t a b f w c p hp i).symm
  · exact (coneLeg_cartesian b D t c p hp i).flip

/-- Nonempty loci compare along actual model-cone legs. No limit witness is needed. -/
theorem nonemptyFiberLocus_cone (i : I) :
    nonemptyFiberLocus (baseChangeMap a b f w p) =
      ((cone D t b c p hp).π.app i) ⁻¹'
        nonemptyFiberLocus (baseChangeMap a b f w (t.app i)) :=
  nonemptyFiberLocus_baseChange (coneMorphism_cartesian a b f w D t c p hp i).flip

/-- Geometric-connectedness loci compare along the same actual model-cone legs. -/
theorem geometricallyConnectedFiberLocus_cone (i : I) :
    geometricallyConnectedFiberLocus (baseChangeMap a b f w p) =
      ((cone D t b c p hp).π.app i) ⁻¹'
        geometricallyConnectedFiberLocus (baseChangeMap a b f w (t.app i)) :=
  geometricallyConnectedFiberLocus_baseChange
    (coneMorphism_cartesian a b f w D t c p hp i).flip

end Langlands.AlgebraicGeometry.SchemeLimitModel.Geometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Chevalley's theorem applied to the actual nonempty-fibre locus. -/
theorem isLocallyConstructible_nonemptyFiberLocus
    [LocallyOfFinitePresentation f] [QuasiCompact f] :
    IsLocallyConstructible (nonemptyFiberLocus f) := by
  rw [nonemptyFiberLocus_eq_range, ← image_univ]
  exact f.isLocallyConstructible_image .univ

/-- On a qcqs target the same actual locus is globally constructible. -/
theorem isConstructible_nonemptyFiberLocus
    [LocallyOfFinitePresentation f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] :
    IsConstructible (nonemptyFiberLocus f) :=
  (isLocallyConstructible_nonemptyFiberLocus f).isConstructible

end Langlands.AlgebraicGeometry.SchemeFiberGeometry

import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeGeometryStatement
import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeSmoothStatement
import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeSeparatedProof
import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeSurjectionProof

/-! # Geometric connectedness and the remaining smoothness reduction for the chosen dual -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- A scheme over `S` receiving a surjective `S`-morphism from a geometrically connected
`S`-scheme is geometrically connected. -/
lemma geometricallyConnected_of_surjective {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (p : X ⟶ S) (q : Y ⟶ S) (w : f ≫ q = p) [Surjective f] [GeometricallyConnected p] :
    GeometricallyConnected q := by
  refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
  have : ConnectedSpace ↥(pullback p y) :=
    GeometricallyConnected.geometrically_connectedSpace (f := p) y (pullback.fst p y)
      (pullback.snd p y) (IsPullback.of_hasPullback p y)
  let g : pullback p y ⟶ Z := h.lift (pullback.fst p y ≫ f) (pullback.snd p y)
    (by rw [Category.assoc, w, pullback.condition])
  have big : IsPullback (g ≫ snd) (pullback.fst p y) y (f ≫ q) := by
    rw [h.lift_snd, w]
    exact (IsPullback.of_hasPullback p y).flip
  have left : IsPullback g (pullback.fst p y) fst f :=
    IsPullback.of_right big (h.lift_fst _ _ _) h.flip
  have : Surjective g := MorphismProperty.of_isPullback left.flip ‹Surjective f›
  exact g.surjective.connectedSpace g.continuous

/-- The chosen dual's structural morphism over any field is universally closed. -/
theorem fieldDualSchemeUniversallyClosed (k : Type u) [Field k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (hA : HasDualScheme A) : UniversallyClosed (dualScheme A hA).hom := by
  obtain ⟨f, hf⟩ := fieldDualSchemeSurjection k A hA
  have w : f.left ≫ (dualScheme A hA).hom = A.X.hom := Over.w f
  have : UniversallyClosed (f.left ≫ (dualScheme A hA).hom) := by
    rw [w]
    infer_instance
  exact .of_comp_surjective f.left _

/-- The chosen dual over any field is geometrically connected. -/
theorem fieldDualSchemeGeometricallyConnected (k : Type u) [Field k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (hA : HasDualScheme A) : GeometricallyConnected (dualScheme A hA).hom := by
  obtain ⟨f, hf⟩ := fieldDualSchemeSurjection k A hA
  exact geometricallyConnected_of_surjective f.left A.X.hom _ (Over.w f)

/-- Local finite type suffices for properness, using the published separatedness
and the universally closed structural morphism. -/
theorem fieldDualSchemeProper_of_locallyOfFiniteType (k : Type u) [Field k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (hA : HasDualScheme A) [LocallyOfFiniteType (dualScheme A hA).hom] :
    IsProper (dualScheme A hA).hom := by
  have : IsSeparated (dualScheme A hA).hom := fieldDualSchemeSeparated k A hA
  have : UniversallyClosed (dualScheme A hA).hom := fieldDualSchemeUniversallyClosed k A hA
  exact (isProper_iff _).mpr ⟨inferInstance, inferInstance, inferInstance⟩

/-- The remaining smoothness statement implies the full chosen-dual geometry
statement, with the same arbitrary fields and universe. -/
def FieldDualSchemeGeometryReductionStatement : Prop :=
  FieldDualSchemeSmoothStatement.{u} → FieldDualSchemeGeometryStatement.{u}

/-- Smoothness supplies the remaining local finite type input to the full
geometry statement for the chosen dual over every field. -/
theorem FieldDualSchemeGeometryStatement.of_smooth :
    FieldDualSchemeGeometryReductionStatement.{u} := by
  intro smooth k _ A hA
  have : Smooth (dualScheme A hA).hom := smooth k A hA
  exact ⟨inferInstance, fieldDualSchemeProper_of_locallyOfFiniteType k A hA,
    fieldDualSchemeGeometricallyConnected k A hA⟩

end Langlands.AbelianScheme

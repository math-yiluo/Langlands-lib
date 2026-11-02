import Langlands.AlgebraicGeometry.Picard.RelativeGeometry
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Ambient geometry for coherent families over a field -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.CoherentSheaves

variable {S X : Scheme.{u}}

/-- The geometric hypotheses on an ambient morphism used for coherent-family
algebraicity: separated, flat, and finitely presented. Finite presentation is
expressed by local finite presentation and quasi-compactness; separatedness
also supplies quasi-separatedness. -/
def HasAtlasAmbientGeometry (f : X ⟶ S) : Prop :=
  IsSeparated f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧ QuasiCompact f

/-- The ambient hypotheses hold on every actual relative space. -/
lemma HasAtlasAmbientGeometry.relativeProjection {f : X ⟶ S}
    (hf : HasAtlasAmbientGeometry f) (T : Over S) :
    HasAtlasAmbientGeometry ((Picard.relativeProjection f).app T) := by
  let : IsSeparated f := hf.1
  let : Flat f := hf.2.1
  let : LocallyOfFinitePresentation f := hf.2.2.1
  let : QuasiCompact f := hf.2.2.2
  change HasAtlasAmbientGeometry (pullback.fst T.hom f)
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- Every actual scheme over a field is flat over that field. -/
lemma flat_over_field (k : Type u) [Field k]
    (X : Over (Spec (CommRingCat.of k))) : Flat X.hom := by
  infer_instance

/-- Finite type over a field implies local finite presentation. -/
lemma locallyOfFinitePresentation_over_field (k : Type u) [Field k]
    (X : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType X.hom] :
    LocallyOfFinitePresentation X.hom := by
  infer_instance

/-- Properness over an arbitrary field supplies all ambient hypotheses. -/
lemma properField_hasAtlasAmbientGeometry (k : Type u) [Field k]
    (X : Over (Spec (CommRingCat.of k))) (hX : IsProper X.hom) :
    HasAtlasAmbientGeometry X.hom := by
  let : IsProper X.hom := hX
  exact ⟨inferInstance, flat_over_field k X,
    locallyOfFinitePresentation_over_field k X, inferInstance⟩

/-- The field reduction retains every test scheme in the full slice. -/
lemma properField_relativeProjection_hasAtlasAmbientGeometry
    (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))
    (hX : IsProper X.hom) (T : Over (Spec (CommRingCat.of k))) :
    HasAtlasAmbientGeometry ((Picard.relativeProjection X.hom).app T) :=
  (properField_hasAtlasAmbientGeometry k X hX).relativeProjection T

end Langlands.AlgebraicGeometry.CoherentSheaves

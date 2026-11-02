import Langlands.AlgebraicGeometry.Picard.EtaleFppfSheafComparison
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # The actual etale Picard class sheaf over a proper field scheme -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

namespace RelativePicard

/-- The actual canonical comparison is invertible exactly when the etale
class sheaf also satisfies fppf descent. -/
lemma etaleToFppfClassSheaf_isIso_iff {S X : Scheme.{u}} (f : X ⟶ S) :
    IsIso (etaleToFppfClassSheaf f) ↔
      Presheaf.IsSheaf (Scheme.fppfTopology.over S) (etaleClassSheafPresheaf f) := by
  constructor
  · intro h
    let e := (sheafToPresheaf (Scheme.etaleTopology.over S) (Type (u + 1))).mapIso
      (asIso (etaleToFppfClassSheaf f))
    exact (Presheaf.isSheaf_of_iso_iff e).mpr (classSheaf f).property
  · intro h
    rw [← etaleFppfClassSheafIso_hom f h]
    infer_instance

end RelativePicard

/-- For a proper scheme over an arbitrary field, the actual etale sheafification
of line-bundle classes is already an fppf sheaf on the entire scheme slice. -/
def FieldEtaleFppfClassSheafStatement : Prop :=
  ∀ (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k))),
    IsProper X.hom →
      Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of k)))
        (RelativePicard.etaleClassSheafPresheaf X.hom)

end Langlands.AlgebraicGeometry.Picard

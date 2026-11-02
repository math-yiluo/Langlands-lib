import Langlands.AlgebraicGeometry.Picard.GroupoidClasses
import Langlands.AlgebraicGeometry.Picard.EtaleFppfSheafComparison
import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic

/-! # Etale classes of the actual relative Picard groupoid -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The etale sheafification of the actual groupoid's isomorphism classes. -/
def relativeEtaleClassSheaf :
    Sheaf (Scheme.etaleTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.etaleTopology.over S) (Type (u + 1))).obj
    (relativeClassPresheaf f)

/-- Groupoid classes give the same etale sheaf as ordinary line-bundle classes. -/
def relativeEtaleClassSheafIso :
    relativeEtaleClassSheaf f ≅ RelativePicard.etaleClassSheaf f :=
  (presheafToSheaf (Scheme.etaleTopology.over S) (Type (u + 1))).mapIso
    (relativeClassPresheafIso f)

/-- The actual etale sheafification unit on groupoid classes. -/
def relativeToEtaleClassSheaf :
    relativeClassPresheaf f ⟶ (relativeEtaleClassSheaf f).obj :=
  toSheafify (Scheme.etaleTopology.over S) (relativeClassPresheaf f)

@[reassoc (attr := simp)]
lemma relativeToEtaleClassSheaf_comparison :
    relativeToEtaleClassSheaf f ≫ (relativeEtaleClassSheafIso f).hom.hom =
      (relativeClassPresheafIso f).hom ≫ RelativePicard.toEtaleClassSheaf f :=
  (toSheafify_naturality (Scheme.etaleTopology.over S)
    (relativeClassPresheafIso f).hom).symm

@[simp]
lemma relativeToEtaleClassSheaf_comparison_isoClass (T : Over S)
    (L : LineBundle ((relativeSpace f).obj T)) :
    (relativeEtaleClassSheafIso f).hom.hom.app (op T)
        ((relativeToEtaleClassSheaf f).app (op T) (isoClass ⟨L⟩)) =
      (RelativePicard.toEtaleClassSheaf f).app (op T)
        (RelativePicard.classOf f T L) :=
  congrArg (fun η ↦ η.app (op T) (isoClass ⟨L⟩))
    (relativeToEtaleClassSheaf_comparison f)

/-- The map from a scheme family to the etale sheaf of groupoid classes. -/
def etaleFamilyMap {U : Over S} (L : LineBundle ((relativeSpace f).obj U)) :
    (AlgebraicSpace.schemeYoneda S).obj U ⟶ (relativeEtaleClassSheaf f).obj :=
  uliftYonedaEquiv.symm
    ((relativeToEtaleClassSheaf f).app (op U) (isoClass ⟨L⟩))

/-- The whole family map agrees with the ordinary etale Picard class map. -/
@[reassoc]
lemma etaleFamilyMap_comparison {U : Over S}
    (L : LineBundle ((relativeSpace f).obj U)) :
    etaleFamilyMap f L ≫ (relativeEtaleClassSheafIso f).hom.hom =
      uliftYonedaEquiv.symm
        ((RelativePicard.toEtaleClassSheaf f).app (op U)
          (RelativePicard.classOf f U L)) := by
  rw [etaleFamilyMap, uliftYonedaEquiv_symm_comp,
    relativeToEtaleClassSheaf_comparison_isoClass]
  rfl

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid

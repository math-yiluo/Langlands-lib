import Langlands.AlgebraicGeometry.Picard.AtlasArrowPresheaf
import Langlands.AlgebraicGeometry.SmoothSurjectiveEtaleLocalSectionsStatement
import Langlands.AlgebraicGeometry.SmoothEtaleLocalSections

/-! # Etale local surjectivity of an actual smooth Picard atlas -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

variable {S X : Scheme.{u}} (f : X ⟶ S) {U : Over S}
  (L : LineBundle ((relativeSpace f).obj U))

/-- Actual smooth surjective point fibres locally cover every groupoid class. -/
theorem classFamilyMap_isLocallySurjective
    (hL : IsSmoothSurjectivePresentation f L) :
    CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (classFamilyMap f L) := by
  constructor
  intro T c
  induction c using Quotient.ind with
  | _ M =>
    obtain ⟨P, ⟨eP⟩, hsm, hsur⟩ := hL T M.of
    let V : Over S := (T.iteratedSliceBackward.obj P).left
    let p : V ⟶ T := (T.iteratedSliceBackward.obj P).hom
    let z : PointFiberPoints f L M.of P :=
      (eP.hom.app (op P) (ULift.up (𝟙 P))).down
    have : Smooth p.left := hsm
    have : Surjective p.left := hsur
    have hsec : SmoothSurjectiveEtaleLocalSectionsStatement.{u} :=
      fun _ _ g _ _ => hasEtaleLocalSections_of_smooth g
    have := AlgebraicSpace.isLocallySurjective_smooth_schemeYoneda_map hsec p
    apply (Scheme.etaleTopology.over S).superset_covering ?_
      (CategoryTheory.Presheaf.imageSieve_mem (Scheme.etaleTopology.over S)
        ((AlgebraicSpace.schemeYoneda S).map p)
        (ULift.up (𝟙 T) : ((AlgebraicSpace.schemeYoneda S).obj T).obj (op T)))
    intro W k hk
    obtain ⟨y, hy⟩ := hk
    have hy' : y.down ≫ p = k := by
      simpa using congrArg ULift.down hy
    exact ⟨ULift.up (y.down ≫ z.1),
      Quotient.sound ⟨Langlands.CategoryTheory.PseudofunctorPointFiber.pullIso
        z.2 y.down (y.down ≫ z.1) k rfl hy'⟩⟩

/-- The same family covers every section of the full etale class sheaf. -/
theorem etaleFamilyMap_isLocallySurjective
    (hL : IsSmoothSurjectivePresentation f L) :
    CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (etaleFamilyMap f L) := by
  have := classFamilyMap_isLocallySurjective f L hL
  have : CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (relativeToEtaleClassSheaf f) :=
    CategoryTheory.Presheaf.isLocallySurjective_toSheafify' _ _
  rw [← classFamilyMap_toEtale]
  infer_instance

/-- The actual etale family map bundled with its proved local surjectivity. -/
def locallySurjectiveEtaleFamilyMap
    (hL : IsSmoothSurjectivePresentation f L) :
    {a : (AlgebraicSpace.schemeYoneda S).obj U ⟶ (relativeEtaleClassSheaf f).obj //
      CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a} :=
  ⟨etaleFamilyMap f L, etaleFamilyMap_isLocallySurjective f L hL⟩

/-- Comparison transfers local surjectivity to ordinary etale Picard classes. -/
theorem ordinaryEtaleFamilyMap_isLocallySurjective
    (hL : IsSmoothSurjectivePresentation f L) :
    CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (uliftYonedaEquiv.{u + 1}.symm
        ((RelativePicard.toEtaleClassSheaf f).app (op U)
          (RelativePicard.classOf f U L))) := by
  have := etaleFamilyMap_isLocallySurjective f L hL
  have : IsIso (relativeEtaleClassSheafIso f).hom.hom :=
    ((sheafToPresheaf (Scheme.etaleTopology.over S) (Type (u + 1))).mapIso
      (relativeEtaleClassSheafIso f)).isIso_hom
  rw [← etaleFamilyMap_comparison f L]
  exact CategoryTheory.Presheaf.isLocallySurjective_comp (Scheme.etaleTopology.over S)
    (etaleFamilyMap f L) (relativeEtaleClassSheafIso f).hom.hom

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid

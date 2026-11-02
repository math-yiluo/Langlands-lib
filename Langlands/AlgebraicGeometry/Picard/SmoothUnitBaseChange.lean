import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeBaseChange
import Langlands.AlgebraicGeometry.Picard.RelativeAutomorphisms

/-! # A smooth global unit scheme gives actual relative automorphism schemes -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

variable {S X : Scheme.{u}} (f : X ⟶ S) (G : Over S)
  (e : (AlgebraicSpace.schemeYoneda S).obj G ≅ RelativeGlobalUnits.presheaf f)

/-- The actual base change of a unit scheme represents the full relative
automorphism presheaf of every bundle on every test scheme. -/
def relativeAutomorphismSchemeIsoOfUnitScheme (T : Over S)
    (L : LineBundle ((relativeSpace f).obj T)) :
    (AlgebraicSpace.schemeYoneda T.left).obj ((Over.pullback T.hom).obj G) ≅
      relativeSliceAutomorphismPresheaf f T L :=
  AlgebraicSpace.representedBaseChangeIso T.hom G e ≪≫
    relativeSliceUnitsAutomorphismPresheafIso f T L

include e in
/-- Smoothness of one actual global unit scheme persists on every test slice. -/
lemma hasSmoothUnitSchemes_of_unitScheme (hG : Smooth G.hom) :
    HasSmoothUnitSchemes f := by
  let := hG
  intro T
  refine ⟨(Over.pullback T.hom).obj G,
    ⟨AlgebraicSpace.representedBaseChangeIso T.hom G e⟩, ?_⟩
  change Smooth (CategoryTheory.Limits.pullback.snd G.hom T.hom)
  infer_instance

include e in
/-- One smooth global unit scheme gives all the actual smooth relative
automorphism schemes required by the quotient theorem. -/
lemma hasSmoothRelativeAutomorphismSchemes_of_unitScheme (hG : Smooth G.hom) :
    HasSmoothRelativeAutomorphismSchemes f :=
  (hasSmoothUnitSchemes_of_unitScheme f G e hG).hasSmoothRelativeAutomorphismSchemes f

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid

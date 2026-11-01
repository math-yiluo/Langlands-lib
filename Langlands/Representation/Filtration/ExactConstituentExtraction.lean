import Langlands.Representation.Filtration.ActualGradedExtraction
import Langlands.Representation.Filtration.ExactSmoothTransport
import Langlands.Representation.Filtration.LengthCriterionProof

/-! Extraction of a coarse irreducible constituent through an exact smooth
functor, using actual image filtrations and actual smooth subquotients. -/

noncomputable section

open CategoryTheory

namespace Langlands.ObjectRepFiltration

universe uG uH uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]
  {A : SmoothRep.{0, uG, uV} ℂ G} {r : ℕ}

/-- Regard an object filtration as a filtration of the constant smooth functor. -/
def onConstantSmooth (s : ObjectRepFiltration A.obj r) :
    RepFunctorFiltration
      (((Functor.const (Discrete PUnit.{1})).obj A) ⋙ SmoothRep.toRep) r := s

/-- The actual image filtration after applying a zero-preserving functor. -/
def exactSmoothImage (s : ObjectRepFiltration A.obj r)
    (J : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uV} ℂ H)
    [J.PreservesZeroMorphisms] : ObjectRepFiltration (J.obj A).obj r :=
  let t := s.onConstantSmooth.exactSmoothTransport J
  ofSubrepresentations
    (fun i => (t.step i).obj (Discrete.mk PUnit.unit))
    (t.monotone _) (t.zero _) (t.top _)

/-- Every grade of the image filtration is the functor applied to the original
actual smooth grade, when the functor preserves short exact sequences. -/
def exactSmoothImageGradedIso (s : ObjectRepFiltration A.obj r)
    (J : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uV} ℂ H)
    [J.PreservesZeroMorphisms]
    (hJ : Derivative.Mirabolic.MapsShortExactIntertwiners J) (j : Fin r) :
    (s.exactSmoothImage J).smoothGradedObject j ≅
      J.obj (s.smoothGradedObject j) :=
  SmoothRep.mkIso (Representation.equivOfIso
    ((s.onConstantSmooth.exactSmoothTransportGradedIso J hJ j).app
      (Discrete.mk PUnit.unit)))

/-- Each actual smooth grade is an actual subquotient of the filtered object. -/
theorem smoothGradedObject_isSubquotient (s : ObjectRepFiltration A.obj r) (j : Fin r) :
    SmoothRep.IsSubquotient (s.smoothGradedObject j) A :=
  SmoothRep.isSubquotient_iff_exists.mpr
    ⟨SmoothRep.subrepresentation A (s.subrepresentation j.succ),
      SmoothRep.subtype _ _, SmoothRep.mkQ _ _,
      SmoothRep.subtype_injective _ _, SmoothRep.mkQ_surjective _ _⟩

/-- Extract a grade of a supplied composition series before applying the exact
functor. The input occurrence need only be an actual subquotient. -/
theorem exists_simple_grade_of_subquotient_image
    (s : ObjectRepFiltration A.obj r) (hs : s.HasSimpleFactors)
    (J : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uV} ℂ H)
    [J.PreservesZeroMorphisms]
    (hJ : Derivative.Mirabolic.MapsShortExactIntertwiners J)
    {D : SmoothRep.{0, uH, uV} ℂ H} (hD : D.IsIrreducible)
    (hDA : SmoothRep.IsSubquotient D (J.obj A)) :
    ∃ j : Fin r,
      (s.smoothGradedObject j).IsIrreducible ∧
      SmoothRep.IsSubquotient (s.smoothGradedObject j) A ∧
      SmoothRep.IsSubquotient D (J.obj (s.smoothGradedObject j)) := by
  obtain ⟨j, hj⟩ :=
    (s.exactSmoothImage J).exists_smoothGradedObject_subquotient hD hDA
  exact ⟨j, hs j, s.smoothGradedObject_isSubquotient j,
    hj.of_iso_right (s.exactSmoothImageGradedIso J hJ j)⟩

/-- A constituent of the image of a finite-length object comes from a simple
actual subquotient of that object. No finite length of the image is required. -/
theorem exists_irreducible_subquotient_of_image
    (hA : A.HasFiniteLength)
    (J : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uV} ℂ H)
    [J.PreservesZeroMorphisms]
    (hJ : Derivative.Mirabolic.MapsShortExactIntertwiners J)
    {D : SmoothRep.{0, uH, uV} ℂ H} (hD : D.IsIrreducible)
    (hDA : SmoothRep.IsSubquotient D (J.obj A)) :
    ∃ E : SmoothRep.{0, uG, uV} ℂ G,
      E.IsIrreducible ∧ SmoothRep.IsSubquotient E A ∧
      SmoothRep.IsSubquotient D (J.obj E) := by
  obtain ⟨c, hzero, htop⟩ := isFiniteLength_iff_exists_compositionSeries.mp hA
  obtain ⟨s, hs⟩ :=
    LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries c hzero htop
  obtain ⟨j, hj⟩ := s.exists_simple_grade_of_subquotient_image hs J hJ hD hDA
  exact ⟨s.smoothGradedObject j, hj⟩

end Langlands.ObjectRepFiltration

import Langlands.Geometry.Analytic.OriginalDomainTopology
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

/-! # The dense site of actual original-chart domains -/

noncomputable section

universe u v w t s

namespace Langlands.Analytic

open Set CategoryTheory CategoryTheory.Limits Opposite

namespace IndexedAffinoidAtlas.OriginalChartDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}

/-- The actual domain subsets that are ranges of original charts. -/
def originalChartProperty (a : IndexedAffinoidAtlas.{u, v, w} K X) :
    ObjectProperty (OriginalChartDomain a) :=
  fun S => ∃ i : a.Index, ofChart i = S

/-- Original chart ranges, with every inclusion between them. Equal chart
ranges give the same object even when their supplied indices differ. -/
abbrev OriginalChart (a : IndexedAffinoidAtlas.{u, v, w} K X) :=
  (originalChartProperty a).FullSubcategory

/-- The fully faithful inclusion into the actual domain category. -/
abbrev originalChartInclusion (a : IndexedAffinoidAtlas.{u, v, w} K X) :
    OriginalChart a ⥤ OriginalChartDomain a :=
  (originalChartProperty a).ι

/-- Every supplied chart index gives an object of the chart category. -/
def originalChartObject (i : a.Index) : OriginalChart a :=
  ⟨ofChart i, ⟨i, rfl⟩⟩

@[simp]
theorem originalChartObject_obj (i : a.Index) :
    (originalChartObject i).obj = ofChart i := rfl

/-- The finite relative neighborhood witnesses of each domain give covering
arrows that factor through actual original-chart objects. -/
instance originalChartInclusion_isCoverDense :
    (originalChartInclusion a).IsCoverDense (quasinetTopology a) where
  is_cover S := by
    apply (quasinetTopology a).superset_covering ?_ (ofArrows_originalCharts_mem S)
    intro V f hf
    obtain ⟨c, g, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hf
    exact ⟨⟨originalChartObject c.val, g,
      homOfLE (show ofChart c.val ≤ S from c.property), rfl⟩⟩

/-- The induced quasinet topology on the actual original charts. -/
def originalChartTopology (a : IndexedAffinoidAtlas.{u, v, w} K X) :
    GrothendieckTopology (OriginalChart a) :=
  (originalChartInclusion a).inducedTopology (quasinetTopology a)

instance originalChartInclusion_isDenseSubsite :
    (originalChartInclusion a).IsDenseSubsite
      (originalChartTopology a) (quasinetTopology a) := by
  delta originalChartTopology
  infer_instance

/-- A chart sieve covers exactly when its actual image generates a
covering sieve of domains. -/
theorem mem_originalChartTopology {S : OriginalChart a} (R : Sieve S) :
    R ∈ originalChartTopology a S ↔
      R.functorPushforward (originalChartInclusion a) ∈
        quasinetTopology a S.obj :=
  (originalChartInclusion a).mem_inducedTopology_iff_of_isCoverDense
    (quasinetTopology a) R

/-- An arbitrarily indexed chart family covers precisely when its literal
subsets have finite relative neighborhood witnesses in the target chart. -/
theorem originalChart_ofArrows_mem_iff_locallyRefines {S : OriginalChart a}
    {ι : Type*} (D : ι → OriginalChart a) (f : ∀ i, D i ⟶ S) :
    Sieve.ofArrows D f ∈ originalChartTopology a S ↔
      AtlasTopology.LocallyRefines (Set.range (fun i => ((D i).obj : Set X)))
        {(S.obj : Set X)} := by
  rw [mem_originalChartTopology, Sieve.functorPushforward_ofArrows]
  exact ofArrows_mem_iff_locallyRefines _ _

/-- The intrinsic covering rule is the quasinet condition on the actual
target subspace. Empty index types are included. -/
theorem originalChart_ofArrows_mem_iff_isQuasinet {S : OriginalChart a}
    {ι : Type*} (D : ι → OriginalChart a) (f : ∀ i, D i ⟶ S) :
    Sieve.ofArrows D f ∈ originalChartTopology a S ↔
      AtlasTopology.IsQuasinet
        (AtlasTopology.restrictedFamily
          (Set.range (fun i => ((D i).obj : Set X))) (S.obj : Set X)) :=
  (originalChart_ofArrows_mem_iff_locallyRefines D f).trans
    (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).symm

/-- Restrict an actual domain sheaf to the original charts. This functor
itself needs no limit hypothesis on the value category. -/
def originalChartSheafRestriction (C : Type t) [Category.{s} C] :
    Sheaf (quasinetTopology a) C ⥤ Sheaf (originalChartTopology a) C :=
  (originalChartInclusion a).sheafPushforwardContinuous C
    (originalChartTopology a) (quasinetTopology a)

@[simp]
theorem originalChartSheafRestriction_obj_obj
    {C : Type t} [Category.{s} C] (F : Sheaf (quasinetTopology a) C)
    (S : OriginalChart a) :
    ((originalChartSheafRestriction C).obj F).obj.obj (op S) =
      F.obj.obj (op S.obj) := rfl

@[simp]
theorem originalChartSheafRestriction_obj_map
    {C : Type t} [Category.{s} C] (F : Sheaf (quasinetTopology a) C)
    {S T : OriginalChart a} (f : S ⟶ T) :
    ((originalChartSheafRestriction C).obj F).obj.map f.op =
      F.obj.map ((originalChartInclusion a).map f).op := rfl

/-- The actual sheaf categories are equivalent under precisely the
structured-arrow limit hypothesis used by Mathlib's comparison theorem. -/
def originalChartSheafEquivalence (C : Type t) [Category.{s} C]
    [∀ (S : (OriginalChartDomain a)ᵒᵖ),
      HasLimitsOfShape (StructuredArrow S (originalChartInclusion a).op) C] :
    Sheaf (originalChartTopology a) C ≌ Sheaf (quasinetTopology a) C :=
  (originalChartInclusion a).sheafInducedTopologyEquivOfIsCoverDense
    (quasinetTopology a) C

/-- The inverse of the comparison is literal restriction, including all
restriction maps rather than only the values at chart objects. -/
theorem originalChartSheafEquivalence_inverse
    (C : Type t) [Category.{s} C]
    [∀ (S : (OriginalChartDomain a)ᵒᵖ),
      HasLimitsOfShape (StructuredArrow S (originalChartInclusion a).op) C] :
    (originalChartSheafEquivalence (a := a) C).inverse =
      originalChartSheafRestriction (a := a) C := rfl

end IndexedAffinoidAtlas.OriginalChartDomain

namespace AffinoidAtlasPresentation

open IndexedAffinoidAtlas.OriginalChartDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : AffinoidAtlasPresentation.{u, v, w} K)

/-- Realize the chart site by the already constructed bounded subspace
presentations and their complete chosen inclusion arrows. -/
def originalChartFunctor : OriginalChart A.atlas ⥤ AffinoidAtlasPresentation.{u, v, w} K :=
  originalChartInclusion A.atlas ⋙ A.originalDomainFunctor

@[simp]
theorem originalChartFunctor_obj (S : OriginalChart A.atlas) :
    A.originalChartFunctor.obj S = A.originalDomainPresentation S.obj := rfl

@[simp]
theorem originalChartFunctor_obj_chart (i : A.atlas.Index) :
    A.originalChartFunctor.obj (originalChartObject i) = A.chartPresentation i := rfl

/-- The algebra maps retain the entire original bounded identities. -/
@[simp]
theorem originalChartFunctor_map_pullback {S T : OriginalChart A.atlas}
    (f : S ⟶ T) (c : (A.originalChartFunctor.obj S).atlas.Index) :
    (A.originalChartFunctor.map f).pullback c =
      BoundedAlgHom.id K (A.atlas.algebra c.val) := rfl

end AffinoidAtlasPresentation

end Langlands.Analytic

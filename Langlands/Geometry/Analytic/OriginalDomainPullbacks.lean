import Langlands.Geometry.Analytic.OriginalChartDomains
import Langlands.Geometry.Analytic.AtlasTopology.QuasinetProperties
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Pullbacks of actual original-chart-domain inclusions -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Topology CategoryTheory CategoryTheory.Limits

namespace AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : AffinoidAtlasPresentation.{u, v, w} K)

/-- Ambient inclusion is monic on the complete chosen bounded atlas data. -/
instance originalDomainInclusion_mono (S : A.atlas.OriginalChartDomain) :
    Mono (A.originalDomainInclusion S) where
  right_cancellation f g h := by
    apply Hom.ext
    · apply ContinuousMap.ext
      intro x
      apply Subtype.ext
      exact congrArg (fun k => k.baseMap x) h
    · funext i
      apply Subtype.ext
      exact congrArg (fun k => k.indexMap i) h
    · exact congr_arg_heq (fun k => k.pullback) h

/-- Nested domain inclusions are monic on the same complete data. -/
instance originalDomainMap_mono {S T : A.atlas.OriginalChartDomain} (h : S ≤ T) :
    Mono (A.originalDomainMap h) :=
  mono_of_mono_fac (A.originalDomainMap_inclusion h)

variable {A} {Z : AffinoidAtlasPresentation.{u, v, w} K}

namespace Hom

/-- Containment of the entire chosen target charts forces pointwise containment. -/
theorem baseMap_memOriginalDomain (f : Z ⟶ A) (S : A.atlas.OriginalChartDomain)
    (hc : ∀ i, Set.range (A.atlas.chart (f.indexMap i)) ⊆ S) (x : Z.space) :
    f.baseMap x ∈ S := by
  have hx : x ∈ ⋃₀ Set.range (fun i => Set.range (Z.atlas.chart i)) := by
    rw [Z.atlas.isNet_chartFamily.1.covers]
    trivial
  obtain ⟨U, ⟨i, rfl⟩, hi⟩ := Set.mem_sUnion.mp hx
  exact hc i (f.image_chart_subset i ⟨x, hi, rfl⟩)

/-- Restrict the codomain without changing any chosen bounded pullback. -/
def factorOriginalDomain (f : Z ⟶ A) (S : A.atlas.OriginalChartDomain)
    (hc : ∀ i, Set.range (A.atlas.chart (f.indexMap i)) ⊆ S) :
    Z ⟶ A.originalDomainPresentation S where
  baseMap := ⟨fun x => ⟨f.baseMap x, f.baseMap_memOriginalDomain S hc x⟩,
    f.baseMap.continuous.subtype_mk _⟩
  indexMap i := ⟨f.indexMap i, hc i⟩
  index_mono i j h := A.atlas.subspaceChart_subset S.carrier _ _ (f.index_mono i j h)
  pullback := f.pullback
  chart_comm i x := Subtype.ext (f.chart_comm i x)
  restriction_comm i j h := f.restriction_comm i j h

@[simp]
theorem factorOriginalDomain_apply (f : Z ⟶ A) (S : A.atlas.OriginalChartDomain)
    (hc : ∀ i, Set.range (A.atlas.chart (f.indexMap i)) ⊆ S) (x : Z.space) :
    ((f.factorOriginalDomain S hc).baseMap x).val = f.baseMap x := rfl

@[simp]
theorem factorOriginalDomain_index (f : Z ⟶ A) (S : A.atlas.OriginalChartDomain)
    (hc : ∀ i, Set.range (A.atlas.chart (f.indexMap i)) ⊆ S) (i : Z.atlas.Index) :
    ((f.factorOriginalDomain S hc).indexMap i).val = f.indexMap i := rfl

@[simp]
theorem factorOriginalDomain_pullback (f : Z ⟶ A) (S : A.atlas.OriginalChartDomain)
    (hc : ∀ i, Set.range (A.atlas.chart (f.indexMap i)) ⊆ S) (i : Z.atlas.Index) :
    (f.factorOriginalDomain S hc).pullback i = f.pullback i := rfl

@[simp]
theorem factorOriginalDomain_inclusion (f : Z ⟶ A) (S : A.atlas.OriginalChartDomain)
    (hc : ∀ i, Set.range (A.atlas.chart (f.indexMap i)) ⊆ S) :
    f.factorOriginalDomain S hc ≫ A.originalDomainInclusion S = f :=
  Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))

theorem factorOriginalDomain_unique (f : Z ⟶ A) (S : A.atlas.OriginalChartDomain)
    (hc : ∀ i, Set.range (A.atlas.chart (f.indexMap i)) ⊆ S)
    (g : Z ⟶ A.originalDomainPresentation S)
    (hg : g ≫ A.originalDomainInclusion S = f) :
    g = f.factorOriginalDomain S hc :=
  (cancel_mono (A.originalDomainInclusion S)).mp
    (hg.trans (f.factorOriginalDomain_inclusion S hc).symm)

end Hom

variable (A)

/-- Compatible complete ambient arrows select original charts in the intersection. -/
theorem originalDomainIntersection_chart_subset (S T : A.atlas.OriginalChartDomain)
    (f : Z ⟶ A.originalDomainPresentation S) (g : Z ⟶ A.originalDomainPresentation T)
    (h : f ≫ A.originalDomainInclusion S = g ≫ A.originalDomainInclusion T)
    (i : Z.atlas.Index) :
    Set.range (A.atlas.chart ((f ≫ A.originalDomainInclusion S).indexMap i)) ⊆ S ⊓ T := by
  intro x hx
  have hi : (f.indexMap i).val = (g.indexMap i).val :=
    congrArg (fun k => k.indexMap i) h
  refine ⟨(f.indexMap i).property hx, (g.indexMap i).property ?_⟩
  change x ∈ Set.range (A.atlas.chart (f.indexMap i).val) at hx
  rwa [← hi]

/-- The actual intersection lift retains the chosen bounded pullbacks of `f`. -/
def originalDomainIntersectionLift (S T : A.atlas.OriginalChartDomain)
    (f : Z ⟶ A.originalDomainPresentation S) (g : Z ⟶ A.originalDomainPresentation T)
    (h : f ≫ A.originalDomainInclusion S = g ≫ A.originalDomainInclusion T) :
    Z ⟶ A.originalDomainPresentation (S ⊓ T) :=
  (f ≫ A.originalDomainInclusion S).factorOriginalDomain (S ⊓ T)
    (A.originalDomainIntersection_chart_subset S T f g h)

@[simp]
theorem originalDomainIntersectionLift_apply (S T : A.atlas.OriginalChartDomain)
    (f : Z ⟶ A.originalDomainPresentation S) (g : Z ⟶ A.originalDomainPresentation T)
    (h : f ≫ A.originalDomainInclusion S = g ≫ A.originalDomainInclusion T)
    (x : Z.space) :
    ((A.originalDomainIntersectionLift S T f g h).baseMap x).val =
      (f.baseMap x).val := rfl

@[simp]
theorem originalDomainIntersectionLift_index (S T : A.atlas.OriginalChartDomain)
    (f : Z ⟶ A.originalDomainPresentation S) (g : Z ⟶ A.originalDomainPresentation T)
    (h : f ≫ A.originalDomainInclusion S = g ≫ A.originalDomainInclusion T)
    (i : Z.atlas.Index) :
    ((A.originalDomainIntersectionLift S T f g h).indexMap i).val =
      (f.indexMap i).val := rfl

@[simp]
theorem originalDomainIntersectionLift_pullback (S T : A.atlas.OriginalChartDomain)
    (f : Z ⟶ A.originalDomainPresentation S) (g : Z ⟶ A.originalDomainPresentation T)
    (h : f ≫ A.originalDomainInclusion S = g ≫ A.originalDomainInclusion T)
    (i : Z.atlas.Index) :
    (A.originalDomainIntersectionLift S T f g h).pullback i = f.pullback i := rfl

@[simp]
theorem originalDomainIntersectionLift_inclusion (S T : A.atlas.OriginalChartDomain)
    (f : Z ⟶ A.originalDomainPresentation S) (g : Z ⟶ A.originalDomainPresentation T)
    (h : f ≫ A.originalDomainInclusion S = g ≫ A.originalDomainInclusion T) :
    A.originalDomainIntersectionLift S T f g h ≫ A.originalDomainInclusion (S ⊓ T) =
      f ≫ A.originalDomainInclusion S :=
  (f ≫ A.originalDomainInclusion S).factorOriginalDomain_inclusion _ _

@[simp]
theorem originalDomainIntersectionLift_fst (S T : A.atlas.OriginalChartDomain)
    (f : Z ⟶ A.originalDomainPresentation S) (g : Z ⟶ A.originalDomainPresentation T)
    (h : f ≫ A.originalDomainInclusion S = g ≫ A.originalDomainInclusion T) :
    A.originalDomainIntersectionLift S T f g h ≫
      A.originalDomainMap (inf_le_left : S ⊓ T ≤ S) = f := by
  apply (cancel_mono (A.originalDomainInclusion S)).mp
  rw [Category.assoc, A.originalDomainMap_inclusion,
    A.originalDomainIntersectionLift_inclusion]

@[simp]
theorem originalDomainIntersectionLift_snd (S T : A.atlas.OriginalChartDomain)
    (f : Z ⟶ A.originalDomainPresentation S) (g : Z ⟶ A.originalDomainPresentation T)
    (h : f ≫ A.originalDomainInclusion S = g ≫ A.originalDomainInclusion T) :
    A.originalDomainIntersectionLift S T f g h ≫
      A.originalDomainMap (inf_le_right : S ⊓ T ≤ T) = g := by
  apply (cancel_mono (A.originalDomainInclusion T)).mp
  rw [Category.assoc, A.originalDomainMap_inclusion,
    A.originalDomainIntersectionLift_inclusion]
  exact h

/-- Even the first projection determines the complete lift, by monicity. -/
theorem originalDomainIntersectionLift_unique (S T : A.atlas.OriginalChartDomain)
    (f : Z ⟶ A.originalDomainPresentation S) (g : Z ⟶ A.originalDomainPresentation T)
    (h : f ≫ A.originalDomainInclusion S = g ≫ A.originalDomainInclusion T)
    (m : Z ⟶ A.originalDomainPresentation (S ⊓ T))
    (hm : m ≫ A.originalDomainMap (inf_le_left : S ⊓ T ≤ S) = f) :
    m = A.originalDomainIntersectionLift S T f g h :=
  (cancel_mono (A.originalDomainMap (inf_le_left : S ⊓ T ≤ S))).mp
    (hm.trans (A.originalDomainIntersectionLift_fst S T f g h).symm)

/-- The actual intersection presentation and its two bounded inclusions. -/
def originalDomainIntersectionCone (S T : A.atlas.OriginalChartDomain) :
    PullbackCone (A.originalDomainInclusion S) (A.originalDomainInclusion T) :=
  PullbackCone.mk (A.originalDomainMap (inf_le_left : S ⊓ T ≤ S))
    (A.originalDomainMap (inf_le_right : S ⊓ T ≤ T))
    (A.originalDomain_intersection_diamond S T)

/-- The universal property holds for complete chosen bounded atlas arrows. -/
def originalDomainIntersectionIsLimit (S T : A.atlas.OriginalChartDomain) :
    IsLimit (A.originalDomainIntersectionCone S T) :=
  PullbackCone.IsLimit.mk (A.originalDomain_intersection_diamond S T)
    (fun c => A.originalDomainIntersectionLift S T c.fst c.snd c.condition)
    (fun c => A.originalDomainIntersectionLift_fst S T c.fst c.snd c.condition)
    (fun c => A.originalDomainIntersectionLift_snd S T c.fst c.snd c.condition)
    (fun c m hm _ => A.originalDomainIntersectionLift_unique S T c.fst c.snd c.condition m hm)

theorem originalDomainIntersection_isPullback (S T : A.atlas.OriginalChartDomain) :
    IsPullback (A.originalDomainMap (inf_le_left : S ⊓ T ≤ S))
      (A.originalDomainMap (inf_le_right : S ⊓ T ≤ T))
      (A.originalDomainInclusion S) (A.originalDomainInclusion T) where
  w := A.originalDomain_intersection_diamond S T
  isLimit' := ⟨A.originalDomainIntersectionIsLimit S T⟩

end AffinoidAtlasPresentation

end Langlands.Analytic

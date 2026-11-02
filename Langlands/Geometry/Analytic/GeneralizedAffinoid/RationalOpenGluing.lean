import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalOpenSections
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartOpenRefinement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteRationalGluingProof
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Category.Ring.Limits

/-! # Actual algebra descent on arbitrary topological open covers -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory TopologicalSpace

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

namespace OpenSections

private theorem finite_gluing {d : RationalChart K A} {n : ℕ}
    (D : Fin n → RationalChart K A) (f : ∀ i, D i ⟶ d)
    (hc : ∀ x ∈ d.locus, ∃ i, x ∈ (D i).locus)
    (s : ∀ i, (D i).algebra)
    (hs : ∀ i j, (interLeft (D i) (D j)).restriction (s i) =
      (interRight (D i) (D j)).restriction (s j)) :
    ∃! a : d.algebra, ∀ i, (f i).restriction a = s i := by
  obtain ⟨a, ha, hu⟩ := finiteRationalGluing K A d (ULift.{u} (Fin n))
    (fun i => D i.down) (fun i => f i.down)
    (by
      intro x hx
      obtain ⟨i, hi⟩ := hc x hx
      exact ⟨⟨i⟩, hi⟩)
    (fun i => s i.down) (fun i j => hs i.down j.down)
  exact ⟨a, fun i => ha ⟨i⟩, fun b hb => hu b (fun i => hb i.down)⟩

private theorem finite_ext {d : RationalChart K A} {n : ℕ}
    (D : Fin n → RationalChart K A) (f : ∀ i, D i ⟶ d)
    (hc : ∀ x ∈ d.locus, ∃ i, x ∈ (D i).locus)
    {a b : d.algebra} (hab : ∀ i, (f i).restriction a = (f i).restriction b) :
    a = b := by
  have hs : ∀ i j,
      (interLeft (D i) (D j)).restriction ((f i).restriction a) =
        (interRight (D i) (D j)).restriction ((f j).restriction a) := by
    intro i j
    exact congrArg (fun h : (D i).inter (D j) ⟶ d => h.restriction a)
      (@Subsingleton.elim (Restriction ((D i).inter (D j)) d) inferInstance
        (interLeft (D i) (D j) ≫ f i) (interRight (D i) (D j) ≫ f j))
  obtain ⟨z, _, hz⟩ := finite_gluing D f hc (fun i => (f i).restriction a) hs
  exact (hz a (fun _ => rfl)).trans (hz b (fun i => (hab i).symm)).symm

variable {I : Type v} (U : I → Opens (BanachSpectrum A))

/-- Matching local sections agree on every actual rational chart contained
in both members of the open cover. -/
def LocalCompatible (s : ∀ i, Sections (U i : Set (BanachSpectrum A))) : Prop :=
  ∀ i j (d : RationalChart K A) (hi : d.locus ⊆ U i) (hj : d.locus ⊆ U j),
    (s i).val ⟨d, hi⟩ = (s j).val ⟨d, hj⟩

/-- Restrict the open cover to the rational locus and construct its finite
actual subordinate refinement. -/
def openRefinement (d : ChartIn ((iSup U : Opens (BanachSpectrum A)) : Set (BanachSpectrum A))) :
    FiniteOpenRefinement d.val (fun i => Subtype.val ⁻¹' (U i : Set (BanachSpectrum A))) :=
  FiniteOpenRefinement.ofOpenCover d.val _
    (fun i => (U i).isOpen.preimage continuous_subtype_val)
    (fun x => Opens.mem_iSup.mp (d.property x.property))

variable {U}

private def componentIn {d : RationalChart K A}
    (c : FiniteOpenRefinement d (fun i => Subtype.val ⁻¹'
      (U i : Set (BanachSpectrum A)))) (j : Fin c.size) :
    ChartIn (U (c.label j) : Set (BanachSpectrum A)) :=
  ⟨c.chart j, fun x hx => c.subordinate_point j x hx⟩

private theorem local_family_compatible {d : RationalChart K A}
    (c : FiniteOpenRefinement d (fun i => Subtype.val ⁻¹'
      (U i : Set (BanachSpectrum A))))
    (s : ∀ i, Sections (U i : Set (BanachSpectrum A))) (hs : LocalCompatible U s) :
    ∀ i j,
      (interLeft (c.chart i) (c.chart j)).restriction ((s (c.label i)).val (componentIn c i)) =
        (interRight (c.chart i) (c.chart j)).restriction
          ((s (c.label j)).val (componentIn c j)) := by
  intro i j
  let e := (c.chart i).inter (c.chart j)
  have hi : e.locus ⊆ U (c.label i) :=
    (interLeft (c.chart i) (c.chart j)).subset.trans (componentIn c i).property
  have hj : e.locus ⊆ U (c.label j) :=
    (interRight (c.chart i) (c.chart j)).subset.trans (componentIn c j).property
  exact ((s (c.label i)).property ⟨e, hi⟩ (componentIn c i)
    (interLeft (c.chart i) (c.chart j))).trans
      ((hs _ _ e hi hj).trans
        ((s (c.label j)).property ⟨e, hj⟩ (componentIn c j)
          (interRight (c.chart i) (c.chart j))).symm)

/-- The actual element of the target rational quotient obtained from finite
analytic descent of the local section components. -/
def glueChart {d : RationalChart K A}
    (c : FiniteOpenRefinement d (fun i => Subtype.val ⁻¹'
      (U i : Set (BanachSpectrum A))))
    (s : ∀ i, Sections (U i : Set (BanachSpectrum A))) (hs : LocalCompatible U s) :
    d.algebra :=
  (finite_gluing c.chart c.map c.covers
    (fun j => (s (c.label j)).val (componentIn c j))
    (local_family_compatible c s hs)).choose

theorem glueChart_refinement {d : RationalChart K A}
    (c : FiniteOpenRefinement d (fun i => Subtype.val ⁻¹'
      (U i : Set (BanachSpectrum A))))
    (s : ∀ i, Sections (U i : Set (BanachSpectrum A))) (hs : LocalCompatible U s)
    (j : Fin c.size) :
    (c.map j).restriction (glueChart c s hs) =
      (s (c.label j)).val (componentIn c j) :=
  (finite_gluing c.chart c.map c.covers
    (fun j => (s (c.label j)).val (componentIn c j))
    (local_family_compatible c s hs)).choose_spec.1 j

/-- The descended quotient element agrees with every original local section
on every actual contained rational test, independently of the refinement. -/
theorem glueChart_local {d e : RationalChart K A}
    (c : FiniteOpenRefinement d (fun i => Subtype.val ⁻¹'
      (U i : Set (BanachSpectrum A))))
    (s : ∀ i, Sections (U i : Set (BanachSpectrum A))) (hs : LocalCompatible U s)
    (i : I) (f : e ⟶ d) (he : e.locus ⊆ U i) :
    f.restriction (glueChart c s hs) = (s i).val ⟨e, he⟩ := by
  apply finite_ext (fun j => e.inter (c.chart j))
    (fun j => interLeft e (c.chart j))
    (by
      intro x hx
      obtain ⟨j, hj⟩ := c.covers x (f.subset hx)
      exact ⟨j, by rw [locus_inter]; exact ⟨hx, hj⟩⟩)
  intro j
  let w := e.inter (c.chart j)
  have hwi : w.locus ⊆ U i := (interLeft e (c.chart j)).subset.trans he
  have hwj : w.locus ⊆ U (c.label j) :=
    (interRight e (c.chart j)).subset.trans (componentIn c j).property
  calc
    (interLeft e (c.chart j)).restriction (f.restriction (glueChart c s hs)) =
        (interRight e (c.chart j)).restriction ((c.map j).restriction (glueChart c s hs)) :=
      congrArg (fun g : w ⟶ d => g.restriction (glueChart c s hs))
        (@Subsingleton.elim (Restriction w d) inferInstance
          (interLeft e (c.chart j) ≫ f) (interRight e (c.chart j) ≫ c.map j))
    _ = (interRight e (c.chart j)).restriction
        ((s (c.label j)).val (componentIn c j)) :=
      congrArg (interRight e (c.chart j)).restriction (glueChart_refinement c s hs j)
    _ = (s (c.label j)).val ⟨w, hwj⟩ :=
      (s (c.label j)).property ⟨w, hwj⟩ (componentIn c j) (interRight e (c.chart j))
    _ = (s i).val ⟨w, hwi⟩ := hs _ _ w hwj hwi
    _ = (interLeft e (c.chart j)).restriction ((s i).val ⟨e, he⟩) :=
      ((s i).property ⟨w, hwi⟩ ⟨e, he⟩ (interLeft e (c.chart j))).symm

/-- Glue the actual quotient elements on all rational charts contained in the
union. The local-test equation proves compatibility under bounded restrictions. -/
def glue (s : ∀ i, Sections (U i : Set (BanachSpectrum A))) (hs : LocalCompatible U s) :
    Sections ((iSup U : Opens (BanachSpectrum A)) : Set (BanachSpectrum A)) := by
  refine ⟨fun d => glueChart (openRefinement U d) s hs, ?_⟩
  intro d e f
  let c := openRefinement U d
  apply finite_ext c.chart c.map c.covers
  intro j
  exact (glueChart_local (openRefinement U e) s hs (c.label j) (c.map j ≫ f)
    (componentIn c j).property).trans (glueChart_refinement c s hs j).symm

@[simp]
theorem restriction_glue (s : ∀ i, Sections (U i : Set (BanachSpectrum A)))
    (hs : LocalCompatible U s) (i : I) :
    restriction (show (U i : Set (BanachSpectrum A)) ⊆
      ((iSup U : Opens (BanachSpectrum A)) : Set (BanachSpectrum A)) from le_iSup U i)
      (glue s hs) = s i := by
  apply ext
  intro d
  exact glueChart_local
    (openRefinement U ⟨d.val, d.property.trans (le_iSup U i)⟩)
    s hs i (𝟙 d.val) d.property

/-- Compatible actual algebra sections on any topological open family have
a unique section on its union. The label universe is independent of K. -/
theorem existsUnique (s : ∀ i, Sections (U i : Set (BanachSpectrum A)))
    (hs : LocalCompatible U s) :
    ∃! t : Sections ((iSup U : Opens (BanachSpectrum A)) : Set (BanachSpectrum A)),
      ∀ i, restriction (show (U i : Set (BanachSpectrum A)) ⊆
        ((iSup U : Opens (BanachSpectrum A)) : Set (BanachSpectrum A))
          from le_iSup U i) t = s i := by
  refine ⟨glue s hs, restriction_glue s hs, ?_⟩
  intro t ht
  apply ext
  intro d
  let c := openRefinement U d
  apply finite_ext c.chart c.map c.covers
  intro j
  have hlocal : t.val ⟨c.chart j, (c.map j).subset.trans d.property⟩ =
      (s (c.label j)).val (componentIn c j) :=
    congrArg (fun z : Sections (U (c.label j) : Set (BanachSpectrum A)) =>
      z.val (componentIn c j)) (ht (c.label j))
  exact (t.property ⟨c.chart j, (c.map j).subset.trans d.property⟩ d (c.map j)).trans
    (hlocal.trans (glueChart_refinement c s hs j).symm)

omit [CompleteSpace K] in
/-- Agreement on every common rational test is exactly ordinary presheaf
compatibility on pairwise intersections of topological opens. -/
theorem localCompatible_iff_isCompatible
    (s : ∀ i, Sections (U i : Set (BanachSpectrum A))) :
    LocalCompatible U s ↔
      TopCat.Presheaf.IsCompatible (X := TopCat.of (BanachSpectrum A))
        (openAlgebraPresheaf K A) U s := by
  constructor
  · intro hs i j
    apply ext
    intro d
    exact hs i j d.val (fun x hx => (d.property hx).1)
      (fun x hx => (d.property hx).2)
  · intro hs i j d hi hj
    exact congrArg
      (fun z : Sections ((U i ⊓ U j : Opens (BanachSpectrum A)) :
        Set (BanachSpectrum A)) =>
        z.val ⟨d, fun x hx => ⟨hi hx, hj hx⟩⟩)
      (hs i j)

end OpenSections

open CategoryTheory.Limits

/-- Actual compatible rational algebra families satisfy descent for every
topological open cover of the affinoid spectrum. -/
theorem openAlgebraPresheaf_isSheaf :
    TopCat.Presheaf.IsSheaf (X := TopCat.of (BanachSpectrum A))
      (openAlgebraPresheaf K A) := by
  let : PreservesLimits (forget (CommAlgCat K)) := by
    change PreservesLimits ((commAlgCatEquivUnder (CommRingCat.of K)).functor ⋙
      Under.forget (CommRingCat.of K) ⋙ forget CommRingCat)
    infer_instance
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).2
  intro I U s hs
  exact OpenSections.existsUnique s
    ((OpenSections.localCompatible_iff_isCompatible s).2 hs)

variable (K A)

/-- The actual algebra sheaf on ordinary topological opens, with the original
compatible-family presheaf and its constructed finite rational descent. -/
def openAlgebraSheaf :
    TopCat.Sheaf (CommAlgCat K) (TopCat.of (BanachSpectrum A)) :=
  ⟨openAlgebraPresheaf K A, openAlgebraPresheaf_isSheaf⟩

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

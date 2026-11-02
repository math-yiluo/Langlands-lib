import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorImages
import Mathlib.AlgebraicGeometry.Cover.Open

/-! # Unions of represented open charts -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.OpenChartUnion

variable {S : Scheme.{u}} {F : Presheaf S} {I : Type u} {U : I → Over S}
  (a : ∀ i, (schemeYoneda S).obj (U i) ⟶ F)

/-- The fppf local union of the ranges of the chart family. -/
def union : Subfunctor F :=
  (Subfunctor.range (Sigma.desc a)).sheafify (fppfTopology S)

/-- The canonical map of a chart to the local union. -/
def chart (i : I) : (schemeYoneda S).obj (U i) ⟶ (union a).toFunctor :=
  Sigma.ι (fun i => (schemeYoneda S).obj (U i)) i ≫
    Subfunctor.toRangeSheafify (fppfTopology S) (Sigma.desc a)

@[reassoc (attr := simp)]
theorem chart_ι (i : I) : chart a i ≫ (union a).ι = a i := by
  ext T x
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (Sigma.ι_comp_desc a i) T) x

/-- Each chart square with the union inclusion is cartesian. -/
theorem chart_isPullback (i : I) :
    IsPullback (𝟙 _) (chart a i) (a i) (union a).ι :=
  IsPullback.of_horiz_isIso_mono ⟨by simp⟩

theorem chart_isOpenImmersion (ha : ∀ i, IsOpenImmersion (a i)) (i : I) :
    IsOpenImmersion (chart a i) := by
  let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
    (SliceOpenGluing.openProperty S)
  exact MorphismProperty.of_isPullback
    (P := (SliceOpenGluing.openProperty S).relative (schemeYoneda S))
    (chart_isPullback a i) (ha i)

instance chart_locallySurjective :
    CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S)
      (Sigma.desc (chart a)) := by
  have h : Sigma.desc (chart a) =
      Subfunctor.toRangeSheafify (fppfTopology S) (Sigma.desc a) := by
    apply Sigma.hom_ext
    intro i
    exact Sigma.ι_comp_desc (chart a) i
  rw [h]
  constructor
  rintro T ⟨x, hx⟩
  apply (fppfTopology S).superset_covering ?_ hx
  rintro V f ⟨y, hy⟩
  exact ⟨y, Subtype.ext hy⟩

theorem union_isSheaf
    (hF : CategoryTheory.Presheaf.IsSheaf (fppfTopology S) F) :
    CategoryTheory.Presheaf.IsSheaf (fppfTopology S) (union a).toFunctor := by
  rw [CategoryTheory.isSheaf_iff_isSheaf_of_type] at hF ⊢
  exact Subfunctor.sheafify_isSheaf _ hF

/-- The actual scheme obtained by gluing the charts along their overlaps. -/
def scheme (ha : ∀ i, IsOpenImmersion (a i)) : Over S :=
  SliceOpenGluing.glued (chart_isOpenImmersion a ha)

/-- The actual gluing represents the local union of the chart ranges. -/
def iso (hF : CategoryTheory.Presheaf.IsSheaf (fppfTopology S) F)
    (ha : ∀ i, IsOpenImmersion (a i)) :
    (schemeYoneda S).obj (scheme a ha) ≅ (union a).toFunctor :=
  (sheafToPresheaf _ _).mapIso
    (SliceOpenGluing.yonedaIsoSheaf
      (G := ⟨(union a).toFunctor, union_isSheaf a hF⟩)
      (chart_isOpenImmersion a ha))

/-- A finite union of compact represented open charts has a compact representer. -/
instance scheme_compactSpace [Finite I] [hU : ∀ i, CompactSpace (U i).left]
    (ha : ∀ i, IsOpenImmersion (a i)) : CompactSpace (scheme a ha).left := by
  let 𝒰 := (SliceOpenGluing.schemeData (chart_isOpenImmersion a ha)).openCover
  let : Finite 𝒰.I₀ := inferInstanceAs (Finite I)
  let : ∀ i, CompactSpace (𝒰.X i) := fun i => hU i
  exact 𝒰.compactSpace

theorem range_sigma_desc :
    Subfunctor.range (Sigma.desc a) = ⨆ i, Subfunctor.range (a i) := by
  ext T x
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨⟨i⟩, y, rfl⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves ((evaluation _ _).obj T)
        (coproductIsCoproduct (fun i => (schemeYoneda S).obj (U i)))) z
    rw [Subfunctor.iSup_obj, Set.mem_iUnion]
    refine ⟨i, y, ?_⟩
    exact (ConcreteCategory.congr_hom
      (NatTrans.congr_app (Sigma.ι_comp_desc a i) T) y).symm
  · rw [Subfunctor.iSup_obj]
    rintro ⟨_, ⟨i, rfl⟩, y, rfl⟩
    refine ⟨(Sigma.ι (fun i => (schemeYoneda S).obj (U i)) i).app T y, ?_⟩
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (Sigma.ι_comp_desc a i) T) y

theorem union_eq_sheafify_iSup :
    union a = (⨆ i, Subfunctor.range (a i)).sheafify (fppfTopology S) := by
  rw [union, range_sigma_desc]

end Langlands.AlgebraicGeometry.AlgebraicSpace.OpenChartUnion

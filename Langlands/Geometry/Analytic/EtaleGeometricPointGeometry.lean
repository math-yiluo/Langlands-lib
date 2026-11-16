import Langlands.Geometry.Analytic.EtaleGeometricPointStatement
import Langlands.CategoryTheory.Sites.PointwiseCovering

/-! # Geometric inputs for points of the analytic étale site -/

noncomputable section

universe u v uL uC vC w

namespace Langlands.Analytic.SaturatedAtlasPresentation.EtaleSite

open _root_.CategoryTheory

/-- A cofiltered category of elements supplies pointwise lifting squares. -/
private theorem hasPointwiseLiftingSquares_of_cofiltered
    {C : Type uC} [Category.{vC} C] (F : C ⥤ Type w) [IsCofiltered F.Elements] :
    Langlands.CategoryTheory.PointwiseCovering.HasPointwiseLiftingSquares F := by
  intro X Y S f g x y h
  let ex := Functor.elementsMk F X x
  let ey := Functor.elementsMk F Y y
  let es := Functor.elementsMk F S (F.map f x)
  let ef : ex ⟶ es := ⟨f, rfl⟩
  let eg : ey ⟶ es := ⟨g, h.symm⟩
  obtain ⟨T, p, q, hpq⟩ := IsCofiltered.cospan ef eg
  exact ⟨T.obj, p.hom, q.hom, congrArg Functor.Elements.Hom.hom hpq,
    T.val, p.map_val, q.map_val⟩

/-- Compatible field-valued points of two étale objects have a common
étale refinement, retaining their prescribed field-valued evaluations. -/
def GeometricPointRefinementStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type uL) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L]
    [NormedAlgebra K L] (X : LocalizedCategory.{u, v, v} (K := K))
    (U V : EtaleSite X) (p : (localizedFieldPointFunctor L).obj U.left)
    (q : (localizedFieldPointFunctor L).obj V.left),
    (localizedFieldPointFunctor L).map U.hom p =
      (localizedFieldPointFunctor L).map V.hom q →
    ∃ (W : EtaleSite X) (f : W ⟶ U) (g : W ⟶ V)
      (r : (localizedFieldPointFunctor L).obj W.left),
      (localizedFieldPointFunctor L).map f.left r = p ∧
        (localizedFieldPointFunctor L).map g.left r = q

/-- Parallel site arrows that agree on a prescribed field-valued point
can be equalized on an étale refinement containing a lift of that point. -/
def GeometricPointEqualizationStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type uL) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L]
    [NormedAlgebra K L] (X : LocalizedCategory.{u, v, v} (K := K))
    (U V : EtaleSite X) (f g : U ⟶ V)
    (p : (localizedFieldPointFunctor L).obj U.left),
    (localizedFieldPointFunctor L).map f.left p =
      (localizedFieldPointFunctor L).map g.left p →
    ∃ (W : EtaleSite X) (h : W ⟶ U)
      (q : (localizedFieldPointFunctor L).obj W.left),
      h ≫ f = h ≫ g ∧ (localizedFieldPointFunctor L).map h.left q = p

/-- A field-valued point lifts through a site arrow whenever its underlying
ordinary point lies in the image of that arrow. -/
def GeometricPointImageLiftStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type uL) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L]
    [NormedAlgebra K L] (X : LocalizedCategory.{u, v, v} (K := K))
    (U V : EtaleSite X) (f : V ⟶ U)
    (p : (localizedFieldPointFunctor L).obj U.left),
    ((localizedFieldPointProjection L).app U.left p).down ∈
      Set.range ((points X).map f) →
    ∃ q : (localizedFieldPointFunctor L).obj V.left,
      (localizedFieldPointFunctor L).map f.left q = p

/-- The three geometric inputs of the finite-diagram and covering argument. -/
def GeometricPointGeometryStatement : Prop :=
  GeometricPointRefinementStatement.{u, v, uL} ∧
    GeometricPointEqualizationStatement.{u, v, uL} ∧
      GeometricPointImageLiftStatement.{u, v, uL}

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type uL) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L]
  [NormedAlgebra K L] {X : LocalizedCategory.{u, v, v} (K := K)}

omit [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L] in
/-- The identity object gives an element of the geometric fibre. -/
theorem pointFibre_elements_nonempty (x : (localizedFieldPointFunctor L).obj X) :
    Nonempty (pointFibre L x).Elements := by
  let U : EtaleSite X := MorphismProperty.Over.mk ⊤ (𝟙 X) (etale_of_isIso _)
  exact ⟨Functor.elementsMk _ U ⟨x, (localizedFieldPointFunctor L).map_id_apply X x⟩⟩

/-- Common refinements and local equalization imply cofilteredness. -/
theorem pointFibre_isCofiltered_of_geometry
    (hR : GeometricPointRefinementStatement.{u, v, uL})
    (hE : GeometricPointEqualizationStatement.{u, v, uL})
    (x : (localizedFieldPointFunctor L).obj X) :
    IsCofiltered (pointFibre L x).Elements where
  nonempty := pointFibre_elements_nonempty L x
  cone_objs a b := by
    obtain ⟨W, f, g, r, hf, hg⟩ := hR K L X a.obj b.obj a.val.1 b.val.1
      (a.val.2.trans b.val.2.symm)
    have hr : (localizedFieldPointFunctor L).map W.hom r = x := by
      rw [← MorphismProperty.Over.w f, Functor.map_comp_apply, hf]
      exact a.val.2
    exact ⟨Functor.elementsMk _ W ⟨r, hr⟩,
      ⟨f, Subtype.ext hf⟩, ⟨g, Subtype.ext hg⟩, trivial⟩
  cone_maps {a b} f g := by
    have hfg : (localizedFieldPointFunctor L).map f.hom.left a.val.1 =
        (localizedFieldPointFunctor L).map g.hom.left a.val.1 :=
      (congrArg Subtype.val f.map_val).trans (congrArg Subtype.val g.map_val).symm
    obtain ⟨W, h, q, heq, hq⟩ := hE K L X a.obj b.obj f.hom g.hom a.val.1 hfg
    have hqx : (localizedFieldPointFunctor L).map W.hom q = x := by
      rw [← MorphismProperty.Over.w h, Functor.map_comp_apply, hq]
      exact a.val.2
    refine ⟨Functor.elementsMk _ W ⟨q, hqx⟩, ⟨h, Subtype.ext hq⟩, ?_⟩
    exact Functor.Elements.Hom.ext heq

/-- Ordinary jointly surjective presieves lift every geometric fibre element
under the image-lifting input. -/
theorem pointFibre_cover_lifting_of_imageLift
    (hL : GeometricPointImageLiftStatement.{u, v, uL})
    (x : (localizedFieldPointFunctor L).obj X) {U : EtaleSite X}
    (R : Presieve U) (hR : R ∈ etalePrecoverage X U)
    (p : (pointFibre L x).obj U) :
    ∃ (V : EtaleSite X) (f : V ⟶ U), R f ∧
      p ∈ Set.range ((pointFibre L x).map f) := by
  obtain ⟨V, f, hf, hpoint⟩ := mem_etalePrecoverage_iff.mp hR
    (((localizedFieldPointProjection L).app U.left p.1).down)
  obtain ⟨q, hq⟩ := hL K L X U V f p.1 hpoint
  have hqx : (localizedFieldPointFunctor L).map V.hom q = x := by
    rw [← MorphismProperty.Over.w f, Functor.map_comp_apply, hq]
    exact p.2
  exact ⟨V, f, hf, ⟨q, hqx⟩, Subtype.ext hq⟩

/-- Cofilteredness and image lifting establish surjectivity for the entire
generated topology, including its pullback and transitivity saturation. -/
theorem pointFibre_jointlySurjective_of_geometry
    (hL : GeometricPointImageLiftStatement.{u, v, uL})
    (x : (localizedFieldPointFunctor L).obj X)
    [IsCofiltered (pointFibre L x).Elements] {U : EtaleSite X} (R : Sieve U)
    (hR : R ∈ etaleTopology X U) :
    ∀ p : (pointFibre L x).obj U,
      ∃ (V : EtaleSite X) (f : V ⟶ U) (_ : R f)
        (q : (pointFibre L x).obj V), (pointFibre L x).map f q = p := by
  have hpre : etalePrecoverage X ≤
      Types.jointlySurjectivePrecoverage.comap (pointFibre L x) := by
    intro U S hS
    exact (Presieve.mem_comap_jointlySurjectivePrecoverage_iff _).mpr
      (pointFibre_cover_lifting_of_imageLift L hL x S hS)
  have hgeo := Langlands.CategoryTheory.PointwiseCovering.isJointlySurjective_of_mem_toGrothendieck
      (hasPointwiseLiftingSquares_of_cofiltered (pointFibre L x))
      (Precoverage.toGrothendieck_mono hpre _ hR)
  intro p
  obtain ⟨V, f, hf, q, hq⟩ := hgeo p
  exact ⟨V, f, hf, q, hq⟩

/-- The three geometric inputs imply the exact published target. -/
theorem geometricPointStatement_of_geometry
    (h : GeometricPointGeometryStatement.{u, v, uL}) :
    GeometricPointStatement.{u, v, uL} := by
  intro K _ _ _ L _ _ _ _ _ X x
  let := pointFibre_isCofiltered_of_geometry L h.1 h.2.1 x
  exact ⟨inferInstance, pointFibre_jointlySurjective_of_geometry L h.2.2 x⟩

end Langlands.Analytic.SaturatedAtlasPresentation.EtaleSite

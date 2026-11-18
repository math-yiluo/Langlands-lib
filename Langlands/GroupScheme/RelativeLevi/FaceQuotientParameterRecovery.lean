import Langlands.GroupScheme.RelativeLevi.FaceQuotientComponentRecovery

/-! # Original term and quotient recovery after arbitrary chart restriction -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent

/-- A genuine original base-change square remains the same square on a further
parameter, through the prescribed actual direct pullback comparisons. -/
lemma directParameter_square {S X Y : Scheme.{u}} (f : X ⟶ S) (b : Y ⟶ X)
    (a : Y ⟶ S) (hb : b ≫ f = a)
    {K Q : GroupScheme S} {L W : GroupScheme X}
    (q : K ⟶ Q) (eK : (baseChange f).obj K ≅ L)
    (eQ : (baseChange f).obj Q ≅ W) (v : L ⟶ W)
    (he : (baseChange f).map q ≫ eQ.hom = eK.hom ≫ v) :
    (baseChange a).map q ≫
        (pullbackComparison f b a hb Q).inv ≫ (baseChange b).map eQ.hom =
      (pullbackComparison f b a hb K).inv ≫
        (baseChange b).map eK.hom ≫ (baseChange b).map v := by
  apply (cancel_epi (pullbackComparison f b a hb K).hom).mp
  rw [← Category.assoc (pullbackComparison f b a hb K).hom,
    ← pullbackComparison_naturality]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp, he, Functor.map_comp]

end Langlands.GroupScheme.Descent

namespace Langlands.GroupScheme.RelativeLevi.FiniteParabolicFaceCover

variable {S : Scheme.{u}} [IsAffine S] {G H U : GroupScheme S}
  [IsAffineHom G.X.hom] {p : H ⟶ G}
  (D : FiniteParabolicFaceCover p)
  (r : U ⟶ H) (hG : IsReductive G) (hp : IsRelativeParabolicSubgroup p)
  (hr : IsRelativeUnipotentRadical r)

/-- The actual original global term on any parameter of an original chart. -/
def globalTermParameterIso (d : ℕ) (i : D.Index) {Y : Scheme.{u}}
    (b : Y ⟶ Spec (D.charts i.down).2.ring) (a : Y ⟶ S)
    (hb : b ≫ (D.charts i.down).2.projection = a) :
    (baseChange a).obj (D.globalTerm r hG hp hr d) ≅
      (baseChange b).obj ((D.charts i.down).2.termGroup d) :=
  (Descent.pullbackComparison (D.charts i.down).2.projection b a hb
      (D.globalTerm r hG hp hr d)).symm ≪≫
    (baseChange b).mapIso (D.globalTermChartIso r hG hp hr d i)

/-- The actual original global quotient on any parameter of an original chart. -/
def globalFaceQuotientParameterIso (d : ℕ) (i : D.Index) {Y : Scheme.{u}}
    (b : Y ⟶ Spec (D.charts i.down).2.ring) (a : Y ⟶ S)
    (hb : b ≫ (D.charts i.down).2.projection = a) :
    (baseChange a).obj (D.globalFaceQuotientData r hG hp hr d).group ≅
      (baseChange b).obj ((D.charts i.down).2.layerGroup d) :=
  (Descent.pullbackComparison (D.charts i.down).2.projection b a hb
      (D.globalFaceQuotientData r hG hp hr d).group).symm ≪≫
    (baseChange b).mapIso (D.globalFaceQuotientComponentIso r hG hp hr d i)

/-- Arbitrary parameter recovery retains the exact original quotient projection
square, with no new chart or kernel compatibility premise. -/
lemma globalFaceQuotientParameterIso_projection (d : ℕ) (i : D.Index)
    {Y : Scheme.{u}} (b : Y ⟶ Spec (D.charts i.down).2.ring) (a : Y ⟶ S)
    (hb : b ≫ (D.charts i.down).2.projection = a) :
    (baseChange a).map (D.globalFaceQuotientData r hG hp hr d).projection ≫
        (D.globalFaceQuotientParameterIso r hG hp hr d i b a hb).hom =
      (D.globalTermParameterIso r hG hp hr d i b a hb).hom ≫
        (baseChange b).map ((D.charts i.down).2.layerProjection d) := by
  exact Descent.directParameter_square (D.charts i.down).2.projection b a hb
    (D.globalFaceQuotientData r hG hp hr d).projection
    (D.globalTermChartIso r hG hp hr d i)
    (D.globalFaceQuotientComponentIso r hG hp hr d i)
    ((D.charts i.down).2.layerProjection d)
    (D.globalFaceQuotientComponentIso_projection r hG hp hr d i)

omit [IsAffine S] in
/-- Original ambient inclusions are retained on arbitrary actual chart parameters. -/
lemma globalTermParameterIso_ambient (d : ℕ) (i : D.Index) {Y : Scheme.{u}}
    (b : Y ⟶ Spec (D.charts i.down).2.ring) (a : Y ⟶ S)
    (hb : b ≫ (D.charts i.down).2.projection = a) :
    (D.globalTermParameterIso r hG hp hr d i b a hb).hom ≫
        (baseChange b).map ((D.charts i.down).2.termInclusion d) ≫
        (Descent.pullbackComparison (D.charts i.down).2.projection b a hb G).hom =
      (baseChange a).map (D.globalTermInclusion r hG hp hr d) := by
  have he : (baseChange (D.charts i.down).2.projection).map
      (D.globalTermInclusion r hG hp hr d) ≫ (Iso.refl _).hom =
      (D.globalTermChartIso r hG hp hr d i).hom ≫
        (D.charts i.down).2.termInclusion d := by
    simpa only [Iso.refl_hom, Category.comp_id, globalTermInclusion, globalTerm,
      D.chartCover_projection] using
      (D.globalTermChartIso_hom_comp r hG hp hr d i).symm
  have H := Descent.directParameter_square (D.charts i.down).2.projection b a hb
    (D.globalTermInclusion r hG hp hr d) (D.globalTermChartIso r hG hp hr d i)
    (Iso.refl _) ((D.charts i.down).2.termInclusion d) he
  have H' := congrArg (fun v => v ≫
    (Descent.pullbackComparison (D.charts i.down).2.projection b a hb G).hom) H.symm
  simpa only [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.comp_id,
    Category.assoc, Iso.inv_hom_id, globalTermParameterIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] using H'

omit [IsAffine S] in
/-- The original successive step maps are retained on every actual parameter. -/
lemma globalTermParameterIso_step (d : ℕ) (i : D.Index) {Y : Scheme.{u}}
    (b : Y ⟶ Spec (D.charts i.down).2.ring) (a : Y ⟶ S)
    (hb : b ≫ (D.charts i.down).2.projection = a) :
    (baseChange a).map (D.globalTermStep r hG hp hr d) ≫
        (D.globalTermParameterIso r hG hp hr d i b a hb).hom =
      (D.globalTermParameterIso r hG hp hr (d + 1) i b a hb).hom ≫
        (baseChange b).map ((D.charts i.down).2.termStep d) :=
  Descent.directParameter_square (D.charts i.down).2.projection b a hb
    (D.globalTermStep r hG hp hr d) (D.globalTermChartIso r hG hp hr (d + 1) i)
    (D.globalTermChartIso r hG hp hr d i) ((D.charts i.down).2.termStep d)
    (D.globalTermStep_chart r hG hp hr d i)

end Langlands.GroupScheme.RelativeLevi.FiniteParabolicFaceCover

import Langlands.Geometry.Analytic.GroundFieldChangingCategory

/-! # The underlying space functor for analytic arrows with varying fields -/

noncomputable section

universe u v

namespace Langlands.Analytic

open _root_.CategoryTheory CompleteUltrametricField CompatibleAtlasPresentation
open AffinoidAtlasPresentation.GroundFieldExtension
open AffinoidAtlasPresentation.GroundFieldExtension.CompleteField
open IndexedAffinoidAtlas.GroundFieldExtension

namespace CompleteUltrametricField

variable {K L M : CompleteUltrametricField.{u}}

private abbrev Q (K : CompleteUltrametricField.{u}) :
    K.CompatibleCategory.{u, v} ⥤ K.CompatibleAnalyticCategory.{u, v} :=
  localizationFunctor

/-- The underlying topological space of a localized analytic space over the given field. -/
abbrev underlyingSpace (K : CompleteUltrametricField.{u}) :
    K.CompatibleAnalyticCategory.{u, v} ⥤ TopCat.{max u v} := localizedSpaceFunctor

private def chartProjection (f : K ⟶ L) (A : K.CompatibleCategory.{u, v}) :
    (spaceFunctor.obj ((compatibleExtend f).obj A)) ⟶ spaceFunctor.obj A := by
  letI := f.normedAlgebra
  exact TopCat.ofHom ⟨projection K L A.presentation.atlas,
    continuous_projection K L A.presentation.atlas⟩

private def projectionBeforeLocalization (f : K ⟶ L) :
    compatibleExtend.{u, v} f ⋙ spaceFunctor ⟶ spaceFunctor where
  app A := chartProjection f A
  naturality A B g := by
    let := f.normedAlgebra
    apply TopCat.hom_ext
    exact ContinuousMap.ext fun z => projection_pointMap K L g.toStrongHom g.compatible z

/-- The projection on the underlying spaces of a scalar extension, natural
for all localized analytic arrows. -/
def localizedExtendProjection (f : K ⟶ L) :
    localizedExtend.{u, v} f ⋙ L.underlyingSpace ⟶ K.underlyingSpace := by
  have h : Q.{u, v} K ⋙ (localizedExtend f ⋙ L.underlyingSpace) =
      compatibleExtend f ⋙ spaceFunctor := by
    change (Q K ⋙ localizedExtend f) ⋙ L.underlyingSpace = _
    rw [localizedExtend_factor]
    change compatibleExtend f ⋙ (Q L ⋙ L.underlyingSpace) = _
    rw [localizationFunctor_localizedSpaceFunctor (K := L.carrier)]
  exact Localization.Construction.natTransExtension
    (eqToHom h ≫ projectionBeforeLocalization f ≫
      eqToHom (localizationFunctor_localizedSpaceFunctor (K := K.carrier)).symm)

theorem localizedExtendProjection_app (f : K ⟶ L) (A : K.CompatibleCategory.{u, v}) :
    (localizedExtendProjection f).app ((Q K).obj A) = chartProjection f A := rfl

theorem localizedExtendProjection_id (A : K.CompatibleAnalyticCategory.{u, v}) :
    (localizedExtendProjection (𝟙 K)).app A = K.underlyingSpace.map ((localizedExtendId K).hom.app A) := by
  obtain ⟨B, rfl⟩ := (localizedObjectEquiv (K := K.carrier)).surjective A
  change (localizedExtendProjection (𝟙 K)).app ((Q K).obj B) =
    K.underlyingSpace.map ((localizedExtendId K).hom.app ((Q K).obj B))
  rw [localizedExtendProjection_app]
  exact ((congrArg (fun p => K.underlyingSpace.map p) (localizedExtendId_hom_app B)).trans
    (localizedSpaceFunctor_map ((compatibleExtendId K).app B))).symm

/-- The continuous projection for direct scalar extension is the composite
of the successive projections through the analytic tower comparison. -/
theorem localizedExtendProjection_comp (f : K ⟶ L) (g : L ⟶ M)
    (A : K.CompatibleAnalyticCategory.{u, v}) :
    M.underlyingSpace.map ((localizedExtendComp f g).hom.app A) ≫
      (localizedExtendProjection g).app ((localizedExtend f).obj A) ≫
      (localizedExtendProjection f).app A =
      (localizedExtendProjection (f ≫ g)).app A := by
  obtain ⟨B, rfl⟩ := (localizedObjectEquiv (K := K.carrier)).surjective A
  have ht := (congrArg (fun p => M.underlyingSpace.map p)
    (localizedExtendComp_hom_app f g B)).trans
      (localizedSpaceFunctor_map ((compatibleExtendComp f g).hom.app B))
  have hg := localizedExtendProjection_app g ((compatibleExtend f).obj B)
  have hf := localizedExtendProjection_app f B
  have hd := localizedExtendProjection_app (f ≫ g) B
  let := f.normedAlgebra
  let := g.normedAlgebra
  let := (f ≫ g).normedAlgebra
  let : IsScalarTower K L M := f.isScalarTower_comp g
  refine (congrArg₂ (fun p q => p ≫ q) ht (congrArg₂ (fun p q => p ≫ q) hg hf)).trans ?_
  refine Eq.trans ?_ hd.symm
  apply TopCat.hom_ext
  exact ContinuousMap.ext fun z => towerHomeomorph_projection K L M B.presentation.atlas z

end CompleteUltrametricField

namespace SpaceOverField

/-- The continuous map represented by an analytic map into a scalar extension. -/
def underlyingAnalyticMap {K L : CompleteUltrametricField.{u}}
    {X : K.CompatibleAnalyticCategory.{u, v}} {Y : L.CompatibleAnalyticCategory.{u, v}}
    (e : K ⟶ L) (f : Y ⟶ (localizedExtend e).obj X) :
    L.underlyingSpace.obj Y ⟶ K.underlyingSpace.obj X :=
  L.underlyingSpace.map f ≫ (localizedExtendProjection e).app X

/-- Pass from a field-changing analytic arrow to the continuous map given by
its analytic map followed by projection from the scalar-extended target. -/
def underlyingMap {Y X : SpaceOverField.{u, v}} (f : Y ⟶ X) :
    Y.field.underlyingSpace.obj Y.space ⟶ X.field.underlyingSpace.obj X.space :=
  underlyingAnalyticMap (fieldMap f) (analyticMap f)

theorem underlyingMap_homMk {K L : CompleteUltrametricField.{u}}
    {X : K.CompatibleAnalyticCategory.{u, v}} {Y : L.CompatibleAnalyticCategory.{u, v}}
    (e : K ⟶ L) (f : Y ⟶ (localizedExtend e).obj X) :
    underlyingMap (homMk (Y := withField L Y) (X := withField K X) e f) =
      underlyingAnalyticMap e f :=
  rfl

/-- The continuous maps underlying analytic arrows respect identity and composition. -/
def underlyingSpaceFunctor : SpaceOverField.{u, v} ⥤ TopCat.{max u v} where
  obj X := X.field.underlyingSpace.obj X.space
  map f := underlyingMap f
  map_id X := by
    let s := X.field.underlyingSpace
    let e := (localizedExtendId X.field).app X.space
    change s.map e.inv ≫ (localizedExtendProjection (𝟙 X.field)).app X.space = _
    calc
      _ = s.map e.inv ≫ s.map e.hom :=
        congrArg (fun p => s.map e.inv ≫ p) (localizedExtendProjection_id X.space)
      _ = s.map (e.inv ≫ e.hom) := (s.map_comp e.inv e.hom).symm
      _ = _ := by rw [e.inv_hom_id, s.map_id]; rfl
  map_comp {Z Y X} f g := by
    let e := fieldMap f
    let d := fieldMap g
    let α := analyticMap f
    let β := analyticMap g
    let s := Z.field.underlyingSpace
    let t := Y.field.underlyingSpace
    let i := (localizedExtendComp d e).app X.space
    let p := localizedExtendProjection e
    let q := localizedExtendProjection d
    change s.map (α ≫ (localizedExtend e).map β ≫ i.inv) ≫
        (localizedExtendProjection (d ≫ e)).app X.space =
      (s.map α ≫ p.app Y.space) ≫ t.map β ≫ q.app X.space
    have ht := localizedExtendProjection_comp d e X.space
    change s.map i.hom ≫ p.app ((localizedExtend d).obj X.space) ≫ q.app X.space = _ at ht
    have hn := p.naturality β
    change s.map ((localizedExtend e).map β) ≫ p.app ((localizedExtend d).obj X.space) =
      p.app Y.space ≫ t.map β at hn
    have hi : s.map i.inv ≫ (localizedExtendProjection (d ≫ e)).app X.space =
        p.app ((localizedExtend d).obj X.space) ≫ q.app X.space :=
      (congrArg (fun r => s.map i.inv ≫ r) ht.symm).trans
        ((s.mapIso i).inv_hom_id_assoc _)
    rw [s.map_comp α _, s.map_comp ((localizedExtend e).map β) i.inv]
    simp only [Category.assoc]
    rw [hi, ← Category.assoc (s.map ((localizedExtend e).map β)), hn, Category.assoc]

end SpaceOverField

end Langlands.Analytic

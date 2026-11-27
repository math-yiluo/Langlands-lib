import Langlands.Geometry.Analytic.GroundFieldChangingSpaceFunctor
import Langlands.Geometry.Analytic.GroundFieldExtensionAtlasAction
import Langlands.Geometry.Analytic.GroundFieldExtensionSemilinearAction

/-! # The underlying action of analytic coefficient automorphisms -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SpaceOverField

open _root_.CategoryTheory CompleteUltrametricField CompatibleAtlasPresentation
open PresentedAffinoidAlgebra.GroundFieldExtension IndexedAffinoidAtlas.GroundFieldExtension

variable {K L : CompleteUltrametricField.{u}}
variable (e : K ⟶ L) (X : K.CompatibleAnalyticCategory.{u, v})

section TowerPullback

variable {M : CompleteUltrametricField.{u}}
variable (f : K ⟶ L) (g : L ⟶ M) (h : K ⟶ M) (hh : f ≫ g = h)

include hh in
/-- A given equality of field embeddings supplies the scalar tower on their fields. -/
theorem scalarTower_of_comp_eq :
    letI := f.normedAlgebra
    letI := g.normedAlgebra
    letI := h.normedAlgebra
    IsScalarTower K L M := by
  subst h
  exact f.isScalarTower_comp g

/-- Pullback along the projection to the first extension, expressed on the direct extension. -/
def towerProjectionPullback (A : PresentedAffinoidAlgebra K) :
    letI := f.normedAlgebra
    letI := h.normedAlgebra
    BoundedAlgHom K (algebra K L A) (algebra K M A) := by
  letI := f.normedAlgebra
  letI := g.normedAlgebra
  letI := h.normedAlgebra
  letI := scalarTower_of_comp_eq f g h hh
  let i := iota L M (algebra K L A)
  let t := towerEquiv K L M A
  let p := t.toBoundedAlgHom.toBoundedRingHom.comp i.toBoundedRingHom
  refine ⟨⟨p.toRingHom, fun c => ?_⟩, p.bounded⟩
  have hc := (iota K L A).toAlgHom.commutes c
  have hc' := (iota K M A).toAlgHom.commutes c
  change t (i (algebraMap K (algebra K L A) c)) = _
  rw [← hc, ← hc']
  exact towerEquiv_iota K L M A _

private theorem towerProjectionPullback_iota (A : PresentedAffinoidAlgebra K) (a : A) :
    letI := f.normedAlgebra
    letI := h.normedAlgebra
    towerProjectionPullback f g h hh A (iota K L A a) = iota K M A a := by
  let := f.normedAlgebra
  let := g.normedAlgebra
  let := h.normedAlgebra
  let : IsScalarTower K L M := scalarTower_of_comp_eq f g h hh
  exact towerEquiv_iota K L M A a

private theorem towerProjectionPullback_scalar (A : PresentedAffinoidAlgebra K) (c : L) :
    letI := f.normedAlgebra
    letI := h.normedAlgebra
    towerProjectionPullback f g h hh A (scalarMap K L A c) = scalarMap K M A (g c) := by
  let := f.normedAlgebra
  let := g.normedAlgebra
  let := h.normedAlgebra
  let : IsScalarTower K L M := scalarTower_of_comp_eq f g h hh
  let i := iota L M (algebra K L A)
  let t := towerEquiv K L M A
  let S := algebra L M (algebra K L A)
  have hs : i (algebraMap L (algebra K L A) c) = algebraMap M S (g c) := i.toAlgHom.commutes c
  change t (i (algebraMap L (algebra K L A) c)) = algebraMap M (algebra K M A) (g c)
  exact (congrArg (fun y => t y) hs).trans (t.toAlgEquiv.commutes (g c))

private def towerProjectionMap (X : K.CompatibleAnalyticCategory.{u, v}) :
    M.underlyingSpace.obj ((localizedExtend h).obj X) ⟶
      L.underlyingSpace.obj ((localizedExtend f).obj X) :=
    underlyingAnalyticMap g
      (eqToHom (congrArg (fun d => (localizedExtend.{u, v} d).obj X) hh.symm) ≫
        (localizedExtendComp f g).hom.app X)

private theorem towerProjection_on_chart (A : K.CompatibleCategory.{u, v}) (i : A.presentation.atlas.Index) :
    letI := f.normedAlgebra
    letI := h.normedAlgebra
    ∀ s : BanachSpectrum (chartAlgebra K M A.presentation.atlas i),
    towerProjectionMap f g h hh (localizationFunctor.obj A) ((chartSystem K M A.presentation.atlas).chart i s) =
      (chartSystem K L A.presentation.atlas).chart i
        (BanachSpectrum.comap
          (towerProjectionPullback f g h hh (A.presentation.atlas.algebra i)).toBoundedRingHom s) := by
  subst h
  let := f.normedAlgebra
  let := g.normedAlgebra
  let := (f ≫ g).normedAlgebra
  let : IsScalarTower K L M := f.isScalarTower_comp g
  let a := A.presentation.atlas
  let X := (localizationFunctor (K := K.carrier)).obj A
  dsimp only
  intro s
  have hcomp := localizedExtendComp_hom_app f g A
  have hU := (congrArg (fun p => M.underlyingSpace.map p) hcomp).trans
    (localizedSpaceFunctor_map ((AffinoidAtlasPresentation.GroundFieldExtension.CompleteField.compatibleExtendComp f g).hom.app A))
  change M.underlyingSpace.map ((localizedExtendComp f g).hom.app X) =
    TopCat.ofHom ⟨towerHomeomorph K L M a, (towerHomeomorph K L M a).continuous⟩ at hU
  change (localizedExtendProjection g).app ((localizedExtend f).obj X)
        (M.underlyingSpace.map (𝟙 _ ≫ (localizedExtendComp f g).hom.app X)
          ((chartSystem K M a).chart i s)) = _
  rw [Category.id_comp, hU]
  change projection L M (atlas K L a) (towerHomeomorph K L M a ((chartSystem K M a).chart i s)) = _
  rw [towerHomeomorph_chart]
  refine (projection_chart L M (atlas K L a) i (towerChartHomeomorph K L M a i s)).trans ?_
  apply congrArg ((chartSystem K L a).chart i)
  apply BanachSpectrum.ext
  intro x
  rfl

end TowerPullback

/-- When the second embedding fixes the base, the tower pullback is the
coefficient operator on the two completed tensor legs. -/
theorem towerProjectionPullback_eq_coefficientHom (σ : CoefficientAutomorphisms e)
    (A : PresentedAffinoidAlgebra K) :
    letI := e.normedAlgebra
    towerProjectionPullback e (coefficientFieldMap σ) e (comp_coefficientFieldMap σ) A =
      coefficientHom K L A σ := by
  let := e.normedAlgebra
  apply hom_ext_over_base K L A
  · intro a
    exact (towerProjectionPullback_iota e _ e _ A a).trans (coefficientHom_iota K L A σ a).symm
  · intro c
    exact (towerProjectionPullback_scalar e _ e _ A c).trans (coefficientHom_scalar K L A σ c).symm

private theorem underlyingMap_coefficientLift_eq_towerProjectionMap (σ : CoefficientAutomorphisms e) :
    underlyingMap (coefficientLift e X σ) =
      towerProjectionMap e (coefficientFieldMap σ⁻¹) e (comp_coefficientFieldMap σ⁻¹) X := by
  let Y := scalarExtendedSpace e X
  let d := coefficientFieldMap σ⁻¹
  exact (congrArg (underlyingMap (Y := Y) (X := Y)) (coefficientLift_eq_homMk e X σ)).trans
    (underlyingMap_homMk d (coefficientLiftMap e X σ))

private abbrev extendedTopCat (A : K.CompatibleCategory.{u, v}) : TopCat.{max u v} :=
  L.underlyingSpace.obj ((localizedExtend.{u, v} e).obj (localizationFunctor.obj A))

private def agreesOnChart (A : K.CompatibleCategory.{u, v}) (σ : CoefficientAutomorphisms e)
    (i : A.presentation.atlas.Index) (f : extendedTopCat e A ⟶ extendedTopCat e A) : Prop :=
    letI := e.normedAlgebra
    let a := A.presentation.atlas
    ∀ s : BanachSpectrum (chartAlgebra K L a i),
      f ((chartSystem K L a).chart i s) = coefficientPointMap K L a σ ((chartSystem K L a).chart i s)

private theorem coefficientProjection_chart (A : K.CompatibleCategory.{u, v})
    (σ : CoefficientAutomorphisms e) (i : A.presentation.atlas.Index) :
    agreesOnChart e A σ i
      (towerProjectionMap.{u, v} e (coefficientFieldMap σ⁻¹) e (comp_coefficientFieldMap σ⁻¹)
        (localizationFunctor.obj A)) := by
  let := e.normedAlgebra
  dsimp only [agreesOnChart]
  intro s
  let a := A.presentation.atlas
  have ht := @towerProjection_on_chart.{u, v} K L L e (coefficientFieldMap σ⁻¹) e
    (comp_coefficientFieldMap σ⁻¹) A i s
  rw [ht]
  calc
    _ = (chartSystem K L a).chart i (coefficientChartAction K L a σ i s) :=
      congrArg (fun φ : BoundedAlgHom K (chartAlgebra K L a i) (chartAlgebra K L a i) =>
        (chartSystem K L a).chart i (BanachSpectrum.comap φ.toBoundedRingHom s))
        (towerProjectionPullback_eq_coefficientHom e σ⁻¹ (a.algebra i))
    _ = coefficientPointMap K L a σ ((chartSystem K L a).chart i s) :=
      (coefficientPointMap_chart K L a σ i s).symm

private theorem underlyingMap_coefficientLift_chart (A : K.CompatibleCategory.{u, v})
    (σ : CoefficientAutomorphisms e) (i : A.presentation.atlas.Index) :
    agreesOnChart e A σ i (underlyingMap (coefficientLift e (localizationFunctor.obj A) σ)) :=
  (underlyingMap_coefficientLift_eq_towerProjectionMap.{u, v} e (localizationFunctor.obj A) σ).symm ▸
    coefficientProjection_chart.{u, v} e A σ i

/-- The continuous map of the analytic lift is the glued action on chart spectra. -/
theorem underlyingMap_coefficientLift_apply (A : K.CompatibleCategory.{u, v})
    (σ : CoefficientAutomorphisms e) :
    letI := e.normedAlgebra
    let a := A.presentation.atlas
    ∀ x : (chartSystem K L a).Space,
      underlyingMap (coefficientLift e (localizationFunctor.obj A) σ) x =
        coefficientPointMap K L a σ x := by
  let := e.normedAlgebra
  dsimp only
  intro x
  obtain ⟨i, s, rfl⟩ := (chartSystem K L A.presentation.atlas).exists_chart x
  have hi := underlyingMap_coefficientLift_chart.{u, v} e A σ i
  dsimp only [agreesOnChart] at hi
  exact hi s

/-- Norm continuity of the scalar orbits gives joint continuity of the
underlying point action of the actual analytic coefficient automorphisms. -/
theorem continuous_underlyingCoefficientAction {G : Type z} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (ρ : G →* CoefficientAutomorphisms e)
    (hρ : ∀ c : L, Continuous (fun g : G => (ρ g).val c)) :
    Continuous (fun x : G × underlyingSpaceFunctor.obj (scalarExtendedSpace e X) =>
      underlyingMap (coefficientLift e X (ρ x.1)) x.2) := by
  obtain ⟨A, rfl⟩ := (localizedObjectEquiv (K := K.carrier)).surjective X
  let := e.normedAlgebra
  change Continuous (fun x : G × (chartSystem K L A.presentation.atlas).Space =>
    underlyingMap (coefficientLift e (localizationFunctor.obj A) (ρ x.1)) x.2)
  exact (continuous_coefficientPointMap K L A.presentation.atlas ρ hρ).congr
    (fun x => (underlyingMap_coefficientLift_apply e A (ρ x.1) x.2).symm)

end Langlands.Analytic.SpaceOverField

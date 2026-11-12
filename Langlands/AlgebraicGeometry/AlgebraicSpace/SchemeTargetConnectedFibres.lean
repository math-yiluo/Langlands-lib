import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeTargetRebase
import Langlands.AlgebraicGeometry.AlgebraicSpace.ConnectedStructuralFibres
import Langlands.AlgebraicGeometry.AlgebraicSpace.ConnectedFibreTargetAtlas

/-! # Connected fibres after rebasing to a represented target -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeTargetRebase

variable {S : Scheme.{u}} {V : Over S} {X : AlgebraicSpace S}
    (f : X ⟶ (schemeToSpace S).obj V)

/-- The rebase square uses the actual structural morphism over the new base. -/
theorem structuralSquare :
    IsPullback (hom (FibreProduct.fst (baseChangeMap V.hom f) (sectionMorphism V)))
      (hom (structuralMorphism (space f))) (hom (baseChangeMap V.hom f))
      (sectionMap V) := by
  have hp : hom (structuralMorphism (space f)) =
      hom (FibreProduct.snd (baseChangeMap V.hom f) (sectionMorphism V)) :=
    (basePresheafIsTerminal V.left).hom_ext _ _
  rw [hp]
  exact FibreProduct.isPullback_presheaf _ _

/-- The structural fibre over the new base has the original fibre's point topology. -/
def fibrePointsHomeomorph {U : Over V.left}
    (y : (schemeYoneda V.left).obj U ⟶
      (schemeYoneda V.left).obj (Over.mk (𝟙 V.left))) :
    @Homeomorph (Points (Limits.pullback (hom (structuralMorphism (space f))) y))
      (Points (Limits.pullback (hom f)
        (originalBaseChart V.hom (y ≫ sectionMap V))))
      (pointTopology _) (pointTopology _) := by
  let := pointTopology (Limits.pullback (hom (structuralMorphism (space f))) y)
  let := pointTopology
    (Limits.pullback (hom (baseChangeMap V.hom f)) (y ≫ sectionMap V))
  let := pointTopology
    (Limits.pullback (hom f) (originalBaseChart V.hom (y ≫ sectionMap V)))
  exact (Points.isoHomeomorph (iteratedFibrePullbackIso (structuralSquare f) y)).trans
    (fibreRestrictionPointsHomeomorph V.hom f (y ≫ sectionMap V))

/-- The canonical map from a test scheme to the new relative base. -/
def baseTest {T : Scheme.{u}} (t : T ⟶ V.left) :
    Over.mk t ⟶ Over.mk (𝟙 V.left) :=
  Over.homMk t (by simp)

/-- The same test over the original scheme base. -/
def originalTest {T : Scheme.{u}} (t : T ⟶ V.left) :
    (Over.map V.hom).obj (Over.mk t) ⟶ V :=
  Over.homMk t rfl

/-- The section of the restricted represented target recovers the actual test map. -/
theorem originalBaseChart_baseTest {T : Scheme.{u}} (t : T ⟶ V.left) :
    originalBaseChart V.hom ((schemeYoneda V.left).map (baseTest t) ≫ sectionMap V) =
      (schemeYoneda S).map (originalTest t) := by
  apply forgetBaseYoneda_comp_injective V.hom (Over.mk t)
  rw [originalBaseChart_restrict]
  have ht : (Over.map V.hom).map (baseTest t) ≫ (originalBaseIso V).hom =
      originalTest t := by
    ext
    simp [baseTest, originalBaseIso, originalTest]
  rw [← ht, Functor.map_comp, Functor.map_comp, ← Category.assoc,
    ← forgetBaseYoneda_naturality]
  rfl

/-- An original test and its recovered new-base test are isomorphic over the
original base, with the identity on their underlying scheme. -/
def testBaseIso {U : Over S} (t : U ⟶ V) :
    (Over.map V.hom).obj (Over.mk t.left) ≅ U :=
  Over.isoMk (Iso.refl _) (by
    change (𝟙 U.left) ≫ U.hom = t.left ≫ V.hom
    rw [Category.id_comp]
    exact (Over.w t).symm)

theorem testBaseIso_hom_comp {U : Over S} (t : U ⟶ V) :
    (testBaseIso t).hom ≫ t = originalTest t.left := by
  ext
  exact Category.id_comp _

/-- The original fibre does not change when the represented test is recovered
from its map to the represented target. -/
def originalTestFibreIso {U : Over S} (t : U ⟶ V) :
    Limits.pullback (hom f) ((schemeYoneda S).map (originalTest t.left)) ≅
      Limits.pullback (hom f) ((schemeYoneda S).map t) := by
  let f' : X.presheaf ⟶ (schemeYoneda S).obj V := hom f
  change Limits.pullback f' ((schemeYoneda S).map (originalTest t.left)) ≅
    Limits.pullback f' ((schemeYoneda S).map t)
  exact asIso (Limits.pullback.map _ _ _ _ (𝟙 X.presheaf)
    ((schemeYoneda S).map (testBaseIso t).hom)
    (𝟙 ((schemeYoneda S).obj V)) (by simp) (by
      rw [Category.comp_id, ← Functor.map_comp, testBaseIso_hom_comp]))

/-- Geometrically connected nonempty fibres agree before and after the actual
rebase to the represented target scheme. -/
theorem hasGeometricallyConnectedFibres_iff :
    HasGeometricallyConnectedFibres f ↔
      HasGeometricallyConnectedFibres (structuralMorphism (space f)) := by
  constructor
  · intro hf K _ s y
    let := pointTopology (Limits.pullback (hom (structuralMorphism (space f))) y)
    let := pointTopology
      (Limits.pullback (hom f) (originalBaseChart V.hom (y ≫ sectionMap V)))
    exact (fibrePointsHomeomorph f y).connectedSpace_iff.mpr
      (hf K (s ≫ V.hom) (originalBaseChart V.hom (y ≫ sectionMap V)))
  · intro hf K _ s y
    obtain ⟨t, rfl⟩ := (schemeYoneda S).map_surjective y
    let y' := (schemeYoneda V.left).map (baseTest t.left)
    let e := fibrePointsHomeomorph f y'
    have he : originalBaseChart V.hom (y' ≫ sectionMap V) =
        (schemeYoneda S).map (originalTest t.left) :=
      originalBaseChart_baseTest t.left
    let e₀ := Limits.pullback.congrHom (f₁ := hom f) rfl he
    let := pointTopology (Limits.pullback (hom (structuralMorphism (space f))) y')
    let := pointTopology
      (Limits.pullback (hom f) (originalBaseChart V.hom (y' ≫ sectionMap V)))
    let := pointTopology
      (Limits.pullback (hom f) ((schemeYoneda S).map (originalTest t.left)))
    let := pointTopology (Limits.pullback (hom f) ((schemeYoneda S).map t))
    exact (Points.isoHomeomorph (originalTestFibreIso f t)).connectedSpace_iff.mp
      ((Points.isoHomeomorph e₀).connectedSpace_iff.mp
        (e.connectedSpace_iff.mp (hf K t.left y')))

end Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeTargetRebase

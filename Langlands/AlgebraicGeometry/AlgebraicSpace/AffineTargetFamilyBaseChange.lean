import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineTargetFamily
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpacePointsIsoTransport
import Langlands.AlgebraicGeometry.AlgebraicSpace.TopologicalMorphismBaseChange

/-! # Actual field fibres of target families after scheme base change -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S T : Scheme.{u}}

/-- Restriction of the represented base remains terminal. -/
def restrictedBaseIsTerminal (g : T ⟶ S) :
    IsTerminal ((restrictPresheaf g).obj ((schemeYoneda S).obj (Over.mk (𝟙 S)))) :=
  (basePresheafIsTerminal S).isTerminalObj (restrictPresheaf g) _

/-- The represented base over the new scheme is the restricted original base. -/
def restrictedBaseIso (g : T ⟶ S) :
    (schemeToSpace T).obj (Over.mk (𝟙 T)) ≅
      baseChange g ((schemeToSpace S).obj (Over.mk (𝟙 S))) where
  hom := homMk ((basePresheafIsTerminal T).uniqueUpToIso (restrictedBaseIsTerminal g)).hom
  inv := homMk ((basePresheafIsTerminal T).uniqueUpToIso (restrictedBaseIsTerminal g)).inv
  hom_inv_id := (homEquiv _ _).injective
    ((basePresheafIsTerminal T).uniqueUpToIso (restrictedBaseIsTerminal g)).hom_inv_id
  inv_hom_id := (homEquiv _ _).injective
    ((basePresheafIsTerminal T).uniqueUpToIso (restrictedBaseIsTerminal g)).inv_hom_id

/-- Structural fibres after restriction have the original structural fibre topology. -/
def structuralBaseChangeFibreHomeomorph (g : T ⟶ S) (X : AlgebraicSpace S)
    {Q : Scheme.{u}} (t : Q ⟶ T) :
    @Homeomorph
      (Points (Limits.pullback (hom (structuralMorphism (baseChange g X)))
        ((schemeYoneda T).map (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 T)) t))))
      (Points (Limits.pullback (hom (structuralMorphism X))
        ((schemeYoneda S).map (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 S)) (t ≫ g)))))
      (pointTopology _) (pointTopology _) := by
  let e := (forgetToPresheaf T).mapIso (restrictedBaseIso g)
  have w : (𝟙 (baseChange g X).presheaf) ≫ hom (baseChangeMap g (structuralMorphism X)) =
      hom (structuralMorphism (baseChange g X)) ≫ e.hom :=
    (restrictedBaseIsTerminal g).hom_ext _ _
  let y := (schemeYoneda T).map (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 T)) t)
  let e₁ := fibrePullbackIsoOfArrowIso
    (hom (structuralMorphism (baseChange g X)))
    (hom (baseChangeMap g (structuralMorphism X))) (Iso.refl _) e w (y ≫ e.hom)
  have he : (y ≫ e.hom) ≫ e.inv = y := by simp
  let e₂ := Limits.pullback.congrHom
    (f₁ := hom (structuralMorphism (baseChange g X))) rfl he
  have hy : originalBaseChart g (y ≫ e.hom) =
      (schemeYoneda S).map (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 S)) (t ≫ g)) :=
    (basePresheafIsTerminal S).hom_ext _ _
  let e₃ := Limits.pullback.congrHom (f₁ := hom (structuralMorphism X)) rfl hy
  let := pointTopology (Limits.pullback (hom (structuralMorphism (baseChange g X))) y)
  let := pointTopology (Limits.pullback (hom (structuralMorphism (baseChange g X)))
    ((y ≫ e.hom) ≫ e.inv))
  let := pointTopology (Limits.pullback (hom (baseChangeMap g (structuralMorphism X)))
    (y ≫ e.hom))
  let := pointTopology (Limits.pullback (hom (structuralMorphism X))
    (originalBaseChart g (y ≫ e.hom)))
  let := pointTopology (Limits.pullback (hom (structuralMorphism X))
    ((schemeYoneda S).map (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 S)) (t ≫ g))))
  exact (Points.isoHomeomorph e₂.symm).trans ((Points.isoHomeomorph e₁).trans
    ((fibreRestrictionPointsHomeomorph g (structuralMorphism X) (y ≫ e.hom)).trans
      (Points.isoHomeomorph e₃)))

namespace AffineTargetFamily

variable {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V : Over S} (b : (schemeYoneda S).obj V ⟶ Y.presheaf)

/-- A field or scheme test of the family has the original morphism's actual fibre. -/
def testFibreHomeomorph {U : Over S} (r : U ⟶ V) :
    @Homeomorph
      (Points (Limits.pullback (hom (structuralMorphism (space f b)))
        ((schemeYoneda V.left).map (SchemeTargetRebase.baseTest r.left))))
      (Points (Limits.pullback (hom f) ((schemeYoneda S).map r ≫ b)))
      (pointTopology _) (pointTopology _) := by
  let p := FibreProduct.snd f (homMk b : (schemeToSpace S).obj V ⟶ Y)
  let y := (schemeYoneda V.left).map (SchemeTargetRebase.baseTest r.left)
  have hy := SchemeTargetRebase.originalBaseChart_baseTest r.left
  let e₀ := Limits.pullback.congrHom (f₁ := hom p) rfl hy
  let e₁ := SchemeTargetRebase.originalTestFibreIso p r
  let e₂ := iteratedFibrePullbackIso
    (FibreProduct.isPullback_presheaf f (homMk b : (schemeToSpace S).obj V ⟶ Y))
    ((schemeYoneda S).map r)
  let := pointTopology (Limits.pullback (hom (structuralMorphism (space f b))) y)
  let := pointTopology (Limits.pullback (hom p)
    (originalBaseChart V.hom (y ≫ SchemeTargetRebase.sectionMap V)))
  let := pointTopology (Limits.pullback (hom p)
    ((schemeYoneda S).map (SchemeTargetRebase.originalTest r.left)))
  let := pointTopology (Limits.pullback (hom p) ((schemeYoneda S).map r))
  let := pointTopology (Limits.pullback (hom f) ((schemeYoneda S).map r ≫ b))
  let := pointTopology (Limits.pullback (hom (structuralMorphism (SchemeTargetRebase.space p))) y)
  exact (SchemeTargetRebase.fibrePointsHomeomorph p y).trans
    ((Points.isoHomeomorph e₀).trans
      ((Points.isoHomeomorph e₁).trans (Points.isoHomeomorph e₂)))

/-- A represented test of the restricted chart recovers the adjoint original test. -/
theorem originalBaseChart_restrictAtlas (g : T ⟶ S) {U : Over T}
    (r : U ⟶ (Over.pullback g).obj V) :
    originalBaseChart g ((schemeYoneda T).map r ≫ restrictAtlas g b) =
      (schemeYoneda S).map (((Over.mapPullbackAdj g).homEquiv U V).symm r) ≫ b := by
  apply uliftYonedaEquiv.{u + 1}.injective
  simp only [originalBaseChart, Equiv.apply_symm_apply, uliftYonedaEquiv_apply,
    NatTrans.comp_app, types_comp_apply]
  change b.app _ (ULift.up (((Over.mapPullbackAdj g).homEquiv U V).symm (𝟙 U ≫ r))) =
    b.app _ (ULift.up (𝟙 ((Over.map g).obj U) ≫
      ((Over.mapPullbackAdj g).homEquiv U V).symm r))
  simp only [Category.id_comp]

end AffineTargetFamily

end Langlands.AlgebraicGeometry.AlgebraicSpace

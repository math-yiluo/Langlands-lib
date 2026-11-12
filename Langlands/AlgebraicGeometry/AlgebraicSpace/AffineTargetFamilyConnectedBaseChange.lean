import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineTargetFamilyBaseChange

/-! # Connected fibres of a target family after arbitrary scheme base change -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.AffineTargetFamily

variable {S T : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V : Over S} (b : (schemeYoneda S).obj V ⟶ Y.presheaf) (g : T ⟶ S)

/-- The changed target-family fibre is the actual changed morphism fibre over
its represented target-chart test. -/
def baseChangeTestFibreHomeomorph {U : Over T} (r : U ⟶ (Over.pullback g).obj V) :
    @Homeomorph
      (Points (Limits.pullback
        (hom (structuralMorphism (baseChange (pullback.fst V.hom g) (space f b))))
        ((schemeYoneda (Limits.pullback V.hom g)).map
          (SchemeTargetRebase.baseTest
            (V := Over.mk (𝟙 (Limits.pullback V.hom g))) r.left))))
      (Points (Limits.pullback (hom (baseChangeMap g f))
        ((schemeYoneda T).map r ≫ restrictAtlas g b)))
      (pointTopology _) (pointTopology _) := by
  let rS := ((Over.mapPullbackAdj g).homEquiv U V).symm r
  let y := (schemeYoneda T).map r ≫ restrictAtlas g b
  let e₀ := structuralBaseChangeFibreHomeomorph (pullback.fst V.hom g) (space f b) r.left
  let e₁ := testFibreHomeomorph f b rS
  let e₂ := Limits.pullback.congrHom (f₁ := hom f) rfl
    (originalBaseChart_restrictAtlas b g r)
  let e₃ := fibreRestrictionPointsHomeomorph g f y
  let := pointTopology (Limits.pullback
    (hom (structuralMorphism (baseChange (pullback.fst V.hom g) (space f b))))
    ((schemeYoneda (Limits.pullback V.hom g)).map
      (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 (Limits.pullback V.hom g))) r.left)))
  let := pointTopology (Limits.pullback (hom (structuralMorphism (space f b)))
    ((schemeYoneda V.left).map
      (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 V.left))
        (r.left ≫ pullback.fst V.hom g))))
  let := pointTopology (Limits.pullback (hom f) ((schemeYoneda S).map rS ≫ b))
  let := pointTopology (Limits.pullback (hom f) (originalBaseChart g y))
  let := pointTopology (Limits.pullback (hom (baseChangeMap g f)) y)
  let := pointTopology (Limits.pullback (hom (structuralMorphism (space f b)))
    ((schemeYoneda V.left).map (SchemeTargetRebase.baseTest rS.left)))
  exact e₀.trans (e₁.trans ((Points.isoHomeomorph e₂).symm.trans e₃.symm))

/-- The actual target family tests connected nonempty geometric fibres after any
scheme base change. -/
theorem hasGeometricallyConnectedFibres_baseChange_iff
    (hb : IsEtale b) (hs : IsSurjective b) :
    HasGeometricallyConnectedFibres (baseChangeMap g f) ↔
      HasGeometricallyConnectedFibres
        (structuralMorphism (baseChange (pullback.fst V.hom g) (space f b))) := by
  let VT := (Over.pullback g).obj V
  constructor
  · intro hf K _ s y
    have hy : y = (schemeYoneda VT.left).map
        (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 VT.left)) s) :=
      (basePresheafIsTerminal VT.left).hom_ext _ _
    rw [hy]
    let r : Over.mk (s ≫ VT.hom) ⟶ VT := Over.homMk s rfl
    let z := (schemeYoneda T).map r ≫ restrictAtlas g b
    let := pointTopology (Limits.pullback (hom (baseChangeMap g f)) z)
    let := pointTopology (Limits.pullback
      (hom (structuralMorphism (baseChange (pullback.fst V.hom g) (space f b))))
      ((schemeYoneda VT.left).map
        (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 VT.left)) s)))
    let := pointTopology (Limits.pullback
      (hom (structuralMorphism (baseChange (pullback.fst V.hom g) (space f b))))
      ((schemeYoneda VT.left).map
        (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 VT.left)) r.left)))
    exact (baseChangeTestFibreHomeomorph f b g r).connectedSpace_iff.mpr
      (hf K (s ≫ VT.hom) z)
  · intro hf
    apply (hasGeometricallyConnectedFibres_iff_algClosed (baseChangeMap g f)).mpr
    intro K _ _ s y
    obtain ⟨r, hr⟩ := exists_lift_atlas_algClosed (restrictAtlas g b)
      (relative_restrictAtlas _ hb) (relative_restrictAtlas _ hs) K s y
    let z := (schemeYoneda T).map r ≫ restrictAtlas g b
    let := pointTopology (Limits.pullback (hom (baseChangeMap g f)) z)
    let := pointTopology (Limits.pullback
      (hom (structuralMorphism (baseChange (pullback.fst V.hom g) (space f b))))
      ((schemeYoneda VT.left).map
        (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 VT.left)) r.left)))
    have hz := (baseChangeTestFibreHomeomorph f b g r).connectedSpace_iff.mp
      (hf K r.left ((schemeYoneda VT.left).map
        (SchemeTargetRebase.baseTest (V := Over.mk (𝟙 VT.left)) r.left)))
    let e := Limits.pullback.congrHom (f₁ := hom (baseChangeMap g f)) rfl hr
    let := pointTopology (Limits.pullback (hom (baseChangeMap g f)) y)
    exact (Points.isoHomeomorph e).connectedSpace_iff.mp hz

end Langlands.AlgebraicGeometry.AlgebraicSpace.AffineTargetFamily

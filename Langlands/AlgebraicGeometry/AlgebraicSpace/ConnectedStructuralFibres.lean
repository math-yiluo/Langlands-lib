import Langlands.AlgebraicGeometry.AlgebraicSpace.GeometricComponentTransport
import Langlands.AlgebraicGeometry.AlgebraicSpace.GeometricFibreFieldTests
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! # Structural connected fibres and geometric component counts -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Exactly one actual connected component means nonempty connectedness. -/
theorem componentCount_eq_one_iff_connectedSpace (A : Type v) [TopologicalSpace A] :
    ENat.card (_root_.ConnectedComponents A) = 1 ↔ ConnectedSpace A := by
  rw [ENat.card_eq_one_iff_unique, unique_iff_subsingleton_and_nonempty]
  constructor
  · rintro ⟨hc, hn⟩
    let := hc
    let : Nonempty A := _root_.ConnectedComponents.nonempty_iff_nonempty.mp hn
    have hp : PreconnectedSpace A := preconnectedSpace_iff_connectedComponent.mpr (by
      intro x
      apply Set.eq_univ_of_forall
      intro y
      exact _root_.ConnectedComponents.coe_eq_coe'.mp
        (Subsingleton.elim (_root_.ConnectedComponents.mk y) (_root_.ConnectedComponents.mk x)))
    exact { toPreconnectedSpace := hp, toNonempty := inferInstance }
  · intro h
    let := h
    exact ⟨inferInstance, inferInstance⟩

variable {S : Scheme.{u}}

/-- The relative functor of points of the base is terminal. -/
def basePresheafIsTerminal (S : Scheme.{u}) :
    IsTerminal ((schemeYoneda S).obj (Over.mk (𝟙 S))) :=
  Over.mkIdTerminal.isTerminalObj (schemeYoneda S)

/-- The canonical morphism of a space to its base, viewed as a relative space. -/
def structuralMorphism (X : AlgebraicSpace S) :
    X ⟶ (schemeToSpace S).obj (Over.mk (𝟙 S)) :=
  homMk ((basePresheafIsTerminal S).from X.presheaf)

/-- A fibre of the structural morphism is the actual product over the relative base. -/
def structuralFibreIso (X : AlgebraicSpace S) {V : Over S}
    (y : (schemeYoneda S).obj V ⟶ (schemeYoneda S).obj (Over.mk (𝟙 S))) :
    X.presheaf ⨯ (schemeYoneda S).obj V ≅ Limits.pullback (hom (structuralMorphism X)) y := by
  have hy : y = (basePresheafIsTerminal S).from ((schemeYoneda S).obj V) :=
    (basePresheafIsTerminal S).hom_ext _ _
  subst y
  exact (IsPullback.of_is_product
    (limit.isLimit (pair X.presheaf ((schemeYoneda S).obj V)))
    (basePresheafIsTerminal S)).isoPullback

/-- Structural geometric connectedness is tested by represented products over every field. -/
theorem hasGeometricallyConnectedFibres_structural_iff (X : AlgebraicSpace S) :
    HasGeometricallyConnectedFibres (structuralMorphism X) ↔
      ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S),
        @ConnectedSpace (Points (X.presheaf ⨯ (schemeYoneda S).obj (Over.mk s)))
          (pointTopology _) := by
  constructor
  · intro h K _ s
    let y := (basePresheafIsTerminal S).from ((schemeYoneda S).obj (Over.mk s))
    let := pointTopology (X.presheaf ⨯ (schemeYoneda S).obj (Over.mk s))
    let := pointTopology (Limits.pullback (hom (structuralMorphism X)) y)
    exact (Points.isoHomeomorph (structuralFibreIso X y)).connectedSpace_iff.mpr (h K s y)
  · intro h K _ s y
    let := pointTopology (X.presheaf ⨯ (schemeYoneda S).obj (Over.mk s))
    let := pointTopology (Limits.pullback (hom (structuralMorphism X)) y)
    exact (Points.isoHomeomorph (structuralFibreIso X y)).connectedSpace_iff.mp (h K s)

/-- The structural morphism has geometrically connected nonempty fibres exactly when
all canonical geometric fibres have one actual connected component. -/
theorem hasGeometricallyConnectedFibres_structural_iff_componentCount
    (B : Type u) [CommRing B] (X : AlgebraicSpace (Spec (CommRingCat.of B)))
    (hX : FinitePresentationOverRing B X) :
    HasGeometricallyConnectedFibres (structuralMorphism X) ↔
      ∀ p, geometricFibreComponentCount B X p = 1 := by
  constructor
  · intro h p
    let := pointTopology (X.presheaf ⨯ (schemeYoneda _).obj
      (Over.mk (SchemeFiberGeometry.componentCountGeometricPoint p)))
    exact (componentCount_eq_one_iff_connectedSpace _).mpr
      ((hasGeometricallyConnectedFibres_structural_iff X).mp h
        (AlgebraicClosure ((Spec (CommRingCat.of B)).residueField p))
        (SchemeFiberGeometry.componentCountGeometricPoint p))
  · intro h
    apply (hasGeometricallyConnectedFibres_iff_algClosed (structuralMorphism X)).mpr
    intro K _ _ s y
    let p := s (IsLocalRing.closedPoint K)
    obtain ⟨U, a, ha, hs, hU⟩ := hX
    let := hU.1
    let := hU.2
    let := pointTopology (X.presheaf ⨯ (schemeYoneda _).obj (Over.mk s))
    let := pointTopology (X.presheaf ⨯ (schemeYoneda _).obj
      (Over.mk (SchemeFiberGeometry.componentCountGeometricPoint p)))
    have hc : ENat.card (@_root_.ConnectedComponents
        (Points (X.presheaf ⨯ (schemeYoneda _).obj (Over.mk s))) (pointTopology _)) = 1 :=
      (ENat.card_congr (GeometricComponentTransport.geometricFibreEquiv X a ha hs s p rfl)).trans
        (h p)
    have hconn := (componentCount_eq_one_iff_connectedSpace _).mp hc
    let := pointTopology (Limits.pullback (hom (structuralMorphism X)) y)
    exact (Points.isoHomeomorph (structuralFibreIso X y)).connectedSpace_iff.mp hconn

end Langlands.AlgebraicGeometry.AlgebraicSpace

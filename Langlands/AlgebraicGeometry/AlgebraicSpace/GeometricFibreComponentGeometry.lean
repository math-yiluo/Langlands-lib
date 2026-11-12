import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasPointTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.PointTopologyIso
import Langlands.AlgebraicGeometry.AlgebraicSpace.GeometricFibreComponentsStatement
import Langlands.AlgebraicGeometry.SchemeGeometricComponentCountStatement
import Langlands.AlgebraicGeometry.LocallyNoetherianConnectedComponentOpenProof
import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Actual geometric fibre component counts for algebraic spaces -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The base change of a scheme atlas along a represented factor, still as a chart over S. -/
def productAtlasMap {F : Presheaf S} {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) (V : Over S) :
    (schemeYoneda S).obj (U ⨯ V) ⟶ F ⨯ (schemeYoneda S).obj V :=
  prodComparison (schemeYoneda S) U V ≫ prod.map a (𝟙 _)

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

/-- Represented base change preserves the étaleness of the atlas. -/
theorem isEtale_productAtlasMap {F : Presheaf S} {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) (ha : IsEtale a) (V : Over S) :
    IsEtale (productAtlasMap a V) := by
  have hprod : IsEtale (prod.map a (𝟙 ((schemeYoneda S).obj V))) :=
    MorphismProperty.of_isPullback
      (P := (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative
        (schemeYoneda S))
      (IsPullback.of_prod_fst_with_id a ((schemeYoneda S).obj V)) ha
  exact hprod.iso_comp (asIso (prodComparison (schemeYoneda S) U V))

/-- Represented base change preserves geometric surjectivity of the atlas. -/
theorem isSurjective_productAtlasMap {F : Presheaf S} {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) (hs : IsSurjective a) (V : Over S) :
    IsSurjective (productAtlasMap a V) := by
  have hprod : IsSurjective (prod.map a (𝟙 ((schemeYoneda S).obj V))) :=
    MorphismProperty.of_isPullback
      (P := (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).relative
        (schemeYoneda S))
      (IsPullback.of_prod_fst_with_id a ((schemeYoneda S).obj V)) hs
  exact (MorphismProperty.cancel_left_of_respectsIso
    ((MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).relative
      (schemeYoneda S)) (prodComparison (schemeYoneda S) U V) _).mpr hprod

/-- A Noetherian space has finitely many connected components. -/
theorem finite_connectedComponents_of_noetherian {A : Type v} [TopologicalSpace A]
    [NoetherianSpace A] : Finite (ConnectedComponents A) := by
  let : DiscreteTopology (ConnectedComponents A) :=
    ConnectedComponents.discreteTopology_iff.mpr
      Langlands.AlgebraicGeometry.isOpen_connectedComponent_of_noetherianSpace
  exact finite_of_compact_of_discrete

/-- The exact geometric fibre component count appearing in Conrad's space statement. -/
def geometricFibreComponentCount (B : Type u) [CommRing B]
    (X : AlgebraicSpace (Spec (CommRingCat.of B))) (p : Spec (CommRingCat.of B)) : ℕ∞ :=
  ENat.card
    (@ConnectedComponents
      (Points (X.presheaf ⨯ (schemeYoneda (Spec (CommRingCat.of B))).obj
        (Over.mk (SchemeFiberGeometry.componentCountGeometricPoint p))))
      (pointTopology _))

/-- Every geometric fibre of a space with a quasi-compact, locally finitely presented
atlas has a Noetherian point space. Quasi-separatedness is not needed for this conclusion. -/
theorem noetherian_geometricFibrePoints (B : Type u) [CommRing B]
    (X : AlgebraicSpace (Spec (CommRingCat.of B))) (hX : FinitePresentationOverRing B X)
    (p : Spec (CommRingCat.of B)) :
    letI := pointTopology (X.presheaf ⨯ (schemeYoneda (Spec (CommRingCat.of B))).obj
      (Over.mk (SchemeFiberGeometry.componentCountGeometricPoint p)))
    NoetherianSpace (Points (X.presheaf ⨯ (schemeYoneda (Spec (CommRingCat.of B))).obj
      (Over.mk (SchemeFiberGeometry.componentCountGeometricPoint p)))) := by
  obtain ⟨U, a, ha, hs, hU⟩ := hX
  let := hU.1
  let := hU.2
  let V : Over (Spec (CommRingCat.of B)) :=
    Over.mk (SchemeFiberGeometry.componentCountGeometricPoint p)
  let : IsNoetherian V.left := by
    change IsNoetherian (Spec (CommRingCat.of
      (AlgebraicClosure ((Spec (CommRingCat.of B)).residueField p))))
    infer_instance
  let P : Scheme.{u} := Limits.pullback U.hom V.hom
  let : IsNoetherian P :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
        (Limits.pullback.snd U.hom V.hom)
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
        (Limits.pullback.snd U.hom V.hom) }
  let : NoetherianSpace (U ⨯ V).left :=
    (noetherianSpace_iff_of_homeomorph (Over.prodLeftIsoPullback U V).hom.homeomorph).mpr
      inferInstance
  let := pointTopology (X.presheaf ⨯ (schemeYoneda (Spec (CommRingCat.of B))).obj V)
  exact noetherianSpace_of_surjective (chartPointMap (productAtlasMap a V))
    (continuous_schemePoint_chart _ (isEtale_productAtlasMap a ha V))
    (surjective_chartPointMap _ (isSurjective_productAtlasMap a hs V))

/-- In particular the geometric component count is always finite under finite presentation. -/
theorem geometricFibreComponentCount_ne_top (B : Type u) [CommRing B]
    (X : AlgebraicSpace (Spec (CommRingCat.of B))) (hX : FinitePresentationOverRing B X)
    (p : Spec (CommRingCat.of B)) : geometricFibreComponentCount B X p ≠ ⊤ := by
  let := pointTopology (X.presheaf ⨯ (schemeYoneda (Spec (CommRingCat.of B))).obj
    (Over.mk (SchemeFiberGeometry.componentCountGeometricPoint p)))
  let := noetherian_geometricFibrePoints B X hX p
  let := finite_connectedComponents_of_noetherian
    (A := Points (X.presheaf ⨯ (schemeYoneda (Spec (CommRingCat.of B))).obj
      (Over.mk (SchemeFiberGeometry.componentCountGeometricPoint p))))
  exact ENat.card_lt_top_of_finite.ne

/-- The named component count is a definitional rephrasing of the unchanged exact target. -/
theorem geometricFibreComponentsConstructibleStatement_iff :
    GeometricFibreComponentsConstructibleStatement.{u} ↔
      ∀ (B : Type u) [CommRing B] (X : AlgebraicSpace (Spec (CommRingCat.of B))),
        IsQuasiSeparated X → FinitePresentationOverRing B X → ∀ n : ℕ,
          IsConstructible {p | geometricFibreComponentCount B X p = n} := Iff.rfl

end Langlands.AlgebraicGeometry.AlgebraicSpace

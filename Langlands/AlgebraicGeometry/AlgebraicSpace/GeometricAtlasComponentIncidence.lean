import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasComponentIncidence
import Langlands.AlgebraicGeometry.AlgebraicSpace.GeometricFibreComponentGeometry

/-! # Finite atlas incidence for actual geometric fibres -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The represented geometric fibre of a scheme chart, kept as an object over the base. -/
abbrev geometricAtlasObject (B : Type u) [CommRing B]
    (U : Over (Spec (CommRingCat.of B))) (p : Spec (CommRingCat.of B)) :
    Over (Spec (CommRingCat.of B)) :=
  U ⨯ Over.mk (SchemeFiberGeometry.componentCountGeometricPoint p)

/-- A quasi-compact chart locally of finite presentation has a Noetherian geometric fibre. -/
theorem noetherian_geometricAtlasObject (B : Type u) [CommRing B]
    (U : Over (Spec (CommRingCat.of B)))
    [LocallyOfFinitePresentation U.hom] [QuasiCompact U.hom]
    (p : Spec (CommRingCat.of B)) :
    NoetherianSpace (geometricAtlasObject B U p).left := by
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
  exact (noetherianSpace_iff_of_homeomorph
    (Over.prodLeftIsoPullback U V).hom.homeomorph).mpr inferInstance

/-- The component space of a geometric chart fibre is discrete. -/
theorem discrete_geometricAtlasComponents (B : Type u) [CommRing B]
    (U : Over (Spec (CommRingCat.of B)))
    [LocallyOfFinitePresentation U.hom] [QuasiCompact U.hom]
    (p : Spec (CommRingCat.of B)) :
    DiscreteTopology (_root_.ConnectedComponents (geometricAtlasObject B U p).left) := by
  let := noetherian_geometricAtlasObject B U p
  exact _root_.ConnectedComponents.discreteTopology_iff.mpr
    Langlands.AlgebraicGeometry.isOpen_connectedComponent_of_noetherianSpace

/-- There are only finitely many vertices in the geometric chart's incidence relation. -/
theorem finite_geometricAtlasComponents (B : Type u) [CommRing B]
    (U : Over (Spec (CommRingCat.of B)))
    [LocallyOfFinitePresentation U.hom] [QuasiCompact U.hom]
    (p : Spec (CommRingCat.of B)) :
    Finite (_root_.ConnectedComponents (geometricAtlasObject B U p).left) := by
  let := noetherian_geometricAtlasObject B U p
  exact finite_connectedComponents_of_noetherian

/-- Kernel-pair incidence for the geometric base change of an étale chart. -/
def geometricAtlasComponentIncidence (B : Type u) [CommRing B]
    {F : Presheaf (Spec (CommRingCat.of B))}
    {U : Over (Spec (CommRingCat.of B))}
    (a : (schemeYoneda _).obj U ⟶ F) (ha : IsEtale a)
    (p : Spec (CommRingCat.of B)) :
    _root_.ConnectedComponents (geometricAtlasObject B U p).left →
      _root_.ConnectedComponents (geometricAtlasObject B U p).left → Prop :=
  atlasComponentIncidence
    (productAtlasMap a (Over.mk (SchemeFiberGeometry.componentCountGeometricPoint p)))
    (isEtale_productAtlasMap a ha _).representable

/-- The generated geometric incidence quotient is finite. -/
theorem finite_geometricAtlasComponentQuotient (B : Type u) [CommRing B]
    {F : Presheaf (Spec (CommRingCat.of B))}
    {U : Over (Spec (CommRingCat.of B))}
    (a : (schemeYoneda _).obj U ⟶ F) (ha : IsEtale a)
    [LocallyOfFinitePresentation U.hom] [QuasiCompact U.hom]
    (p : Spec (CommRingCat.of B)) :
    Finite (Quot (geometricAtlasComponentIncidence B a ha p)) := by
  let := finite_geometricAtlasComponents B U p
  infer_instance

/-- Components of the actual geometric presheaf fibre are its finite atlas incidence quotient. -/
def geometricAtlasConnectedComponentsEquiv (B : Type u) [CommRing B]
    {F : Presheaf (Spec (CommRingCat.of B))}
    {U : Over (Spec (CommRingCat.of B))}
    (a : (schemeYoneda _).obj U ⟶ F) (ha : IsEtale a) (hs : IsSurjective a)
    [LocallyOfFinitePresentation U.hom] [QuasiCompact U.hom]
    (p : Spec (CommRingCat.of B)) :
    Quot (geometricAtlasComponentIncidence B a ha p) ≃
      @_root_.ConnectedComponents
        (Points (F ⨯ (schemeYoneda _).obj
          (Over.mk (SchemeFiberGeometry.componentCountGeometricPoint p))))
        (pointTopology _) := by
  letI := discrete_geometricAtlasComponents B U p
  exact atlasConnectedComponentsEquiv
    (productAtlasMap a (Over.mk (SchemeFiberGeometry.componentCountGeometricPoint p)))
    (isEtale_productAtlasMap a ha _) (isSurjective_productAtlasMap a hs _)

/-- Compute the exact component count from the finite geometric atlas incidence quotient. -/
theorem geometricFibreComponentCount_eq_card_incidence (B : Type u) [CommRing B]
    (X : AlgebraicSpace (Spec (CommRingCat.of B)))
    {U : Over (Spec (CommRingCat.of B))}
    (a : (schemeYoneda _).obj U ⟶ X.presheaf) (ha : IsEtale a) (hs : IsSurjective a)
    [LocallyOfFinitePresentation U.hom] [QuasiCompact U.hom]
    (p : Spec (CommRingCat.of B)) :
    geometricFibreComponentCount B X p =
      ENat.card (Quot (geometricAtlasComponentIncidence B a ha p)) :=
  (ENat.card_congr (geometricAtlasConnectedComponentsEquiv B a ha hs p)).symm

/-- Preserving vertices and their incidence preserves the geometric component count. -/
theorem geometricFibreComponentCount_eq_of_incidenceEquiv (B : Type u) [CommRing B]
    (X : AlgebraicSpace (Spec (CommRingCat.of B)))
    {U : Over (Spec (CommRingCat.of B))}
    (a : (schemeYoneda _).obj U ⟶ X.presheaf) (ha : IsEtale a) (hs : IsSurjective a)
    [LocallyOfFinitePresentation U.hom] [QuasiCompact U.hom]
    (p q : Spec (CommRingCat.of B))
    (e : _root_.ConnectedComponents (geometricAtlasObject B U p).left ≃
      _root_.ConnectedComponents (geometricAtlasObject B U q).left)
    (he : ∀ c d, geometricAtlasComponentIncidence B a ha p c d ↔
      geometricAtlasComponentIncidence B a ha q (e c) (e d)) :
    geometricFibreComponentCount B X p = geometricFibreComponentCount B X q := by
  rw [geometricFibreComponentCount_eq_card_incidence B X a ha hs p,
    geometricFibreComponentCount_eq_card_incidence B X a ha hs q]
  exact ENat.card_congr (Quot.congr e he)

end Langlands.AlgebraicGeometry.AlgebraicSpace

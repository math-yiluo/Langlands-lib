import Langlands.AlgebraicGeometry.AlgebraicSpace.RestrictionPointTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.AlgebraicallyClosedAtlasComponents
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChangeComparison

/-! # Geometric connected components under base change -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace GeometricComponentTransport

/-- A homeomorphism transports the actual connected-component quotient. -/
def componentsEquiv {A : Type v} {B : Type w} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) : _root_.ConnectedComponents A ≃ _root_.ConnectedComponents B where
  toFun := e.continuous.connectedComponentsMap
  invFun := e.symm.continuous.connectedComponentsMap
  left_inv x := by
    obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe x
    simp
  right_inv x := by
    obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe x
    simp

variable {S : Scheme.{u}} {K L : Type u} [Field K] [Field L]

/-- Extension of an algebraically closed relative field preserves actual components. -/
def algClosedBaseChangeEquiv [IsAlgClosed K]
    (X : AlgebraicSpace S) {U : Over S} (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (ha : IsEtale a) (hs : IsSurjective a)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (b : Spec (CommRingCat.of K) ⟶ S)
    (e : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
    (c : Spec (CommRingCat.of L) ⟶ S) (hc : e ≫ b = c) :
    @_root_.ConnectedComponents (Points (baseChange c X).presheaf) (pointTopology _) ≃
      @_root_.ConnectedComponents (Points (baseChange b X).presheaf) (pointTopology _) := by
  letI := pointTopology ((restrictPresheaf c).obj X.presheaf)
  letI := pointTopology ((restrictPresheaf e).obj ((restrictPresheaf b).obj X.presheaf))
  letI := pointTopology (((restrictPresheaf b).obj X.presheaf) ⨯
    (schemeYoneda _).obj (Over.mk e))
  letI := pointTopology ((restrictPresheaf b).obj X.presheaf)
  letI : LocallyOfFiniteType ((Over.pullback b).obj U).hom := by
    change LocallyOfFiniteType (Limits.pullback.snd U.hom b)
    infer_instance
  letI : QuasiCompact ((Over.pullback b).obj U).hom := by
    change QuasiCompact (Limits.pullback.snd U.hom b)
    infer_instance
  let a' := restrictAtlas b a
  have ha' : IsEtale a' := relative_restrictAtlas _ ha
  have hs' : IsSurjective a' := relative_restrictAtlas _ hs
  exact (componentsEquiv (Points.isoHomeomorph
      (BaseChangeComparison.presheafIso b e c hc X.presheaf)).symm).trans
    ((componentsEquiv (RestrictionPoints.homeomorph e a' ha' hs')).trans
      (algebraicallyClosedAtlasComponentsEquiv a' ha' hs' e))

open SchemeFiberGeometry (componentCountGeometricPoint)

/-- Every algebraically closed geometric point factors through the canonical one
at its underlying ordinary point. -/
def geometricPointFactorization [IsAlgClosed L]
    (s : Spec (CommRingCat.of L) ⟶ S) (p : S)
    (hp : s (IsLocalRing.closedPoint L) = p) :
    {e : Spec (CommRingCat.of L) ⟶
        Spec (CommRingCat.of (AlgebraicClosure (S.residueField p))) //
      e ≫ componentCountGeometricPoint p = s} := by
  subst p
  let r : S.residueField (s (IsLocalRing.closedPoint L)) →+* L :=
    (Scheme.descResidueField (Scheme.stalkClosedPointTo s)).hom
  letI := r.toAlgebra
  let j : AlgebraicClosure (S.residueField (s (IsLocalRing.closedPoint L))) →ₐ[
      S.residueField (s (IsLocalRing.closedPoint L))] L := IsAlgClosed.lift
  refine ⟨Spec.map (CommRingCat.ofHom j.toRingHom), ?_⟩
  have hj : CommRingCat.ofHom (algebraMap (S.residueField (s (IsLocalRing.closedPoint L)))
      (AlgebraicClosure (S.residueField (s (IsLocalRing.closedPoint L))))) ≫
      CommRingCat.ofHom j.toRingHom =
        Scheme.descResidueField (Scheme.stalkClosedPointTo s) := by
    ext x
    exact j.commutes x
  dsimp only [componentCountGeometricPoint]
  rw [← Category.assoc, ← Spec.map_comp, hj]
  exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField L S s

/-- The actual component set of a geometric fibre is independent of the chosen
algebraically closed field over its ordinary point. -/
def geometricFibreEquiv [IsAlgClosed L]
    (X : AlgebraicSpace S) {U : Over S} (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (ha : IsEtale a) (hs : IsSurjective a)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (s : Spec (CommRingCat.of L) ⟶ S) (p : S)
    (hp : s (IsLocalRing.closedPoint L) = p) :
    @_root_.ConnectedComponents
        (Points (X.presheaf ⨯ (schemeYoneda S).obj (Over.mk s))) (pointTopology _) ≃
      @_root_.ConnectedComponents
        (Points (X.presheaf ⨯ (schemeYoneda S).obj
          (Over.mk (componentCountGeometricPoint p)))) (pointTopology _) := by
  let b := componentCountGeometricPoint p
  letI := pointTopology (X.presheaf ⨯ (schemeYoneda S).obj (Over.mk s))
  letI := pointTopology (X.presheaf ⨯ (schemeYoneda S).obj (Over.mk b))
  letI := pointTopology ((restrictPresheaf s).obj X.presheaf)
  letI := pointTopology ((restrictPresheaf b).obj X.presheaf)
  letI := pointTopology (baseChange s X).presheaf
  letI := pointTopology (baseChange b X).presheaf
  let e := geometricPointFactorization s p hp
  exact (componentsEquiv (baseChangePointsHomeomorph s X).symm).trans
    ((algClosedBaseChangeEquiv X a ha hs b e.val s e.property).trans
      (componentsEquiv (baseChangePointsHomeomorph b X)))

/-- Base change preserves the actual component set of each geometric fibre. -/
def baseChangeGeometricFibreEquiv {T : Scheme.{u}} (g : T ⟶ S)
    (X : AlgebraicSpace S) {U : Over S} (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (ha : IsEtale a) (hs : IsSurjective a)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] (q : T) :
    @_root_.ConnectedComponents
        (Points ((baseChange g X).presheaf ⨯ (schemeYoneda T).obj
          (Over.mk (componentCountGeometricPoint q)))) (pointTopology _) ≃
      @_root_.ConnectedComponents
        (Points (X.presheaf ⨯ (schemeYoneda S).obj
          (Over.mk (componentCountGeometricPoint (g q))))) (pointTopology _) := by
  let b := componentCountGeometricPoint q
  let s := b ≫ g
  letI := pointTopology ((baseChange g X).presheaf ⨯ (schemeYoneda T).obj (Over.mk b))
  letI := pointTopology (baseChange b (baseChange g X)).presheaf
  letI := pointTopology (baseChange s X).presheaf
  letI := pointTopology (X.presheaf ⨯ (schemeYoneda S).obj (Over.mk s))
  have hp : s (IsLocalRing.closedPoint (AlgebraicClosure (T.residueField q))) = g q := by
    change g (T.fromSpecResidueField q _) = g q
    rw [Scheme.fromSpecResidueField_apply]
  let e : (baseChange b (baseChange g X)).presheaf ≅ (baseChange s X).presheaf :=
    BaseChangeComparison.presheafIso g b s rfl X.presheaf
  exact (componentsEquiv (baseChangePointsHomeomorph b (baseChange g X)).symm).trans
    ((componentsEquiv (Points.isoHomeomorph e)).trans
        ((componentsEquiv (baseChangePointsHomeomorph s X)).trans
          (geometricFibreEquiv X a ha hs s (g q) hp)))

/-- The exact host component count commutes with every morphism of affine bases. -/
theorem geometricFibreComponentCount_baseChange
    (A B : Type u) [CommRing A] [CommRing B]
    (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (X : AlgebraicSpace (Spec (CommRingCat.of B)))
    (hX : FinitePresentationOverRing B X) (q : Spec (CommRingCat.of A)) :
    geometricFibreComponentCount A (baseChange g X) q =
      geometricFibreComponentCount B X (g q) := by
  obtain ⟨U, a, ha, hs, hU⟩ := hX
  let := hU.1
  let := hU.2
  exact ENat.card_congr (baseChangeGeometricFibreEquiv g X a ha hs q)

end GeometricComponentTransport

end Langlands.AlgebraicGeometry.AlgebraicSpace

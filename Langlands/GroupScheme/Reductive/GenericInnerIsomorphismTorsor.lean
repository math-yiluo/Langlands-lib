import Langlands.GroupScheme.LocalGroupIsoBaseChangeEquivalence
import Langlands.GroupScheme.LocalGroupIsoRefinement
import Langlands.GroupScheme.AutomorphicAction.BaseChange
import Langlands.GroupScheme.Adjoint.InnerAction
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.IntegralTorsorPoint
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints

/-! # An integral torsor of inner isomorphisms containing a generic isomorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace LocalGroupIso

variable {S : Scheme.{u}} {G H : GroupScheme S} {U : Over S}

/-- Evaluate a natural local isomorphism at a section of its parameter scheme. -/
def atSection (e : LocalGroupIso G H U) (p : Over.mk (𝟙 S) ⟶ U) : G ≅ H :=
  isoOfPoints
    (fun T => e.toFun ((Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ p))
    (by
      intro T W t g
      have ht : t ≫ (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) =
          (Over.homMk W.hom : W ⟶ Over.mk (𝟙 S)) := by
        apply Over.OverMorphism.ext
        exact Over.w t
      simpa only [← Category.assoc, ht] using
        e.naturality t ((Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ p) g)

/-- The evaluated isomorphism has the original local effect on all relative tests. -/
theorem comp_atSection_hom (e : LocalGroupIso G H U)
    (p : Over.mk (𝟙 S) ⟶ U) (T : Over S) (g : T ⟶ G.X) :
    g ≫ (e.atSection p).hom.hom.hom =
      e.toFun ((Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ p) g := by
  rw [atSection, comp_isoOfPoints_hom]
  intro T W t g
  have ht : t ≫ (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) =
      (Over.homMk W.hom : W ⟶ Over.mk (𝟙 S)) := by
    apply Over.OverMorphism.ext
    exact Over.w t
  simpa only [← Category.assoc, ht] using
    e.naturality t ((Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ p) g

end LocalGroupIso

/-- An actual integral adjoint torsor parametrizing inner-related isomorphisms,
with a point that recovers the specified generic isomorphism.

The action on isomorphisms is `d • φ = φ ∘ inner(d⁻¹)`, so it is a left action.
This is data and intrinsic compatibility, with no assertion that such data exist. -/
structure GenericInnerIsomorphismTorsor
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    (G H : GroupScheme (Spec (CommRingCat.of R)))
    (f : (baseChange (Spec.algebraMap R K)).obj G ≅
      (baseChange (Spec.algebraMap R K)).obj H) where
  adjoint : GroupScheme (Spec (CommRingCat.of R))
  isReductive_adjoint : IsReductive adjoint
  quotient : G ⟶ adjoint
  isQuotient : RelativeRoot.IsFppfQuotient (center G) quotient
  action : AutomorphicAction adjoint G
  action_restrict : action.restrict quotient = AutomorphicAction.conjugation (𝟙 G)
  genericQuotient : IsAdjointQuotient ((baseChange (Spec.algebraMap R K)).map quotient)
  genericAction :
    action.baseChange (Spec.algebraMap R K) = genericQuotient.innerAction
  parameter : Over (Spec (CommRingCat.of R))
  [modObj : CategoryTheory.ModObj adjoint.X parameter]
  flat : Flat parameter.hom
  surjective : Surjective parameter.hom
  quasiCompact : QuasiCompact parameter.hom
  shear : IsIso (CategoryTheory.ModObj.leftSMul adjoint.X parameter)
  localIso : LocalGroupIso G H parameter
  action_localIso : ∀ (T : Over (Spec (CommRingCat.of R)))
    (d : T ⟶ adjoint.X) (a : T ⟶ parameter) (g : T ⟶ G.X),
    localIso.toFun (d • a) g = localIso.toFun a (action.act d⁻¹ g)
  genericPoint : Over.mk (Spec.algebraMap R K) ⟶ parameter
  genericIso : (localIso.refine genericPoint).toBaseChangeIso = f

attribute [instance] GenericInnerIsomorphismTorsor.modObj

namespace GenericInnerIsomorphismTorsor

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  {f : (baseChange (Spec.algebraMap R K)).obj G ≅
    (baseChange (Spec.algebraMap R K)).obj H}
  (d : GenericInnerIsomorphismTorsor R K G H f)

/-- Lang's theorem and complete-ring lifting give a section of the supplied torsor. -/
theorem nonempty_section
    (I : Ideal R) [I.IsMaximal] [Finite (R ⧸ I)] [IsAdicComplete I R] :
    Nonempty (Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ d.parameter) := by
  let : Field (R ⧸ I) := Ideal.Quotient.field I
  let : Smooth d.adjoint.X.hom := d.isReductive_adjoint.smooth
  let : IsAffineHom d.adjoint.X.hom := d.isReductive_adjoint.isAffineHom
  obtain ⟨p⟩ := IntegralTorsorPoint.nonempty_ringPoint R I d.adjoint d.parameter
    (d.isReductive_adjoint.isConnectedReductive_algebraMap (R ⧸ I)).connectedSpace
    d.flat d.surjective d.quasiCompact d.shear
  exact ⟨(Langlands.AlgebraicGeometry.PointTopology.rationalPointEquiv
    R d.parameter).symm p⟩

end GenericInnerIsomorphismTorsor

end Langlands.GroupScheme

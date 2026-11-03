import Langlands.GroupScheme.NormalSubgroupQuotientStatement
import Langlands.AlgebraicGeometry.GeometricallyReducedOfAlgClosedProof
import Langlands.AlgebraicGeometry.Morphisms.LocallyOfFinitePresentationSourceDescent
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Mathlib.AlgebraicGeometry.Group.Smooth

/-! # Smooth targets of faithfully flat group homomorphisms -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Geometric reducedness descends through a flat surjective map of sources. -/
theorem geometricallyReduced_of_surjective_flat_comp
    {X Y S : Scheme.{u}} (p : X ⟶ Y) (f : Y ⟶ S)
    [Flat p] [Surjective p] [GeometricallyReduced (p ≫ f)] :
    GeometricallyReduced f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x ↦ ?_⟩
  have : IsReduced (pullback (p ≫ f) x) :=
    pullback_of_geometrically GeometricallyReduced.geometrically_isReduced K x
  have : IsReduced (pullback p (pullback.fst f x)) :=
    isReduced_of_isOpenImmersion (pullbackRightPullbackFstIso f x p).hom
  exact GeometricallyReducedOfAlgClosedProof.isReduced_of_flat_of_surjective
    (pullback.snd p (pullback.fst f x))

end Langlands.AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Smoothness descends along flat surjective locally finitely presented
homomorphisms of group schemes over arbitrary fields. -/
def FppfHomSmoothTargetStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q),
    Smooth G.X.hom → Flat q.hom.hom.left → Surjective q.hom.hom.left →
      LocallyOfFinitePresentation q.hom.hom.left → Smooth Q.X.hom

variable {k : Type u} [Field k]
    {G Q : GroupScheme (Spec (CommRingCat.of k))}

/-- A flat surjective locally finitely presented homomorphism from a smooth group
has smooth target. No smoothness hypothesis on its kernel is needed. -/
theorem smooth_target_of_surjective_flat_hom (q : G ⟶ Q)
    [Smooth G.X.hom] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left] : Smooth Q.X.hom := by
  have : LocallyOfFinitePresentation (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : LocallyOfFinitePresentation Q.X.hom :=
    Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_surjective_flat_comp
      q.hom.hom.left Q.X.hom
  have : GeometricallyReduced G.X.hom :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.geometricallyReduced_of_smooth _
  have : GeometricallyReduced (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : GeometricallyReduced Q.X.hom :=
    Langlands.AlgebraicGeometry.geometricallyReduced_of_surjective_flat_comp
      q.hom.hom.left Q.X.hom
  let : GrpObj (Over.mk Q.X.hom) := inferInstanceAs (GrpObj Q.X)
  exact AlgebraicGeometry.smooth_of_grpObj Q.X.hom

/-- The named smooth-target proposition follows from reducedness and
finite-presentation descent and the group-scheme smoothness theorem. -/
theorem fppfHomSmoothTarget : FppfHomSmoothTargetStatement.{u} := by
  intro k _ G Q q hG hflat hsurj hfp
  exact smooth_target_of_surjective_flat_hom q

namespace RelativeRoot

/-- An existing fppf quotient of a smooth group over an arbitrary field is smooth. -/
theorem IsFppfQuotient.smooth_target {H : SubgroupFunctor G} {q : G ⟶ Q}
    (hq : IsFppfQuotient H q) [Smooth G.X.hom] : Smooth Q.X.hom := by
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  exact smooth_target_of_surjective_flat_hom q

end RelativeRoot
end Langlands.GroupScheme

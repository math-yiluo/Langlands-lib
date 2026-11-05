import Langlands.Geometry.Building.CentralIsogenyFunctions
import Langlands.GroupScheme.Rational.DerivedRelativeRoots

/-! # Actual roots and root points through a central cover of the derived group -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
    {R T A S : CommGroupScheme (Spec (CommRingCat.of k))}
    {C D G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom C.X.hom] [IsAffineHom D.X.hom] [IsAffineHom G.X.hom]
    [LocallyOfFiniteType C.X.hom] [LocallyOfFiniteType D.X.hom]
    [Smooth G.X.hom]
    (π : C ⟶ D) (hπ : IsCentralIsogeny π)
    (d : D ⟶ G) (hd : IsDerivedSubgroup d)
    (iC : R.toGrp ⟶ C) (iD : T.toGrp ⟶ D) (iG : S.toGrp ⟶ G)
    (t : R ⟶ T) (e : T ⟶ S) (c : A ⟶ S)
    (hC : iC ≫ π = CommGroupScheme.groupHom t ≫ iD)
    (hD : iD ≫ d = CommGroupScheme.groupHom e ≫ iG)
    (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hR : IsSplitTorus R.toGrp) (hT : IsSplitTorus T.toGrp)
    (hS : IsSplitTorus S.toGrp) (hA : IsSplitTorus A.toGrp)
    [Flat (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    [Surjective (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    (hc : IsCentral (CommGroupScheme.groupHom c ≫ iG))

/-- The actual ambient-to-cover root bijection is the composition of the
derived restriction with central-isogeny pullback. -/
def derivedCoverRootPullbackEquiv : relativeRoots iG ≃ relativeRoots iC :=
  (RelativeRoot.derivedRelativeRootEquiv e c iD iG d hd hD hT hS hA hc).trans
    (centralIsogenyRootPullbackEquiv π hπ hR hT t hC ht)

@[simp] theorem derivedCoverRootPullbackEquiv_coe (a : relativeRoots iG) :
    (derivedCoverRootPullbackEquiv π hπ d hd iC iD iG t e c hC hD ht
      hR hT hS hA hc a : characterLattice R) = t ≫ e ≫ a.val := rfl

/-- Corresponding actual root groups have multiplicatively equivalent
rational points through the composite of the central cover and derived inclusion. -/
def derivedCoverRootGroupPointsEquiv (a : relativeRoots iG) :
    rootGroupPoints iC (t ≫ e ≫ a.val) ≃* rootGroupPoints iG a.val :=
  (centralIsogenyRootGroupPointsEquiv π hπ hR t hC ht
    (RelativeRoot.derivedRelativeRootEquiv e c iD iG d hd hD hT hS hA hc a)).trans
    (RelativeRoot.derivedRelativeRootPointsEquiv e c iD iG d hd hD hT hS hA hc
      a.val a.property (Over.mk (𝟙 _)))

omit [LocallyOfFiniteType C.X.hom] in
@[simp] theorem derivedCoverRootGroupPointsEquiv_coe (a : relativeRoots iG)
    (g : rootGroupPoints iC (t ≫ e ≫ a.val)) :
    (derivedCoverRootGroupPointsEquiv π hπ d hd iC iD iG t e c hC hD ht
      hR hT hS hA hc a g : rationalPoints G) =
      rationalPoints.map (π ≫ d) g.val := by
  change (g.val ≫ π.hom.hom) ≫ d.hom.hom = g.val ≫ (π ≫ d).hom.hom
  rw [Grp.comp_hom_hom, Category.assoc]

include hπ hd hC hD ht hR hT hS hA hc in
omit [LocallyOfFiniteType C.X.hom] in
/-- The rational-point map of the actual composite has exactly the ambient
root group as the image of its corresponding source root group. -/
theorem map_rootGroupPoints_derivedCover (a : relativeRoots iG) :
    (rootGroupPoints iC (t ≫ e ≫ a.val)).map (rationalPoints.map (π ≫ d)) =
      rootGroupPoints iG a.val := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    have hm := (derivedCoverRootGroupPointsEquiv π hπ d hd iC iD iG t e c
      hC hD ht hR hT hS hA hc a ⟨g, hg⟩).property
    simpa only [derivedCoverRootGroupPointsEquiv_coe] using hm
  · intro g hg
    obtain ⟨gC, hCg⟩ := (derivedCoverRootGroupPointsEquiv π hπ d hd iC iD iG
      t e c hC hD ht hR hT hS hA hc a).surjective ⟨g, hg⟩
    refine ⟨gC.val, gC.property, ?_⟩
    have heq := congrArg Subtype.val hCg
    simpa only [derivedCoverRootGroupPointsEquiv_coe] using heq

include hπ hd hC hD ht hR hT hS hA hc in
omit [LocallyOfFiniteType C.X.hom] in
/-- On each corresponding source root group the actual composite is injective. -/
theorem injective_rootGroupPoints_derivedCover (a : relativeRoots iG) :
    Function.Injective (fun g : rootGroupPoints iC (t ≫ e ≫ a.val) =>
      rationalPoints.map (π ≫ d) g.val) := by
  intro g h heq
  apply (derivedCoverRootGroupPointsEquiv π hπ d hd iC iD iG t e c hC hD ht
    hR hT hS hA hc a).injective
  apply Subtype.ext
  simpa only [derivedCoverRootGroupPointsEquiv_coe] using heq

end Langlands.Geometry.Building

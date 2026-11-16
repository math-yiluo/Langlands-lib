import Langlands.GroupScheme.Reductive.RelativeRootScalingTorus
import Langlands.GroupScheme.AutomorphicAction.FppfCenterQuotient
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Fppf local lifting of independent monomials -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.splitTorus

variable (R : CommRingCat.{u}) {I J : Type u} [Fintype I] [Fintype J]

/-- A canonical fppf local lift of a tuple of unit values through independent monomials. -/
def exponentUnitsLift (m : J → I → ℤ) (hm : LinearIndependent ℤ m)
    (V : Over (Spec R)) (c : J → (Γ(V.left, ⊤))ˣ) :
    AutomorphicAction.FppfQuotientPointLift (exponentTorusProjection R m)
      ((pointsEquiv J V).symm c) := by
  have h := exponentTorusProjection_fppf R m hm
  have := h.1
  have := h.2.1
  have := h.2.2
  exact AutomorphicAction.fppfQuotientPointLift (exponentTorusProjection R m)
    ((pointsEquiv J V).symm c)

/-- The chosen lift realizes all prescribed monomial values on its covering test scheme. -/
theorem exponentUnitsLift_equation (m : J → I → ℤ) (hm : LinearIndependent ℤ m)
    (V : Over (Spec R)) (c : J → (Γ(V.left, ⊤))ˣ) (j : J) :
    let L := exponentUnitsLift R m hm V c
    (∏ i, pointsEquiv I L.cover L.lift i ^ m j i) =
      unitsRestrict J L.projection c j := by
  dsimp only
  let L := exponentUnitsLift R m hm V c
  calc
    (∏ i, pointsEquiv I L.cover L.lift i ^ m j i) =
        pointsEquiv J L.cover (L.lift ≫ (exponentTorusProjection R m).hom.hom) j :=
      (exponentTorusProjection_points R m L.cover L.lift j).symm
    _ = pointsEquiv J L.cover (L.projection ≫ (pointsEquiv J V).symm c) j :=
      congrArg (fun x => pointsEquiv J L.cover x j) L.commutes.symm
    _ = unitsRestrict J L.projection
        (pointsEquiv J V ((pointsEquiv J V).symm c)) j :=
      congrFun (pointsEquiv_naturality J L.projection ((pointsEquiv J V).symm c)) j
    _ = unitsRestrict J L.projection c j :=
      congrArg (fun y => unitsRestrict J L.projection y j)
        ((pointsEquiv J V).apply_symm_apply c)

/-- The local lift defines a singleton fppf cover of the original test scheme. -/
def exponentUnitsLiftCover (m : J → I → ℤ) (hm : LinearIndependent ℤ m)
    (V : Over (Spec R)) (c : J → (Γ(V.left, ⊤))ˣ) :
    Scheme.Cover.{u} Scheme.fppfPrecoverage V.left := by
  let L := exponentUnitsLift R m hm V c
  exact Scheme.Cover.mkOfCovers PUnit (fun _ => L.cover.left) (fun _ => L.projection.left)
    (fun v => by obtain ⟨w, hw⟩ := L.surjective.surj v; exact ⟨PUnit.unit, w, hw⟩)
    (fun _ => ⟨L.flat, L.locallyOfFinitePresentation⟩)

/-- Arbitrary unit values are realized by independent integer monomials after a flat,
surjective, locally finitely presented change of test scheme. -/
theorem exists_fppf_exponent_units (m : J → I → ℤ) (hm : LinearIndependent ℤ m)
    (V : Over (Spec R)) (c : J → (Γ(V.left, ⊤))ˣ) :
    ∃ (W : Over (Spec R)) (b : W ⟶ V) (t : I → (Γ(W.left, ⊤))ˣ),
      Flat b.left ∧ Surjective b.left ∧ LocallyOfFinitePresentation b.left ∧
      ∀ j, (∏ i, t i ^ m j i) = unitsRestrict J b c j := by
  let L := exponentUnitsLift R m hm V c
  exact ⟨L.cover, L.projection, pointsEquiv I L.cover L.lift,
    L.flat, L.surjective, L.locallyOfFinitePresentation,
    fun j => exponentUnitsLift_equation R m hm V c j⟩

end Langlands.GroupScheme.splitTorus

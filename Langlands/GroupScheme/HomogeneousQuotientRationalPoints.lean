import Langlands.GroupScheme.HomogeneousQuotientFiber
import Langlands.GroupScheme.PseudoParabolic
import Langlands.AlgebraicGeometry.PointTopology.SchemePoints

/-! # Rational points from actual local sections and quotient fibers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomogeneousQuotient

section LocalSections

variable (R : Type u) [CommRing R] [IsLocalRing R]
variable {X Y : Over (Spec (CommRingCat.of R))}

/-- The actual factorization of an identity-test point through an open
containing the image of the closed point of the local base. -/
def rationalPointInOpen (U : X.left.Opens) (p : RationalPoint R X)
    (hp : p.left (IsLocalRing.closedPoint R) ∈ U) :
    RationalPoint R (openOver R X U) :=
  (rationalPointEquiv R (openOver R X U)).symm
    (openPointLift R X R U (rationalPointEquiv R X p)
      ((range_subset_open_iff_closedPoint R X R U _).mpr (by
        rw [rationalPointEquiv_left]
        exact hp)))

@[reassoc]
theorem rationalPointInOpen_comp (U : X.left.Opens) (p : RationalPoint R X)
    (hp : p.left (IsLocalRing.closedPoint R) ∈ U) :
    rationalPointInOpen R U p hp ≫ openOverι R X U = p := by
  apply (rationalPointEquiv R X).injective
  rw [rationalPointEquiv_natural, rationalPointInOpen, Equiv.apply_symm_apply]
  exact openPointMap_lift R X R U _ _

/-- An actual rational lift obtained by composing the point's open
factorization with a section on that open. -/
def rationalLiftThroughOpenSection (U : X.left.Opens)
    (s : openOver R X U ⟶ Y) (p : RationalPoint R X)
    (hp : p.left (IsLocalRing.closedPoint R) ∈ U) : RationalPoint R Y :=
  rationalPointInOpen R U p hp ≫ s

theorem rationalLiftThroughOpenSection_comp (f : Y ⟶ X) (U : X.left.Opens)
    (s : openOver R X U ⟶ Y) (hs : s ≫ f = openOverι R X U)
    (p : RationalPoint R X) (hp : p.left (IsLocalRing.closedPoint R) ∈ U) :
    rationalLiftThroughOpenSection R U s p hp ≫ f = p := by
  rw [rationalLiftThroughOpenSection, Category.assoc, hs, rationalPointInOpen_comp]

/-- Zariski sections around every topological point give lifts of every
identity-test rational point, over any local base ring. -/
theorem rational_lifts_of_local_sections (f : Y ⟶ X)
    (hsections : ∀ x : X.left, ∃ (U : X.left.Opens) (s : openOver R X U ⟶ Y),
      x ∈ U ∧ s ≫ f = openOverι R X U) :
    ∀ p : RationalPoint R X, ∃ y : RationalPoint R Y, y ≫ f = p := by
  intro p
  obtain ⟨U, s, hp, hs⟩ := hsections (p.left (IsLocalRing.closedPoint R))
  exact ⟨rationalLiftThroughOpenSection R U s p hp,
    rationalLiftThroughOpenSection_comp R f U s hs p hp⟩

end LocalSections

section FiniteField

variable (k : Type u) [Field k] [Finite k]
variable (G P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G)
variable {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
variable [Mono i.hom.hom] [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
variable (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
  g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)

include hfib

/-- Transport the actual finite torsor bridge to identity-test rational points. -/
theorem rational_lifts_of_finite_torsor_identity
    (hfinite : FiniteFieldTorsorPointStatement.{u})
    [Smooth P.X.hom] [IsAffineHom P.X.hom] (hP : ConnectedSpace P.X.left) :
    ∀ p : RationalPoint k Q, ∃ g : RationalPoint k G.X, g ≫ q = p := by
  intro p
  obtain ⟨g, hg⟩ := Dynamic.rational_lifts_of_finite_torsor k G P q i hfib
    hfinite hP (rationalPointEquiv k Q p)
  refine ⟨(rationalPointEquiv k G.X).symm g, ?_⟩
  apply (rationalPointEquiv k Q).injective
  rw [rationalPointEquiv_natural, Equiv.apply_symm_apply]
  exact hg

end FiniteField

section PseudoParabolicFinite

variable (k : Type u) [Field k] [Finite k]
variable (G P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G)
variable [IsAffineHom G.X.hom]
variable {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
variable [Smooth q.left] [Surjective q.left] [QuasiCompact q.left]

/-- For the supplied smooth exact quotient, the remaining finite-field
structural input is connectedness of the pseudo-parabolic subgroup. The Lang
torsor proposition remains an explicit input. -/
theorem rational_lifts_pseudo_of_finite_torsor_and_connected
    (hi : IsPseudoParabolicSubgroup i) (hP : ConnectedSpace P.X.left)
    (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)
    (hfinite : FiniteFieldTorsorPointStatement.{u}) :
    ∀ p : RationalPoint k Q, ∃ g : RationalPoint k G.X, g ≫ q = p := by
  let : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : Smooth P.X.hom := smooth_subgroup_of_smooth_quotient G P i q hfib
  let : IsAffineHom P.X.hom := affine_subgroup_of_closed G P i hi.isClosedSubgroup
  exact rational_lifts_of_finite_torsor_identity k G P i q hfib hfinite hP

end PseudoParabolicFinite

end Langlands.GroupScheme.HomogeneousQuotient

import Langlands.GroupScheme.Reductive.SuppliedIsogenyRootUnit
import Langlands.GroupScheme.Reductive.RelativeIsogenyRootAlignment

/-! # Fppf alignment of supplied root restrictions over arbitrary rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SuppliedRootIsogeny

open LocalRootGroup LocalSplitCell

variable {R : Type u} [CommRing R]
  {I I' : Type u} [Fintype I] [Fintype I']
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
  {J J' : Type u} [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  [P.IsReduced] [Q.IsReduced]
  (hP : IsFibrewiseRootDatumOf I G i P) (hQ : IsFibrewiseRootDatumOf I' H j Q)
  {p : ℕ} (r : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
  (tau : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
    splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I')
  (hweight : ∀ m : I' → ℤ, tau ≫ splitTorus.exponentCharacter _ I' m =
    splitTorus.exponentCharacter _ I (r.weightMap m))
  (phi Phi : G ⟶ H)
  (hphi : i ≫ phi = CommGroupScheme.groupHom tau ≫ j)
  (hPhi : i ≫ Phi = CommGroupScheme.groupHom tau ≫ j)
  (hH : IsReductive H)
  (hmaxH : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
  [IsFinite phi.hom.hom.left] [IsFinite Phi.hom.hom.left]

include hP hQ hweight hphi hPhi hH hmaxH

/-- The canonical fppf cover and target torus point for selected supplied roots. -/
def selectedRootAlignmentLift
    {K : Type u} [Fintype K] (beta : K → J')
    (hind : LinearIndependent ℤ (fun a => Q.root (beta a)))
    {u : K → (Ga R ⟶ G)} {v : K → (Ga R ⟶ H)}
    (hu : ∀ a, IsRootParametrization i (P.root (r.indexEquiv (beta a))) (u a))
    (hv : ∀ a, IsRootParametrization j (Q.root (beta a)) (v a))
    (V : Over (Spec (CommRingCat.of R))) :=
  LocalSplitCell.rootAlignmentLift (fun a => Q.root (beta a)) hind V
    (fun a => rootRestrictionUnit i j hP hQ r tau hweight phi hphi hH hmaxH
      (beta a) (hu a) (hv a))
    (fun a => rootRestrictionUnit i j hP hQ r tau hweight Phi hPhi hH hmaxH
      (beta a) (hu a) (hv a))

/-- On every refinement, the canonical lift conjugates the second map to the
first on all selected supplied root points. -/
theorem selectedRootAlignmentLift_rootPoint
    {K : Type u} [Fintype K] (beta : K → J')
    (hind : LinearIndependent ℤ (fun a => Q.root (beta a)))
    {u : K → (Ga R ⟶ G)} {v : K → (Ga R ⟶ H)}
    (hu : ∀ a, IsRootParametrization i (P.root (r.indexEquiv (beta a))) (u a))
    (hv : ∀ a, IsRootParametrization j (Q.root (beta a)) (v a))
    (V Z : Over (Spec (CommRingCat.of R)))
    (d : Z ⟶ (selectedRootAlignmentLift i j hP hQ r tau hweight phi Phi hphi hPhi
      hH hmaxH beta hind hu hv V).cover) (a : K) (x : Γ(Z.left, ⊤)) :
    rootPoint (u a) Z x ≫ phi.hom.hom =
      ((d ≫ (selectedRootAlignmentLift i j hP hQ r tau hweight phi Phi hphi hPhi
        hH hmaxH beta hind hu hv V).lift) ≫ j.hom.hom) *
      (rootPoint (u a) Z x ≫ Phi.hom.hom) *
      ((d ≫ (selectedRootAlignmentLift i j hP hQ r tau hweight phi Phi hphi hPhi
        hH hmaxH beta hind hu hv V).lift) ≫ j.hom.hom)⁻¹ := by
  exact rootAlignmentLift_rootPoint j (fun a => Q.root (beta a)) hind u v hv phi Phi
    (fun a => rootRestrictionUnit i j hP hQ r tau hweight phi hphi hH hmaxH
      (beta a) (hu a) (hv a))
    (fun a => rootRestrictionUnit i j hP hQ r tau hweight Phi hPhi hH hmaxH
      (beta a) (hu a) (hv a))
    (fun a => r.rootFactor (beta a))
    (fun a => rootRestriction_unit_power_rootPoint i j hP hQ r tau hweight phi hphi
      hH hmaxH (beta a) (hu a) (hv a))
    (fun a => rootRestriction_unit_power_rootPoint i j hP hQ r tau hweight Phi hPhi
      hH hmaxH (beta a) (hu a) (hv a)) V Z d a x

/-- Two finite homomorphisms with the same supplied root-datum isogeny and torus
map are fppf-locally conjugate on any family of independent target roots. -/
theorem exists_fppf_selected_root_alignment
    {K : Type u} [Fintype K] (beta : K → J')
    (hind : LinearIndependent ℤ (fun a => Q.root (beta a)))
    (u : K → (Ga R ⟶ G)) (v : K → (Ga R ⟶ H))
    (hu : ∀ a, IsRootParametrization i (P.root (r.indexEquiv (beta a))) (u a))
    (hv : ∀ a, IsRootParametrization j (Q.root (beta a)) (v a))
    (V : Over (Spec (CommRingCat.of R))) :
    ∃ (W : Over (Spec (CommRingCat.of R))) (b : W ⟶ V)
      (t : W ⟶ (splitTorus (Spec (CommRingCat.of R)) I').X),
      Flat b.left ∧ Surjective b.left ∧ LocallyOfFinitePresentation b.left ∧
      ∀ (Z : Over (Spec (CommRingCat.of R))) (d : Z ⟶ W) (a : K) (x : Γ(Z.left, ⊤)),
        rootPoint (u a) Z x ≫ phi.hom.hom =
          ((d ≫ t) ≫ j.hom.hom) * (rootPoint (u a) Z x ≫ Phi.hom.hom) *
            ((d ≫ t) ≫ j.hom.hom)⁻¹ := by
  exact exists_fppf_root_alignment j (fun a => Q.root (beta a)) hind u v hv phi Phi
    (fun a => rootRestrictionUnit i j hP hQ r tau hweight phi hphi hH hmaxH
      (beta a) (hu a) (hv a))
    (fun a => rootRestrictionUnit i j hP hQ r tau hweight Phi hPhi hH hmaxH
      (beta a) (hu a) (hv a))
    (fun a => r.rootFactor (beta a))
    (fun a => rootRestriction_unit_power_rootPoint i j hP hQ r tau hweight phi hphi
      hH hmaxH (beta a) (hu a) (hv a))
    (fun a => rootRestriction_unit_power_rootPoint i j hP hQ r tau hweight Phi hPhi
      hH hmaxH (beta a) (hu a) (hv a)) V

/-- In particular, target simple roots can be aligned simultaneously after an
fppf change of any test scheme. -/
theorem exists_fppf_simple_root_alignment (bQ : Q.Base)
    (u : bQ.support → (Ga R ⟶ G)) (v : bQ.support → (Ga R ⟶ H))
    (hu : ∀ a : bQ.support, IsRootParametrization i (P.root (r.indexEquiv a)) (u a))
    (hv : ∀ a : bQ.support, IsRootParametrization j (Q.root a) (v a))
    (V : Over (Spec (CommRingCat.of R))) :
    ∃ (W : Over (Spec (CommRingCat.of R))) (b : W ⟶ V)
      (t : W ⟶ (splitTorus (Spec (CommRingCat.of R)) I').X),
      Flat b.left ∧ Surjective b.left ∧ LocallyOfFinitePresentation b.left ∧
      ∀ (Z : Over (Spec (CommRingCat.of R))) (d : Z ⟶ W)
        (a : bQ.support) (x : Γ(Z.left, ⊤)),
        rootPoint (u a) Z x ≫ phi.hom.hom =
          ((d ≫ t) ≫ j.hom.hom) * (rootPoint (u a) Z x ≫ Phi.hom.hom) *
            ((d ≫ t) ≫ j.hom.hom)⁻¹ :=
  exists_fppf_selected_root_alignment i j hP hQ r tau hweight phi Phi hphi hPhi
    hH hmaxH Subtype.val bQ.linearIndepOn_root.linearIndependent u v hu hv V

end Langlands.GroupScheme.SuppliedRootIsogeny

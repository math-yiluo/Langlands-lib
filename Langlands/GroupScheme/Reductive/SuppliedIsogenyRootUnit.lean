import Langlands.GroupScheme.Reductive.SuppliedIsogenyRootPower
import Langlands.GroupScheme.Reductive.RelativeIsogenyRootUnit

/-! # Unit coefficients of supplied root restrictions over arbitrary rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

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
  (phi : G ⟶ H) (hphi : i ≫ phi = CommGroupScheme.groupHom tau ≫ j)
  (hH : IsReductive H)
  (hmaxH : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
  (b : J')
  {u : Ga R ⟶ G} {v : Ga R ⟶ H}
  (hu : IsRootParametrization i (P.root (r.indexEquiv b)) u)
  (hv : IsRootParametrization j (Q.root b) v)
  [IsFinite phi.hom.hom.left]

/-- An actual root restriction of a finite ambient map is finite. -/
theorem rootRestriction_isFinite :
    IsFinite (rootRestriction i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv).hom.hom.left := by
  let f := rootRestriction i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv
  have : IsClosedImmersion u.hom.hom.left := hu.isClosedSubgroup
  have : IsClosedImmersion v.hom.hom.left := hv.isClosedSubgroup
  have hcomp : f.hom.hom.left ≫ v.hom.hom.left =
      u.hom.hom.left ≫ phi.hom.hom.left := by
    exact congrArg (fun h : Ga R ⟶ H => h.hom.hom.left)
      (rootRestriction_comp i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv)
  have : IsFinite (f.hom.hom.left ≫ v.hom.hom.left) := hcomp.symm ▸ inferInstance
  exact IsFinite.of_comp f.hom.hom.left v.hom.hom.left

/-- Finiteness forces the prescribed-power coefficient to be a unit over the
entire base ring. -/
theorem isUnit_rootRestrictionCoefficient :
    IsUnit (rootRestrictionCoefficient i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv) := by
  let f := rootRestriction i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv
  let : IsFinite f.hom.hom.left :=
    rootRestriction_isFinite i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv
  exact isUnit_coefficient_of_power_of_isFinite f _ (r.rootFactor b)
    (rootRestriction_power i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv)

/-- The unit coefficient of the actual supplied-root restriction. -/
def rootRestrictionUnit : Rˣ :=
  (isUnit_rootRestrictionCoefficient i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv).unit

@[simp] theorem coe_rootRestrictionUnit :
    (rootRestrictionUnit i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv : R) =
      rootRestrictionCoefficient i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv :=
  IsUnit.unit_spec _

/-- The actual root restriction has a unit-coefficient power formula on every
coefficient algebra. -/
theorem rootRestriction_unit_power (A : CommAlgCat.{u} (CommRingCat.of R)) (a : A) :
    (scalarOperation (rootRestriction i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv)).app A a =
      algebraMap R A (rootRestrictionUnit i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv : R) *
        a ^ r.rootFactor b := by
  rw [coe_rootRestrictionUnit]
  exact rootRestriction_power i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv A a

/-- The unit-coefficient formula holds in the ambient group on every scheme
test, including nonreduced tests. -/
theorem rootRestriction_unit_power_rootPoint (Z : Over (Spec (CommRingCat.of R)))
    (a : Γ(Z.left, ⊤)) :
    rootPoint u Z a ≫ phi.hom.hom =
      rootPoint v Z (baseScalar Z
        (rootRestrictionUnit i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv : R) *
          a ^ r.rootFactor b) := by
  rw [coe_rootRestrictionUnit]
  exact rootRestriction_power_rootPoint i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv Z a

end Langlands.GroupScheme.SuppliedRootIsogeny

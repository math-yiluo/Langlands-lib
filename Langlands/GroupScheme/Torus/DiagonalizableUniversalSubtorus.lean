import Langlands.GroupScheme.Torus.UniversalSubtorusKernel
import Langlands.GroupScheme.Torus.DiagonalizablePowerDecomposition
import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Torus.UniversalSubtorusTransport

/-! # Universal subtori of diagonalizable groups over arbitrary schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Diagonalizable

theorem multiplication_exponent_eq_one (R : CommRingCat.{u}) (A : Type u)
    [AddCommGroup A] [Finite A] :
    multiplication (groupScheme R A).toGrp (AddMonoid.exponent A : ℤ) = 1 := by
  apply hom_ext_points
  intro U x
  rw [points_multiplication, Grp.Hom.hom_one, Mon.Hom.hom_one, MonObj.comp_one]
  apply (characterPointsEquiv R A U).injective
  rw [map_zpow, map_one]
  apply MonoidHom.ext
  intro a
  change (characterPointsEquiv R A U x a) ^ (AddMonoid.exponent A : ℤ) = 1
  rw [zpow_natCast, ← map_pow]
  have ha : a ^ AddMonoid.exponent A = 1 := by
    change AddMonoid.exponent A • a.toAdd = 0
    exact AddMonoid.exponent_nsmul_eq_zero a.toAdd
  rw [ha, map_one]

/-- The inclusion of the free-character factor in a diagonalizable group
over an arbitrary scheme. -/
def freeInclusionOverScheme (S : Scheme.{u}) {Λ I A : Type u}
    [AddCommGroup Λ] [AddCommGroup A] (e : Λ ≃+ (I → ℤ) × A) :
    RelativeMultiplicativeType.diagonalizable S (I → ℤ) ⟶
      RelativeMultiplicativeType.diagonalizable S Λ :=
  (GroupScheme.baseChange (Gm.toSpecZ S)).map
    (freeInclusion (CommRingCat.of (ULift.{u} ℤ)) e)

theorem isUniversalSubtorus_freeInclusionOverScheme
    (S : Scheme.{u}) {Λ I A : Type u}
    [AddCommGroup Λ] [AddCommGroup A] [Fintype I] [DecidableEq I] [Finite A]
    (e : Λ ≃+ (I → ℤ) × A) :
    IsUniversalSubtorus (freeInclusionOverScheme S e) := by
  let R := CommRingCat.of (ULift.{u} ℤ)
  let b := Gm.toSpecZ S
  let F := GroupScheme.baseChange b
  let Q := F.obj (groupScheme R A).toGrp
  let q := F.map (finiteProjection R e)
  have hj : IsClosedSubgroup (freeInclusionOverScheme S e) :=
    (isClosedSubgroup_freeInclusion R e).baseChange b
  have hT : RelativeTorus.IsTorus
      (RelativeMultiplicativeType.diagonalizable S (I → ℤ)) :=
    .of_isSplitTorus ((isSplitTorus_free R (I := I)).baseChange b)
  have hker : SubgroupFunctor.range (freeInclusionOverScheme S e) =
      SubgroupFunctor.range (kernelι q) := by
    change SubgroupFunctor.range (F.map (freeInclusion R e)) = _
    rw [SubgroupFunctor.range_baseChangeHom, ← kernel_finiteProjection R e,
      SubgroupFunctor.range_kernel_baseChange]
  have hQ : multiplication Q (AddMonoid.exponent A : ℤ) = 1 := by
    change multiplication (F.obj (groupScheme R A).toGrp) _ = _
    rw [← multiplication_baseChange b, multiplication_exponent_eq_one]
    apply Grp.hom_ext
    change (Over.pullback b).map
      (1 : (groupScheme R A).toGrp.X ⟶ (groupScheme R A).toGrp.X) =
      (1 : (Over.pullback b).obj (groupScheme R A).toGrp.X ⟶
        (Over.pullback b).obj (groupScheme R A).toGrp.X)
    exact (Functor.homMonoidHom (Over.pullback b)).map_one
  exact isUniversalSubtorus_of_kernel_torsion
    (freeInclusionOverScheme S e) q hj hT hker
    (Int.natCast_ne_zero.mpr AddMonoid.exponent_ne_zero_of_finite) hQ

end Langlands.GroupScheme.Diagonalizable

namespace Langlands.GroupScheme.RelativeMultiplicativeType

theorem IsDiagonalizable.exists_universalSubtorus
    {S : Scheme.{u}} {H : GroupScheme S} (hH : IsDiagonalizable H) :
    ∃ (T : GroupScheme S) (j : T ⟶ H), IsUniversalSubtorus j := by
  classical
  obtain ⟨Λ, hΛ, hfg, ⟨eH⟩⟩ := hH
  obtain ⟨I, A, hI, hA, hfin, ⟨e⟩⟩ := Diagonalizable.exists_freeFiniteEquiv Λ
  exact ⟨diagonalizable S (I → ℤ),
    Diagonalizable.freeInclusionOverScheme S e ≫ eH.inv,
    (Diagonalizable.isUniversalSubtorus_freeInclusionOverScheme S e).comp_iso eH.symm⟩

end Langlands.GroupScheme.RelativeMultiplicativeType

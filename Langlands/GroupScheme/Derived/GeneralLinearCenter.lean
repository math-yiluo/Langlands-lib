import Langlands.GroupScheme.Derived.GeneralLinearCenterDerivedStatement

/-! # The centre of the general linear group on every test scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable (n : Type) [Fintype n] [DecidableEq n] (R : CommRingCat.{u})

/-- A general-linear scheme point is central exactly when its matrix is a unit scalar.
This includes the empty index type. -/
theorem mem_center_iff_scalar (T : Over (Spec R)) (g : T ⟶ (groupScheme n R).X) :
    g ∈ (center (groupScheme n R)).carrier T ↔
      ∃ a : Γ(T.left, ⊤)ˣ,
        (pointsEquiv n R T g : Matrix n n Γ(T.left, ⊤)) =
          Matrix.scalar n (a : Γ(T.left, ⊤)) := by
  constructor
  · intro hg
    have hm : pointsEquiv n R T g ∈ Subgroup.center (GL n Γ(T.left, ⊤)) := by
      apply Subgroup.mem_center_iff.mpr
      intro h
      have hc := commute_of_mem_center hg ((pointsEquiv n R T).symm h)
      have he := congrArg (pointsEquiv n R T) hc.eq.symm
      simpa only [map_mul, MulEquiv.apply_symm_apply] using he
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hm
    obtain ⟨a, ha⟩ := hm
    exact ⟨a, (congrArg Units.val ha).symm⟩
  · rintro ⟨a, ha⟩
    let x := (Gm.pointsEquiv (Spec R) T).symm a
    have hx : x ≫ (scalarTorus n R).hom.hom = g := by
      apply (pointsEquiv n R T).injective
      rw [pointsEquiv_scalarTorus]
      apply Units.ext
      simpa only [x, MulEquiv.apply_symm_apply, Matrix.GeneralLinearGroup.coe_scalar] using
        ha.symm
    rw [← hx]
    exact isCentral_scalarTorus T x

/-- The scalar homomorphism has the centre as its full all-test range, even in rank zero. -/
theorem range_scalarTorus_eq_center :
    SubgroupFunctor.range (scalarTorus n R) = center (groupScheme n R) := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro g
  constructor
  · rintro ⟨x, rfl⟩
    exact isCentral_scalarTorus T x
  · intro hg
    obtain ⟨a, ha⟩ := (mem_center_iff_scalar n R T g).mp hg
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨(Gm.pointsEquiv (Spec R) T).symm a, ?_⟩
    apply (pointsEquiv n R T).injective
    rw [pointsEquiv_scalarTorus, MulEquiv.apply_symm_apply]
    exact Units.ext ha.symm

end Langlands.GroupScheme.GeneralLinear

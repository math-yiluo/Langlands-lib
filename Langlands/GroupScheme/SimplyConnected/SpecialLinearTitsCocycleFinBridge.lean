import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleFinCoordinates
import Langlands.GroupScheme.Reductive.SpecialLinearRoots

/-! # Comparing the finite and pivot-coordinate special-linear tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinearTitsCocycle

variable (n : ℕ)

/-- The finite and last-pivot coordinate products give the same diagonal entry. -/
theorem torusEntry_eq_lastPivot_torusWeights {A : Type*} [CommRing A]
    (τ : ULift.{u} (Fin n) → Aˣ) (x : Fin (n + 1)) :
    SpecialLinear.FinSucc.torusEntry τ x =
      SpecialLinear.torusWeights (Fin.last n)
        (fun c => τ ((lastPivotEquiv n).symm c)) x := by
  unfold SpecialLinear.FinSucc.torusEntry SpecialLinear.torusWeights
  exact Fintype.prod_equiv (lastPivotEquiv n) _ _ fun c => by
    change τ c ^ SpecialLinear.FinSucc.weightCoord n x c.down =
      τ ((lastPivotEquiv n).symm ((lastPivotEquiv n) c)) ^
        SpecialLinear.weightCoord (Fin.last n) x ((lastPivotEquiv n) c).down
    rw [Equiv.symm_apply_apply, weightCoord_lastPivotEquiv]
    rfl

/-- The last-pivot diagonal inclusion expressed on the finite coordinate torus. -/
def lastPivotDiagonalTorus (R : CommRingCat.{u}) :
    (splitTorus.commGroupScheme (Spec R) (ULift.{u} (Fin n))).toGrp ⟶
      SpecialLinear.groupScheme (Fin (n + 1)) R :=
  CommGroupScheme.groupHom (lastPivotTorusIso n (Spec R)).hom ≫
    SpecialLinear.diagonalTorus (Fin.last n) R

/-- The finite diagonal-torus inclusion is the published pivot inclusion after reindexing. -/
theorem fin_diagonalTorus_eq_lastPivot (R : CommRingCat.{u}) :
    SpecialLinear.FinSucc.diagonalTorus n R = lastPivotDiagonalTorus n R := by
  unfold lastPivotDiagonalTorus
  apply hom_ext_points
  intro Z t
  apply (SpecialLinear.pointsEquiv (Fin (n + 1)) R Z).injective
  rw [SpecialLinear.FinSucc.pointsEquiv_diagonalTorus, Grp.comp_hom_hom,
    ← Category.assoc, SpecialLinear.pointsEquiv_diagonalTorus]
  apply Subtype.ext
  rw [SpecialLinear.FinSucc.coe_torusMatrix, SpecialLinear.coe_torusUnits]
  congr 1
  funext x
  rw [torusEntry_eq_lastPivot_torusWeights]
  congr 2
  funext c
  exact (splitTorus.pointsEquiv_reindexIso_hom (Spec R) (lastPivotEquiv n) Z t c).symm

/-- Each finite root character is the pullback of the corresponding diagonal-weight difference. -/
theorem fin_rootChar_eq_lastPivot (k : Type u) [Field k] (x y : Fin (n + 1)) :
    SpecialLinear.FinSucc.rootChar n k x y =
      (lastPivotTorusIso n (Spec (CommRingCat.of k))).hom ≫
        (SpecialLinear.diagonalWeight (Fin.last n) (Spec (CommRingCat.of k)) x -
          SpecialLinear.diagonalWeight (Fin.last n) (Spec (CommRingCat.of k)) y) := by
  exact (lastPivotTorusIso_hom_comp_diagonalWeight_sub n k x y).symm

end Langlands.GroupScheme.SpecialLinearTitsCocycle

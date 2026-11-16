import Langlands.GroupScheme.Reductive.RankOneRingRelation
import Langlands.GroupScheme.Reductive.LocalWeylNormalizationProof

/-! # Dual-number coordinates of actual rank-one cells over rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RingRootCell

open LocalWeylNormalization Corepresented.RingCoordinates

namespace DualCell

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]

/-- The coefficient extension on dual numbers over arbitrary commutative rings. -/
def coefficientMap : DualNumber R →ₐ[R] DualNumber A :=
  DualNumber.lift ⟨(Algebra.ofId R (DualNumber A), DualNumber.eps),
    DualNumber.eps_mul_eps, fun _ => DualNumber.commute_eps_left _⟩

theorem coefficientMap_eps :
    coefficientMap A (DualNumber.eps : DualNumber R) = DualNumber.eps :=
  DualNumber.lift_apply_eps _

theorem snd_coefficientMap (x : DualNumber R) :
    (coefficientMap A x).snd = algebraMap R A x.snd := by
  rw [coefficientMap, DualNumber.lift_apply_apply]
  simp [Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl']

theorem coefficientMap_appTop_eps :
    (specMapOver (coefficientMap (R := R) A)).left.appTop (epsSec R) =
      epsSec A := by
  change (Spec.map (CommRingCat.ofHom (coefficientMap A).toRingHom)).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv DualNumber.eps) = _
  rw [specMap_appTop_inv]
  exact congrArg _ (coefficientMap_eps A)

/-- The unit `1 + c ε`, with its explicit inverse, over a commutative ring. -/
def unit (c : R) : (DualNumber R)ˣ where
  val := 1 + TrivSqZeroExt.inr c
  inv := 1 - TrivSqZeroExt.inr c
  val_inv := by
    rw [add_mul, one_mul, mul_sub, mul_one, TrivSqZeroExt.inr_mul_inr]
    abel
  inv_val := by
    rw [sub_mul, one_mul, mul_add, mul_one, TrivSqZeroExt.inr_mul_inr]
    abel

theorem pb_spec (x : Γ((base R).left, ⊤)) :
    WeylData.pb (specOver (CommRingCat.of R) A) x =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv
        (algebraMap R A ((Scheme.ΓSpecIso (CommRingCat.of R)).hom x)) := by
  change (Spec.map (CommRingCat.ofHom (algebraMap R A))).appTop x = _
  calc
    _ = (Spec.map (CommRingCat.ofHom (algebraMap R A))).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv
          ((Scheme.ΓSpecIso (CommRingCat.of R)).hom x)) := by
      rw [Iso.hom_inv_id_apply]
    _ = _ := specMap_appTop_inv _ _

end DualCell

namespace CellData

variable {R : Type u} [CommRing R] (D : CellData R)

/-- Openness lifts `xp(1) xm(ε)` into the actual rank-one cell. -/
theorem exists_dualFactorization :
    ∃ (y : Γ((dualOver R).left, ⊤)) (t : dualOver R ⟶ D.T.X)
      (x : Γ((dualOver R).left, ⊤)),
      D.A 1 * D.B (epsSec R) = D.cellPt y t x := by
  apply (D.inCell_iff _).mp
  apply InCell.of_comp D (surjective_dualZero R)
  rw [MonObj.comp_mul, D.comp_A, D.comp_B, map_one,
    dualZero_appTop_epsSec, D.B_zero, mul_one, D.A_eq_cellPt]
  exact D.inCell_cellPt _ _ _

end CellData

namespace WeylData

variable {R : Type u} [CommRing R] (D : WeylData R)

/-- The supplied unit beta coordinate, viewed in the coefficient ring. -/
def betaUnit : Rˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom D.unitβ.unit

theorem betaUnit_val :
    (D.betaUnit : R) = (Scheme.ΓSpecIso (CommRingCat.of R)).hom D.cβ := by
  simp only [betaUnit, Units.coe_map, IsUnit.unit_spec]
  rfl

/-- The positive coordinate of `xp(1) xm(ε)` has coefficient `-β⁻¹`.
This calculation works over arbitrary rings, including rings with nilpotents. -/
theorem snd_dual_positive [IsAffine D.G.X.left]
    {y : Γ((dualOver R).left, ⊤)} {t : dualOver R ⟶ D.T.X}
    {x : Γ((dualOver R).left, ⊤)}
    (hx : D.A 1 * D.B (epsSec R) = D.cellPt y t x) :
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom x).snd =
      -(↑D.betaUnit⁻¹ : R) := by
  let gam := (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv
  let w : Γ((dualOver R).left, ⊤) :=
    gam (TrivSqZeroExt.inr (↑D.betaUnit⁻¹ : R))
  let u₀ := DualCell.unit (↑D.betaUnit⁻¹ : R)
  let U : Γ((dualOver R).left, ⊤)ˣ := Units.map gam.hom.toMonoidHom u₀
  have hu : (U : Γ((dualOver R).left, ⊤)) = 1 + (1 : Γ((dualOver R).left, ⊤)) * w := by
    change gam (1 + TrivSqZeroExt.inr (↑D.betaUnit⁻¹ : R)) = _
    simp only [map_add, map_one, one_mul, w]
  have heps : pb (dualOver R) D.cβ * w = epsSec R := by
    rw [DualCell.pb_spec, ← D.betaUnit_val]
    change gam (algebraMap R (DualNumber R) (D.betaUnit : R)) *
      gam (TrivSqZeroExt.inr (↑D.betaUnit⁻¹ : R)) = gam DualNumber.eps
    rw [← map_mul, TrivSqZeroExt.algebraMap_eq_inl,
      TrivSqZeroExt.inl_mul_inr, smul_eq_mul, Units.mul_inv]
    rfl
  have hr := D.relation (Z := dualOver R) 1 w U hu
  rw [heps, mul_one] at hr
  have hp := (D.cellPt_inj (hx.symm.trans hr)).2.2
  have hp' := congrArg (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom hp
  change (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom x =
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom (gam (↑u₀⁻¹ : DualNumber R)) at hp'
  rw [Iso.inv_hom_id_apply] at hp'
  rw [hp']
  change (1 - TrivSqZeroExt.inr (↑D.betaUnit⁻¹ : R) : DualNumber R).snd = _
  simp

end WeylData

end RingRootCell

end Langlands.GroupScheme

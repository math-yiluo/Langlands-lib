import Langlands.Shimura.LevelHeckeBasis
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.RingTheory.Noetherian.Basic

/-! # Inversion of the counting-measure level Hecke algebra -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

universe uG uR

namespace Langlands.Shimura.LevelHecke

variable {G : Type uG} [Group G]

private def invertDoubleCoset (K : Subgroup G) :
    DoubleCoset.Quotient (K : Set G) K → DoubleCoset.Quotient (K : Set G) K :=
  Quotient.lift (fun g : G => DoubleCoset.mk K K g⁻¹) (by
    intro a b hab
    obtain ⟨k, hk, l, hl, rfl⟩ := DoubleCoset.rel_iff.mp hab
    exact DoubleCoset.eq.mpr ⟨l⁻¹, K.inv_mem hl, k⁻¹, K.inv_mem hk, by group⟩)

/-- Inversion permutes the double cosets of a subgroup with itself. -/
def doubleCosetInversion (K : Subgroup G) :
    DoubleCoset.Quotient (K : Set G) K ≃ DoubleCoset.Quotient (K : Set G) K :=
  { toFun := invertDoubleCoset K
    invFun := invertDoubleCoset K
    left_inv := by
      intro q
      induction q using Quotient.inductionOn' with
      | h g => change DoubleCoset.mk K K g⁻¹⁻¹ = DoubleCoset.mk K K g; rw [inv_inv]
    right_inv := by
      intro q
      induction q using Quotient.inductionOn' with
      | h g => change DoubleCoset.mk K K g⁻¹⁻¹ = DoubleCoset.mk K K g; rw [inv_inv] }

@[simp] theorem doubleCosetInversion_mk (K : Subgroup G) (g : G) :
    doubleCosetInversion K (DoubleCoset.mk K K g) = DoubleCoset.mk K K g⁻¹ := rfl

variable (R : Type uR) [CommRing R]
  [TopologicalSpace G] [IsTopologicalGroup G] (K : CompactOpenLevel G)

/-- Inversion of double-coset coordinates, as a linear equivalence. -/
def heckeInversion : LevelHeckeAlgebra R K.subgroup ≃ₗ[R]
    LevelHeckeAlgebra R K.subgroup :=
  (heckeAlgebraBasis R K).repr.trans
    ((Finsupp.domLCongr (doubleCosetInversion K.subgroup)).trans
      (heckeAlgebraBasis R K).repr.symm)

private theorem algebraBasis_repr_mk (a : LevelHeckeAlgebra R K.subgroup) (g : G) :
    (heckeAlgebraBasis R K).repr a (DoubleCoset.mk K.subgroup K.subgroup g) =
      a.val (g : G ⧸ K.subgroup) :=
  heckeBasis_repr_mk R K K a g

/-- The inverted function at `gK` has the original value at `g⁻¹K`. -/
theorem heckeInversion_apply (a : LevelHeckeAlgebra R K.subgroup) (g : G) :
    (heckeInversion R K a).val (g : G ⧸ K.subgroup) = a.val ((g⁻¹ : G) : G ⧸ K.subgroup) := by
  rw [← algebraBasis_repr_mk, ← algebraBasis_repr_mk]
  change ((heckeAlgebraBasis R K).repr
    ((heckeAlgebraBasis R K).repr.symm
      (Finsupp.domLCongr (doubleCosetInversion K.subgroup)
        ((heckeAlgebraBasis R K).repr a)))) _ = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

private theorem heckeInversion_apply_out (a : LevelHeckeAlgebra R K.subgroup)
    (q : G ⧸ K.subgroup) :
    (heckeInversion R K a).val q =
      a.val (((Quotient.out q : G)⁻¹ : G) : G ⧸ K.subgroup) := by
  simpa only [Quotient.out_eq'] using heckeInversion_apply R K a (Quotient.out q)

/-- Inversion is involutive. -/
theorem heckeInversion_involutive : Function.Involutive (heckeInversion R K) := by
  intro a
  apply Subtype.ext
  ext q
  induction q using QuotientGroup.induction_on with
  | H g => rw [heckeInversion_apply, heckeInversion_apply, inv_inv]

private theorem finsum_finsupp_mul {X : Type*} (a : X →₀ R) (b : X → R) :
    (∑ᶠ x, a x * b x) = a.sum (fun x r => r * b x) := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro x hx
  apply Finsupp.mem_support_iff.mpr
  intro ha
  exact hx (by change a x * b x = 0; rw [ha, zero_mul])

omit [IsTopologicalGroup G] in
/-- Coset convolution may be summed over all cosets because its first factor is finitely supported. -/
theorem heckeMul_finsum (a b : LevelHeckeAlgebra R K.subgroup) (g : G) :
    (a * b).val (g : G ⧸ K.subgroup) =
      ∑ᶠ q : G ⧸ K.subgroup,
        a.val q * b.val (((Quotient.out q : G)⁻¹ * g : G) : G ⧸ K.subgroup) := by
  rw [finsum_finsupp_mul, LevelHeckeAlgebra.mul_def, heckeMul_apply]
  rfl

/-- Inversion reverses convolution. -/
theorem heckeInversion_mul (a b : LevelHeckeAlgebra R K.subgroup) :
    heckeInversion R K (a * b) = heckeInversion R K b * heckeInversion R K a := by
  apply Subtype.ext
  ext q
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [heckeInversion_apply, heckeMul_finsum, heckeMul_finsum]
    symm
    rw [← finsum_comp_equiv (MulAction.toPerm g : (G ⧸ K.subgroup) ≃ (G ⧸ K.subgroup))]
    symm
    apply finsum_congr
    intro q
    have hout : ((Quotient.out (g • q) : G) : G ⧸ K.subgroup) =
        ((g * (Quotient.out q : G) : G) : G ⧸ K.subgroup) := by
      exact (QuotientGroup.out_eq' (g • q)).trans
        (congrArg (fun z : G ⧸ K.subgroup => g • z) (QuotientGroup.out_eq' q)).symm
    rw [heckeInversion_apply_out, heckeInversion_apply, mul_inv_rev, inv_inv]
    have hleft : a.val ((g⁻¹ * (Quotient.out (g • q) : G) : G) : G ⧸ K.subgroup) =
        a.val q := by
      change a.val (g⁻¹ • (((Quotient.out (g • q) : G) : G ⧸ K.subgroup))) = a.val q
      rw [QuotientGroup.out_eq', inv_smul_smul]
    have hright : b.val (((Quotient.out (g • q) : G)⁻¹ : G) : G ⧸ K.subgroup) =
        b.val (((Quotient.out q : G)⁻¹ * g⁻¹ : G) : G ⧸ K.subgroup) := by
      have hi := congrArg (fun z : G ⧸ K.subgroup =>
        (heckeInversion R K b).val z) hout
      simpa only [heckeInversion_apply, mul_inv_rev] using hi
    change a.val q * b.val (((Quotient.out q : G)⁻¹ * g⁻¹ : G) : G ⧸ K.subgroup) =
      b.val (((Quotient.out (g • q) : G)⁻¹ : G) : G ⧸ K.subgroup) *
        a.val ((g⁻¹ * (Quotient.out (g • q) : G) : G) : G ⧸ K.subgroup)
    rw [hleft, hright, mul_comm]

/-- The published level Hecke algebra is isomorphic to its opposite ring. -/
def heckeOppositeEquiv : LevelHeckeAlgebra R K.subgroup ≃+*
    (LevelHeckeAlgebra R K.subgroup)ᵐᵒᵖ :=
  { (heckeInversion R K).toAddEquiv.trans MulOpposite.opAddEquiv with
    map_mul' a b := congrArg MulOpposite.op (heckeInversion_mul R K a b) }

/-- Left and right Noetherianity of a compact-open level Hecke algebra are equivalent. -/
theorem hecke_isNoetherianRing_op_iff :
    IsNoetherianRing (LevelHeckeAlgebra R K.subgroup)ᵐᵒᵖ ↔
      IsNoetherianRing (LevelHeckeAlgebra R K.subgroup) := by
  constructor
  · intro h
    let _ := h
    exact isNoetherianRing_of_ringEquiv _ (heckeOppositeEquiv R K).symm
  · intro h
    let _ := h
    exact isNoetherianRing_of_ringEquiv _ (heckeOppositeEquiv R K)

end Langlands.Shimura.LevelHecke

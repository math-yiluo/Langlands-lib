import Langlands.Geometry.FormalGroup.HarrisSplitFrameAction

/-! # Group laws for inverse precomposition on the actual split affine points -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v s

open CategoryTheory ValuativeRel

namespace Langlands.PDivisibleGroup

variable {R : CommRingCat.{v}} {p : ℕ} [Fact p.Prime]
variable {A : Type u} [Ring A] {G H : PDivisibleGroup R p}
variable {a : A →+* End G} {b : A →+* End H}

private theorem symm_aut_one (q : OrderQuasiIsogeny a b) :
    (OrderQuasiIsogeny.ofAut (1 : orderAut a)).symm.trans q = q := by
  apply OrderQuasiIsogeny.ext_val
  exact CategoryTheory.Iso.refl_trans q.val

private theorem symm_aut_mul (g h : orderAut a) (q : OrderQuasiIsogeny a b) :
    (OrderQuasiIsogeny.ofAut (g * h)).symm.trans q =
      (OrderQuasiIsogeny.ofAut g).symm.trans ((OrderQuasiIsogeny.ofAut h).symm.trans q) := by
  apply OrderQuasiIsogeny.ext_val
  apply CategoryTheory.Iso.ext
  change RationalHom.comp (RationalHom.comp g.val.asIso.inv h.val.asIso.inv) q.val.hom =
    RationalHom.comp g.val.asIso.inv (RationalHom.comp h.val.asIso.inv q.val.hom)
  exact RationalHom.comp_assoc _ _ _

end Langlands.PDivisibleGroup

namespace Langlands.FormalGroup.Harris.SplitPDivisibleAffinePoint

open LocalDivision GroupScheme.Cartier PDivisibleGroup
open SpecialModule.HeightSquaredModule

attribute [local instance] Langlands.FormalGroup.Harris.splitPointTestAlgebra

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {W : Type v} [CommRing W] [Algebra 𝒪[K] W] {π : 𝒪[K]}
variable {p e : ℕ} [Fact p.Prime] {b : 𝒪[K]ˣ}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) («ι» := ι)
  (R := ResidueRing W (algebraMap 𝒪[K] W π)) π}
variable {hp : (p : 𝒪[K]) = (b : 𝒪[K]) * π ^ e} {he : 0 < e}
variable {T : Nilp.{v, v} W (algebraMap 𝒪[K] W π)}

local notation "red" => specialFibre (π := π) T
local notation "α" => pDivisibleAction Φ hp he
local notation "Point" => SplitPDivisibleAffinePoint (W := W) (π := π) Φ hp he T
local notation "Similitudes" => SplitFrameSimilitudes α

/-- The identity frame similitude acts by the identity. -/
theorem actFrame_one (X : Point) : actFrame 1 X = X := by
  have h₁ : (1 : Similitudes).1 = 1 := rfl
  have h₂ : (1 : Similitudes).2 = 1 := rfl
  have hq : (OrderQuasiIsogeny.ofAut (orderAutBaseChange (S := red) α (1 : Similitudes).1)).symm.trans
      X.primalRigidifier = X.primalRigidifier := by
    rw [h₁, map_one]
    exact symm_aut_one X.primalRigidifier
  have hc : (1 : Similitudes).2⁻¹ * X.multiplier = X.multiplier := by rw [h₂, inv_one, one_mul]
  dsimp only [actFrame]
  have h := congrArg₂ (fun q c => { X with primalRigidifier := q, multiplier := c }) hq hc
  with_reducible exact h

/-- The inverse-precomposition rule is a left action on the actual points. -/
theorem actFrame_mul (g h : Similitudes) (X : Point) :
    actFrame (g * h) X = actFrame g (actFrame h X) := by
  have h₁ : (g * h).1 = g.1 * h.1 := rfl
  have h₂ : (g * h).2 = g.2 * h.2 := rfl
  have hq : (OrderQuasiIsogeny.ofAut (orderAutBaseChange (S := red) α (g * h).1)).symm.trans
        X.primalRigidifier =
      (OrderQuasiIsogeny.ofAut (orderAutBaseChange (S := red) α g.1)).symm.trans
        ((OrderQuasiIsogeny.ofAut (orderAutBaseChange (S := red) α h.1)).symm.trans X.primalRigidifier) := by
    rw [h₁, map_mul]
    exact symm_aut_mul (orderAutBaseChange (S := red) α g.1)
      (orderAutBaseChange (S := red) α h.1) X.primalRigidifier
  have hc : (g * h).2⁻¹ * X.multiplier = g.2⁻¹ * (h.2⁻¹ * X.multiplier) := by
    rw [h₂, mul_inv_rev, mul_comm h.2⁻¹ g.2⁻¹, mul_assoc]
  dsimp only [actFrame]
  have h' := congrArg₂ (fun q c => { X with primalRigidifier := q, multiplier := c }) hq hc
  with_reducible exact h'

/-- Frame similitudes act on the actual split affine point data. -/
@[instance_reducible]
def pointFrameAction : MulAction Similitudes Point where
  smul := actFrame
  one_smul := actFrame_one
  mul_smul := actFrame_mul

end Langlands.FormalGroup.Harris.SplitPDivisibleAffinePoint

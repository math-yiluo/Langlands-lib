import Langlands.GroupScheme.IntegralModel.CongruenceLieTruncation
import Langlands.GroupScheme.IntegralModel.CongruenceLieUnramified

/-! # Unramified scalar extension of the Lie quotient with two models -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.LocalGalois.Separable Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.GroupScheme.IntegralModel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local notation "K" => inertiaFixedField F
local notation "A" => fixedFieldIntegers F

private local instance : Algebra ↥𝒪[F] A :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

private local instance : IsScalarTower ↥𝒪[F] A K :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsAffineHom (baseChanged F K G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (baseMap F K))
  infer_instance

/-- Extension of generic tangents preserves each scaled Lie lattice of the model. -/
theorem baseChangeUnramified_mem_lieLatticeAt (M : IntegralModel ↥𝒪[F] F G)
    (n : ℕ+) {X : GenericLie ↥𝒪[F] G} (hX : X ∈ M.lieLatticeAt n) :
    GenericLie.baseChange ↥𝒪[F] A G X ∈ M.baseChangeUnramified.lieLatticeAt n := by
  let : IsLocalHom (algebraMap ↥𝒪[F] A) := integerToFixedField_isLocalHom F
  have hpow : (IsLocalRing.maximalIdeal ↥𝒪[F] ^ (n : ℕ)).map (algebraMap ↥𝒪[F] A) ≤
      IsLocalRing.maximalIdeal A ^ (n : ℕ) := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' (IsLocalRing.map_maximalIdeal_le _) _
  have h : M.lieLatticeAt n ≤
      (M.baseChangeUnramified.lieLatticeAt n).comap (GenericLie.baseChange ↥𝒪[F] A G) := by
    refine Submodule.smul_le.mpr ?_
    intro a ha Y hY
    change GenericLie.baseChange ↥𝒪[F] A G (a • Y) ∈ M.baseChangeUnramified.lieLatticeAt n
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem_smul (hpow (Ideal.mem_map_of_mem _ ha))
      (M.baseChange_mem_lieLattice hY)
  exact h hX

/-- The semilinear tangent extension on the quotient by a second model's level-`n` lattice. -/
def unramifiedTruncatedCongruenceLieQuotientMap (N M : IntegralModel ↥𝒪[F] F G) (n : ℕ+) :
    N.truncatedCongruenceLieQuotient M n →ₛₗ[algebraMap ↥𝒪[F] A]
      N.baseChangeUnramified.truncatedCongruenceLieQuotient M.baseChangeUnramified n :=
  (Submodule.comap (N.lieLatticeAt n).subtype (M.lieLatticeAt n)).mapQ _
    (LinearMap.codRestrict _ ((GenericLie.baseChange ↥𝒪[F] A G).comp (N.lieLatticeAt n).subtype)
      (fun X => N.baseChangeUnramified_mem_lieLatticeAt n X.property))
    (fun _ hX => M.baseChangeUnramified_mem_lieLatticeAt n hX)

/-- The map sends the class of a tangent vector in the level-`n` lattice of `N` to the
class of its generic scalar extension. -/
@[simp] theorem unramifiedTruncatedCongruenceLieQuotientMap_mk (N M : IntegralModel ↥𝒪[F] F G)
    (n : ℕ+) (X : N.lieLatticeAt n) :
    N.unramifiedTruncatedCongruenceLieQuotientMap M n (Submodule.Quotient.mk X) =
      Submodule.Quotient.mk ⟨GenericLie.baseChange ↥𝒪[F] A G X,
        N.baseChangeUnramified_mem_lieLatticeAt n X.property⟩ := rfl

end Langlands.GroupScheme.IntegralModel

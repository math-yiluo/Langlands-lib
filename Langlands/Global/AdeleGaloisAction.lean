import Langlands.Global.NumberFieldAdeleModuleTopology
import Langlands.Global.IdeleNormAbsoluteValue

/-! # The Galois action on the adeles of a Galois extension -/

noncomputable section

universe u

open NumberField
open scoped TensorProduct NNReal

namespace Langlands.Global.AdeleGalois

open AdelicFunctoriality

variable (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]

/-- The ring automorphism of `𝔸_L` induced by `σ ⊗ 1` on `L ⊗_F 𝔸_F`. -/
def ringEquiv (σ : L ≃ₐ[F] L) : Adeles L ≃+* Adeles L :=
  (numberFieldAdeleTensorEquiv F L).toRingEquiv.symm.trans
    ((Algebra.TensorProduct.congr σ (AlgEquiv.refl : Adeles F ≃ₐ[F] Adeles F)).toRingEquiv.trans
      (numberFieldAdeleTensorEquiv F L).toRingEquiv)

variable {F L}

theorem ringEquiv_tensor (σ : L ≃ₐ[F] L) (a : L) (x : Adeles F) :
    ringEquiv F L σ (numberFieldAdeleTensorEquiv F L (a ⊗ₜ[F] x)) =
      numberFieldAdeleTensorEquiv F L (σ a ⊗ₜ[F] x) := by
  change numberFieldAdeleTensorEquiv F L
      (Algebra.TensorProduct.congr σ (AlgEquiv.refl : Adeles F ≃ₐ[F] Adeles F)
        ((numberFieldAdeleTensorEquiv F L).symm
          (numberFieldAdeleTensorEquiv F L (a ⊗ₜ[F] x)))) = _
  rw [AlgEquiv.symm_apply_apply]
  rfl

/-- The automorphism is `σ`-semilinear on principal adeles. -/
@[simp] theorem ringEquiv_algebraMap (σ : L ≃ₐ[F] L) (a : L) :
    ringEquiv F L σ (algebraMap L (Adeles L) a) = algebraMap L (Adeles L) (σ a) := by
  have h (b : L) : algebraMap L (Adeles L) b = numberFieldAdeleTensorEquiv F L (b ⊗ₜ[F] 1) := by
    rw [numberFieldAdeleTensorEquiv_tmul, map_one, mul_one]
  rw [h, ringEquiv_tensor, h]

/-- The automorphism fixes the adeles of the ground field. -/
@[simp] theorem ringEquiv_adeleInclusion (σ : L ≃ₐ[F] L) (x : Adeles F) :
    ringEquiv F L σ (adeleInclusion x) = adeleInclusion x := by
  have h (y : Adeles F) : adeleInclusion (L := L) y =
      numberFieldAdeleTensorEquiv F L ((1 : L) ⊗ₜ[F] y) := by
    rw [numberFieldAdeleTensorEquiv_tmul, map_one, one_mul]
  rw [h, ringEquiv_tensor, map_one]

/-- In tensor coordinates for a field basis, the automorphism moves only the basis. -/
theorem ringEquiv_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F L)
    (σ : L ≃ₐ[F] L) (y : Adeles L) :
    ringEquiv F L σ y =
      ∑ i, algebraMap L (Adeles L) (σ (b i)) * adeleInclusion (adeleBasisEquiv F L b y i) := by
  conv_lhs => rw [← (adeleBasisEquiv F L b).symm_apply_apply y, adeleBasisEquiv_symm_apply]
  simp only [map_sum, map_mul, ringEquiv_algebraMap, ringEquiv_adeleInclusion]

theorem continuous_ringEquiv (σ : L ≃ₐ[F] L) : Continuous (ringEquiv F L σ) := by
  classical
  let b := Module.finBasis F L
  have heq : (ringEquiv F L σ : Adeles L → Adeles L) = fun y =>
      ∑ i, algebraMap L (Adeles L) (σ (b i)) * adeleInclusion (adeleBasisEquiv F L b y i) :=
    funext fun y => ringEquiv_eq_sum b σ y
  rw [heq]
  exact continuous_finsetSum _ fun i _ => continuous_const.mul
    (continuous_adeleInclusion.comp ((continuous_apply i).comp (continuous_adeleBasisEquiv F L b)))

/-- The automorphism of the idele group. -/
def idelesMap (σ : L ≃ₐ[F] L) : Ideles L →ₜ* Ideles L where
  toMonoidHom := Units.map (ringEquiv F L σ).toRingHom.toMonoidHom
  continuous_toFun := (continuous_ringEquiv σ).units_map _

@[simp] theorem idelesMap_val (σ : L ≃ₐ[F] L) (x : Ideles L) :
    (idelesMap σ x : Adeles L) = ringEquiv F L σ x := rfl

omit [NumberField F] [NumberField L] in
/-- Embedding a real number at the infinite places commutes with the adele inclusion. -/
theorem infiniteAdeleMap_infiniteRealEmbedding (t : ℝ) :
    infiniteAdeleMap (algebraMap F L) (PositiveRealIdeles.infiniteRealEmbedding F t) =
      PositiveRealIdeles.infiniteRealEmbedding L t := by
  have h := Rat.denseRange_cast.equalizer
    ((continuous_infiniteAdeleMap (algebraMap F L)).comp
      (PositiveRealIdeles.continuous_infiniteRealEmbedding F))
    (PositiveRealIdeles.continuous_infiniteRealEmbedding L) (by
      funext q
      change infiniteAdeleMap (algebraMap F L)
        (PositiveRealIdeles.infiniteRealEmbedding F (q : ℝ)) =
          PositiveRealIdeles.infiniteRealEmbedding L (q : ℝ)
      rw [infiniteRealEmbedding_ratCast, infiniteRealEmbedding_ratCast,
        infiniteAdeleMap_diagonal, map_ratCast])
  exact congrFun h t

/-- Positive real ideles of `L` come from the ground field. -/
theorem adeleInclusion_positiveReal (a : ℝ≥0ˣ) :
    adeleInclusion ((PositiveRealIdeles.full F a : Ideles F) : Adeles F) =
      ((PositiveRealIdeles.full L a : Ideles L) : Adeles L) := by
  apply Prod.ext
  · exact infiniteAdeleMap_infiniteRealEmbedding _
  · exact map_one finiteAdeleInclusion

/-- The Galois automorphism preserves the normalized idelic norm. -/
theorem full_idelesMap (σ : L ≃ₐ[F] L) (x : Ideles L) :
    IdeleAbsoluteValue.full L (idelesMap σ x) = IdeleAbsoluteValue.full L x := by
  have heq : (IdeleAbsoluteValue.full L).comp (idelesMap σ) = IdeleAbsoluteValue.full L := by
    apply IdeleAbsoluteValue.eq_of_positiveRealIdeles
    · intro a
      have hd : idelesMap σ (diagonalUnits L a) = diagonalUnits L (Units.map σ.toRingEquiv.toRingHom.toMonoidHom a) := by
        apply Units.ext
        exact ringEquiv_algebraMap σ (a : L)
      change IdeleAbsoluteValue.full L (idelesMap σ (diagonalUnits L a)) = 1
      rw [hd, IdeleAbsoluteValue.full_diagonalUnits]
    · intro a
      have hp : idelesMap σ (PositiveRealIdeles.full L a) = PositiveRealIdeles.full L a := by
        apply Units.ext
        rw [idelesMap_val, ← adeleInclusion_positiveReal (F := F), ringEquiv_adeleInclusion]
      change IdeleAbsoluteValue.full L (idelesMap σ (PositiveRealIdeles.full L a)) = _
      rw [hp]
  exact DFunLike.congr_fun heq x

end Langlands.Global.AdeleGalois

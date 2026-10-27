import Langlands.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement
import Langlands.Group.GL.Mirabolic

/-!
# Unequal-rank mirabolic-versus-general-linear covariant bilinear forms

For `n < r`, the actual block embedding `g ↦ diag(g, I_(r-n))` lands in the
mirabolic subgroup of `GL_(r+1)`, and the actual JPSS group `U_(n+2,r+1)`
lifts canonically into the same subgroup. For arbitrary complex
representations of the mirabolic group and of `GL_(n+1)`, this module builds
the submodule of bilinear forms satisfying the two covariance laws of JPSS
(2.11.2) and (2.11.4), and compares it with the published coefficient-model
predicate. It does not prove the irreducible lemma on p.399 of JPSS.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW

variable {F : Type uF} [Field F] {n r : ℕ}

/-- The block matrix `diag(g, I_(r-n))`, reindexed to rank `r+1`, has last row
`(0, …, 0, 1)` because its last index lies in the identity block. -/
theorem unequalRankBlock_mem_mirabolic (hnr : n < r)
    (g : Langlands.GeneralLinear (n + 1) F) :
    GeneralLinear.reindex (finCongr (show n + (r - n) + 1 = r + 1 by omega))
        (appendIdentity n (r - n) g) ∈ mirabolic r F := by
  rw [mem_mirabolic]
  intro j
  change appendIdentity n (r - n) g
      ((finCongr (show n + (r - n) + 1 = r + 1 by omega)).symm (Fin.last r))
      ((finCongr (show n + (r - n) + 1 = r + 1 by omega)).symm j) = _
  rw [appendIdentity_entry]
  have hlast : ¬ ((finCongr (show n + (r - n) + 1 = r + 1 by omega)).symm
      (Fin.last r)).val < n + 1 := by
    simp only [finCongr_symm, finCongr_apply, Fin.val_cast, Fin.val_last]
    omega
  simp only [hlast, ↓reduceDIte, EmbeddingLike.apply_eq_iff_eq]
  exact if_congr eq_comm rfl rfl

/-- The actual embedding `GL_(n+1) → P_(r+1)`, `g ↦ diag(g, I_(r-n))`, obtained
from the shared block embedding `appendIdentity`. -/
def unequalRankEmbedding (hnr : n < r) :
    Langlands.GeneralLinear (n + 1) F →* mirabolic r F :=
  ((GeneralLinear.reindex
      (finCongr (show n + (r - n) + 1 = r + 1 by omega))).toMonoidHom.comp
      (appendIdentity n (r - n))).codRestrict (mirabolic r F)
    (unequalRankBlock_mem_mirabolic hnr)

/-- The underlying ambient matrix of `unequalRankEmbedding` is exactly the
expression used in `IsUnequalRankBilinearCovariant`. -/
@[simp] theorem unequalRankEmbedding_val (hnr : n < r)
    (g : Langlands.GeneralLinear (n + 1) F) :
    ((unequalRankEmbedding hnr g : mirabolic r F) :
        Langlands.GeneralLinear (r + 1) F) =
      GeneralLinear.reindex (finCongr (show n + (r - n) + 1 = r + 1 by omega))
        (appendIdentity n (r - n) g) :=
  rfl

/-- Entrywise, `unequalRankEmbedding hnr g` is `diag(g, I_(r-n))`. -/
theorem unequalRankEmbedding_entry (hnr : n < r)
    (g : Langlands.GeneralLinear (n + 1) F) (i j : Fin (r + 1)) :
    ((unequalRankEmbedding hnr g : mirabolic r F) :
        Langlands.GeneralLinear (r + 1) F) i j =
      if hi : i.val < n + 1 then
        if hj : j.val < n + 1 then g ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
      else if i = j then 1 else 0 := by
  change appendIdentity n (r - n) g
      ((finCongr (show n + (r - n) + 1 = r + 1 by omega)).symm i)
      ((finCongr (show n + (r - n) + 1 = r + 1 by omega)).symm j) = _
  rw [appendIdentity_entry]
  simp only [finCongr_symm, finCongr_apply, Fin.val_cast, Fin.cast_inj]

/-- The canonical lift of the actual upper unipotent group of `GL_(r+1)` into
the mirabolic subgroup, through `upperUnipotent_le_mirabolic`. -/
def unequalRankUnipotentLift :
    GeneralLinear.upperUnipotent (r + 1) F →* mirabolic r F :=
  Subgroup.inclusion upperUnipotent_le_mirabolic

@[simp] theorem unequalRankUnipotentLift_val
    (u : GeneralLinear.upperUnipotent (r + 1) F) :
    ((unequalRankUnipotentLift u : mirabolic r F) :
        Langlands.GeneralLinear (r + 1) F) = u.val :=
  rfl

/-- Left multiplication by an element of `U_(n+2,r+1)` does not change the
leading `(n+2)`-square block of an upper unipotent matrix. -/
private theorem covarianceUnipotent_mul_entry
    {u : GeneralLinear.upperUnipotent (r + 1) F}
    (hu : IsUnequalRankCovarianceUnipotent n u)
    (v : GeneralLinear.upperUnipotent (r + 1) F) {i j : Fin (r + 1)}
    (hi : i.val < n + 2) (hj : j.val < n + 2) :
    (u * v).val i j = v.val i j := by
  change (u.val.val * v.val.val) i j = v.val.val i j
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hu i i hi hi]
    simp
  · intro k _ hki
    by_cases hk : k.val < n + 2
    · rw [hu i k hi hk]
      simp [Ne.symm hki]
    · rw [UpperUnipotent.entry_eq_zero v
        (show j < k by rw [Fin.lt_def]; omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The actual JPSS group `U_(n+2,r+1)` as a subgroup of the upper unipotent
group of `GL_(r+1)`: its leading `(n+2)`-square block is the identity. -/
def unequalRankCovarianceSubgroup (n r : ℕ) (F : Type uF) [Field F] :
    Subgroup (GeneralLinear.upperUnipotent (r + 1) F) where
  carrier := {u | IsUnequalRankCovarianceUnipotent n u}
  one_mem' := by
    intro i j _ _
    rfl
  mul_mem' := by
    intro u v hu hv i j hi hj
    rw [covarianceUnipotent_mul_entry hu v hi hj, hv i j hi hj]
  inv_mem' := by
    intro u hu i j hi hj
    have h := covarianceUnipotent_mul_entry hu u⁻¹ hi hj
    rw [mul_inv_cancel] at h
    rw [← h]
    rfl

@[simp] theorem mem_unequalRankCovarianceSubgroup
    (u : GeneralLinear.upperUnipotent (r + 1) F) :
    u ∈ unequalRankCovarianceSubgroup n r F ↔
      IsUnequalRankCovarianceUnipotent n u :=
  Iff.rfl

/-- At adjacent ranks `r = n + 1` the group `U_(n+2,r+1)` is trivial. -/
theorem unequalRankCovarianceSubgroup_adjacent (n : ℕ) (F : Type uF) [Field F] :
    unequalRankCovarianceSubgroup n (n + 1) F = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact hu i j (by have := i.isLt; omega) (by have := j.isLt; omega)

section FixedData

variable [TopologicalSpace F]
  {V : Type uV} [AddCommMonoid V] [Module ℂ V]
  {W : Type uW} [AddCommMonoid W] [Module ℂ W]

/-- The two covariance laws of JPSS (2.11.2) and (2.11.4) for a bilinear form
between a representation `ξ` of the mirabolic subgroup of `GL_(r+1)` and a
representation `η` of `GL_(n+1)`. The parameter `s` is the integral parameter;
the source's twisted-pairing parameter is `s - (r-n)/2`. -/
def IsUnequalRankMirabolicCovariant (hnr : n < r)
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (ξ : Representation ℂ (mirabolic r F) V)
    (η : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (s : ℂ) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) : Prop :=
  (∀ (g : Langlands.GeneralLinear (n + 1) F) (v : V) (w : W),
      B (ξ (unequalRankEmbedding hnr g) v) (η g w) =
        determinantWeight abv g (((r - n : ℕ) : ℂ) / 2 - s) * B v w) ∧
  (∀ u : GeneralLinear.upperUnipotent (r + 1) F,
    IsUnequalRankCovarianceUnipotent n u →
    ∀ (v : V) (w : W),
      B (ξ (unequalRankUnipotentLift u) v) w =
        (standardCharacter ψ r u : ℂ) * B v w)

/-- The actual space of bilinear forms satisfying both unequal-rank
covariance laws. -/
def unequalRankMirabolicForms (hnr : n < r)
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (ξ : Representation ℂ (mirabolic r F) V)
    (η : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (s : ℂ) : Submodule ℂ (V →ₗ[ℂ] W →ₗ[ℂ] ℂ) where
  carrier := {B | IsUnequalRankMirabolicCovariant hnr ψ abv ξ η s B}
  zero_mem' := by
    refine ⟨fun g v w => ?_, fun u _ v w => ?_⟩ <;> simp
  add_mem' := by
    rintro B C ⟨hB, hB'⟩ ⟨hC, hC'⟩
    refine ⟨fun g v w => ?_, fun u hu v w => ?_⟩
    · change B (ξ (unequalRankEmbedding hnr g) v) (η g w) +
          C (ξ (unequalRankEmbedding hnr g) v) (η g w) =
        determinantWeight abv g (((r - n : ℕ) : ℂ) / 2 - s) * (B v w + C v w)
      rw [hB, hC, mul_add]
    · change B (ξ (unequalRankUnipotentLift u) v) w +
          C (ξ (unequalRankUnipotentLift u) v) w =
        (standardCharacter ψ r u : ℂ) * (B v w + C v w)
      rw [hB' u hu, hC' u hu, mul_add]
  smul_mem' := by
    rintro a B ⟨hB, hB'⟩
    refine ⟨fun g v w => ?_, fun u hu v w => ?_⟩
    · change a * B (ξ (unequalRankEmbedding hnr g) v) (η g w) =
        determinantWeight abv g (((r - n : ℕ) : ℂ) / 2 - s) * (a * B v w)
      rw [hB, mul_left_comm]
    · change a * B (ξ (unequalRankUnipotentLift u) v) w =
        (standardCharacter ψ r u : ℂ) * (a * B v w)
      rw [hB' u hu, mul_left_comm]

theorem mem_unequalRankMirabolicForms (hnr : n < r)
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (ξ : Representation ℂ (mirabolic r F) V)
    (η : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (s : ℂ) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) :
    B ∈ unequalRankMirabolicForms hnr ψ abv ξ η s ↔
      IsUnequalRankMirabolicCovariant hnr ψ abv ξ η s B :=
  Iff.rfl

end FixedData

section CoefficientModels

variable [TopologicalSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- On actual coefficient models, with the first model restricted to the
mirabolic subgroup, the new predicate is the published
`IsUnequalRankBilinearCovariant`. -/
theorem isUnequalRankMirabolicCovariant_restrict_iff (hnr : n < r)
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ) (s : ℂ)
    (B : (coefficientModel π ℓ).toSubmodule →ₗ[ℂ]
      (coefficientModel σ ℓ').toSubmodule →ₗ[ℂ] ℂ) :
    IsUnequalRankMirabolicCovariant hnr ψ abv
        ((modelRepresentation π ℓ).comp (mirabolic r F).subtype)
        (modelRepresentation σ ℓ') s B ↔
      IsUnequalRankBilinearCovariant hnr ψ abv π σ ℓ ℓ' s B :=
  Iff.rfl

/-- Membership form of `isUnequalRankMirabolicCovariant_restrict_iff`. -/
theorem mem_unequalRankMirabolicForms_restrict_iff (hnr : n < r)
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ) (s : ℂ)
    (B : (coefficientModel π ℓ).toSubmodule →ₗ[ℂ]
      (coefficientModel σ ℓ').toSubmodule →ₗ[ℂ] ℂ) :
    B ∈ unequalRankMirabolicForms hnr ψ abv
        ((modelRepresentation π ℓ).comp (mirabolic r F).subtype)
        (modelRepresentation σ ℓ') s ↔
      IsUnequalRankBilinearCovariant hnr ψ abv π σ ℓ ℓ' s B :=
  Iff.rfl

end CoefficientModels

end Langlands.RankinSelberg

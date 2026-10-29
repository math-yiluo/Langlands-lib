import Langlands.Representation.Parabolic.RefinedOppositeJacquetTensor
import Langlands.Representation.Parabolic.RefinedInductionTensorNormalization

/-! Upper normalized refined Jacquet modules of finite external tensor products. -/

noncomputable section

namespace Langlands.RefinedJacquetTensor

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- Every upper refined quotient class has an ambient representative. -/
theorem refinedJacquetMk_surjective {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    Function.Surjective (refinedJacquetMk B S ρ) :=
  Jacquet.mk_surjective ρ (refinedUnipotent F.Carrier B S)

/-- An equivalence of the coarse Levi representations descends to their upper
normalized refined Jacquet modules. -/
def normalizedRefinedJacquetCongr {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W} (e : ρ.Equiv τ) :
    (T.normalizedRefinedJacquet B S ρ).Equiv (T.normalizedRefinedJacquet B S τ) :=
  Representation.Equiv.mk
    (LinearEquiv.ofLinearMap
      (T.normalizedRefinedJacquetMap B S e.toIntertwiningMap).toLinearMap
      (T.normalizedRefinedJacquetMap B S e.symm.toIntertwiningMap).toLinearMap
      (by
        apply LinearMap.ext
        intro x
        obtain ⟨w, rfl⟩ := refinedJacquetMk_surjective B S τ x
        change refinedJacquetMk B S τ (e (e.symm w)) = refinedJacquetMk B S τ w
        rw [Representation.Equiv.apply_symm_apply])
      (by
        apply LinearMap.ext
        intro x
        obtain ⟨v, rfl⟩ := refinedJacquetMk_surjective B S ρ x
        change refinedJacquetMk B S ρ (e.symm (e v)) = refinedJacquetMk B S ρ v
        rw [Representation.Equiv.symm_apply_apply]))
    (T.normalizedRefinedJacquetMap B S e.toIntertwiningMap).isIntertwining'

@[simp]
theorem normalizedRefinedJacquetCongr_mk {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W} (e : ρ.Equiv τ) (v : V) :
    normalizedRefinedJacquetCongr T B S e (refinedJacquetMk B S ρ v) =
      refinedJacquetMk B S τ (e v) := rfl

/-- The inverse half of the product modulus is the product of inverse block halves. -/
theorem refinedLeviInverseHalfModulus_eq_prod (m : refinedLevi F.Carrier B S) :
    T.refinedLeviInverseHalfModulus B S m =
      ∏ i, (T.leviHalfModulus (S i)
        (PadicField.TopologicalData.refinedLeviBlock B S i m))⁻¹ := by
  change (T.refinedLeviHalfModulus B S m)⁻¹ = _
  rw [T.refinedLeviHalfModulus_eq_prod, Finset.prod_inv_distrib]

variable (A : ∀ i, Rep.{uV} ℂ (GeneralLinear (B.size i) F.Carrier))

/-- Product-subgroup coinvariants, transported to the actual parabolic Jacquet
carriers of the upper factor modules. -/
def refinedCoinvariantsEquiv :
    RefinedJacquetModule B S (FiniteTensor.external fun i => (A i).ρ) ≃ₗ[ℂ]
      PiTensorProduct ℂ (fun i => (S i).JacquetModule (A i).ρ) :=
  (RefinedOppositeJacquetTensor.coinvariantsEquiv (fun i => (A i).ρ)
      (fun i => (S i).unipotentSubgroup F.Carrier)).trans
    (PiTensorProduct.congr fun i => ((S i).jacquetModuleEquiv (A i).ρ).symm)

@[simp]
theorem refinedCoinvariantsEquiv_mk_tprod (v : ∀ i, A i) :
    refinedCoinvariantsEquiv B S A
        (refinedJacquetMk B S _ (PiTensorProduct.tprod ℂ v)) =
      PiTensorProduct.tprod ℂ (fun i => (S i).jacquetMk (A i).ρ (v i)) := by
  change PiTensorProduct.congr _
      (RefinedOppositeJacquetTensor.coinvariantsEquiv _ _
        (Jacquet.mk _ _ (PiTensorProduct.tprod ℂ v))) = _
  rw [RefinedOppositeJacquetTensor.coinvariantsEquiv_mk_tprod,
    PiTensorProduct.congr_tprod]
  simp_rw [← BlockShape.jacquetModuleEquiv_mk, LinearEquiv.symm_apply_apply]

theorem refinedCoinvariantsEquiv_comm (m : refinedLevi F.Carrier B S) (v : ∀ i, A i) :
    refinedCoinvariantsEquiv B S A
        (T.normalizedRefinedJacquet B S (FiniteTensor.external fun i => (A i).ρ) m
          (refinedJacquetMk B S _ (PiTensorProduct.tprod ℂ v))) =
      FiniteTensor.external (fun i => T.normalizedJacquet (S i) (A i).ρ)
          ((refinedLeviEquiv F.Carrier B S).symm m)
        (refinedCoinvariantsEquiv B S A
          (refinedJacquetMk B S _ (PiTensorProduct.tprod ℂ v))) := by
  rw [T.normalizedRefinedJacquet_mk, FiniteTensor.external_tprod, map_smul,
    refinedCoinvariantsEquiv_mk_tprod, refinedCoinvariantsEquiv_mk_tprod,
    FiniteTensor.external_tprod]
  simp_rw [T.normalizedJacquet_mk_eq_inv_halfModulus, Units.smul_def]
  rw [MultilinearMap.map_smul_univ, refinedLeviInverseHalfModulus_eq_prod T B S m,
    Units.coe_prod]
  simp_rw [RefinedOppositeJacquetTensor.leviEmbedding_refinedLeviEquiv_symm]
  rfl

set_option maxHeartbeats 800000 in
/-- The actual upper normalized refined Jacquet module of a finite external tensor
is the external tensor of the actual upper normalized Jacquet factor modules. -/
def jacquetEquiv :
    Representation.Equiv
      (T.normalizedRefinedJacquet B S (FiniteTensor.external fun i => (A i).ρ))
      ((FiniteTensor.external fun i => T.normalizedJacquet (S i) (A i).ρ).comp
        (refinedLeviEquiv F.Carrier B S).symm.toMonoidHom) :=
  Representation.Equiv.mk (refinedCoinvariantsEquiv B S A) (fun m => by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := refinedJacquetMk_surjective B S _ x
    induction y using PiTensorProduct.induction_on with
    | smul_tprod a v =>
      simp only [LinearMap.comp_apply, map_smul]
      exact congrArg (a • ·) (refinedCoinvariantsEquiv_comm T B S A m v)
    | add x y hx hy =>
      simp only [LinearMap.comp_apply, map_add] at hx hy ⊢
      rw [hx, hy])

@[simp]
theorem jacquetEquiv_mk_tprod (v : ∀ i, A i) :
    jacquetEquiv T B S A (refinedJacquetMk B S _ (PiTensorProduct.tprod ℂ v)) =
      PiTensorProduct.tprod ℂ (fun i => (S i).jacquetMk (A i).ρ (v i)) :=
  refinedCoinvariantsEquiv_mk_tprod B S A v

end Langlands.RefinedJacquetTensor

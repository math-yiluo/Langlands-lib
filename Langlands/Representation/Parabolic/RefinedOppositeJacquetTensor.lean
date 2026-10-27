import Langlands.Representation.Parabolic.OppositeJacquetMap
import Langlands.Representation.Parabolic.OppositeRefinementFunctors
import Langlands.Representation.Tensor.CharacterLocalization

/-! The normalized refined opposite Jacquet module of a finite external tensor product. -/

noncomputable section

namespace Langlands.RefinedOppositeJacquetTensor

open GeneralLinear Geometric
open scoped NNReal

universe uR uI uG uV uF

section Coinvariants

variable {R : Type uR} [CommRing R] {ι : Type uI} [Fintype ι]
  {H : ι → Type uG} [∀ i, Group (H i)]
  {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- The product of trivial characters is trivial. -/
theorem productCharacter_one (U : ∀ i, Subgroup (H i)) :
    FiniteTensor.productCharacter (R := R) U (fun _ => 1) = 1 := by
  ext u
  simp

/-- Untwisted coinvariants of a finite external tensor product by a product subgroup
are the tensor product of the factor coinvariants. -/
def coinvariantsEquiv (ρ : ∀ i, Representation R (H i) (V i)) (U : ∀ i, Subgroup (H i)) :
    Jacquet.Coinvariants (FiniteTensor.external ρ) (Subgroup.pi Set.univ U) ≃ₗ[R]
      PiTensorProduct R (fun i => Jacquet.Coinvariants (ρ i) (U i)) :=
  ((Submodule.quotEquivOfEq (Jacquet.relations (FiniteTensor.external ρ) (Subgroup.pi Set.univ U))
      (Jacquet.Localization.relations (FiniteTensor.external ρ) (Subgroup.pi Set.univ U)
        (FiniteTensor.productCharacter U (fun _ => 1)))
      (by rw [productCharacter_one, Jacquet.Localization.relations_one])).trans
    (FiniteTensor.characterLocalizationEquiv ρ U (fun _ => 1))).trans
    (PiTensorProduct.congr fun i =>
      Submodule.quotEquivOfEq _ _ (Jacquet.Localization.relations_one (ρ i) (U i)))

@[simp]
theorem coinvariantsEquiv_mk_tprod (ρ : ∀ i, Representation R (H i) (V i))
    (U : ∀ i, Subgroup (H i)) (v : ∀ i, V i) :
    coinvariantsEquiv ρ U (Jacquet.mk (FiniteTensor.external ρ) (Subgroup.pi Set.univ U)
        (PiTensorProduct.tprod R v)) =
      PiTensorProduct.tprod R (fun i => Jacquet.mk (ρ i) (U i) (v i)) := by
  change PiTensorProduct.congr
      (fun i => Submodule.quotEquivOfEq _ _ (Jacquet.Localization.relations_one (ρ i) (U i)))
      (FiniteTensor.characterLocalizationEquiv ρ U (fun _ => 1)
        (Jacquet.Localization.mk (FiniteTensor.external ρ) (Subgroup.pi Set.univ U)
          (FiniteTensor.productCharacter U (fun _ => 1)) (PiTensorProduct.tprod R v))) = _
  rw [FiniteTensor.characterLocalizationEquiv_mk_tprod, PiTensorProduct.congr_tprod]
  rfl

end Coinvariants

section Opposite

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}

/-- The general-linear opposite Jacquet action on a quotient class: the positive half
of the upper modulus times the class of the block-diagonal action. -/
theorem oppositeJacquet_mk (C : BlockShape n) (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (x : C.Levi F.Carrier) (w : A) :
    (CuspidalJacquetMultiplicity.oppositeJacquet T C A).ρ x (PadicField.TopologicalData.oppositeJacquetMk T C A w) =
      ((NNReal.sqrt (T.leviModulus C x : ℝ≥0) : ℝ) : ℂ) •
        PadicField.TopologicalData.oppositeJacquetMk T C A (A.ρ (C.leviEmbedding F.Carrier x) w) := by
  change Jacquet.normalizedActionOfModulus A.ρ _ _ _ _ (C.leviEquiv F.Carrier x)
      (Jacquet.mk A.ρ (C.oppositeUnipotentSubgroup F.Carrier) w) = _
  rw [Jacquet.normalizedActionOfModulus_mk]
  simp only [MonoidHom.inv_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, Units.val_inv_eq_inv_val, NNReal.sqrt_inv, NNReal.coe_inv,
    Complex.ofReal_inv, inv_inv]
  rfl

variable (B : BlockShape n) (S : BlockRefinement B)

/-- An equivalence of representations of the coarse Levi descends to an equivalence of
their normalized refined opposite Jacquet modules. -/
def normalizedRefinedOppositeJacquetCongr {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W} (e : ρ.Equiv τ) :
    (T.normalizedRefinedOppositeJacquet B S ρ).Equiv
      (T.normalizedRefinedOppositeJacquet B S τ) :=
  Representation.Equiv.mk
    (LinearEquiv.ofLinearMap
      (T.normalizedRefinedOppositeJacquetMap B S e.toIntertwiningMap).toLinearMap
      (T.normalizedRefinedOppositeJacquetMap B S e.symm.toIntertwiningMap).toLinearMap
      (by
        apply LinearMap.ext
        intro x
        obtain ⟨w, rfl⟩ := refinedOppositeJacquetMk_surjective B S τ x
        simp only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply,
          PadicField.TopologicalData.normalizedRefinedOppositeJacquetMap_mk,
          Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.apply_symm_apply,
          LinearMap.id_apply])
      (by
        apply LinearMap.ext
        intro x
        obtain ⟨v, rfl⟩ := refinedOppositeJacquetMk_surjective B S ρ x
        simp only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply,
          PadicField.TopologicalData.normalizedRefinedOppositeJacquetMap_mk,
          Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.symm_apply_apply,
          LinearMap.id_apply]))
    (T.normalizedRefinedOppositeJacquetMap B S e.toIntertwiningMap).isIntertwining'

@[simp]
theorem normalizedRefinedOppositeJacquetCongr_mk {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W} (e : ρ.Equiv τ) (v : V) :
    normalizedRefinedOppositeJacquetCongr T B S e (refinedOppositeJacquetMk B S ρ v) =
      refinedOppositeJacquetMk B S τ (e v) :=
  rfl

/-- The positive half of the product modulus is the product of the block positive halves. -/
theorem refinedLeviHalfModulus_eq_prod (m : refinedLevi F.Carrier B S) :
    (T.refinedLeviHalfModulus B S m : ℂ) =
      ∏ i, ((NNReal.sqrt (T.leviModulus (S i) (PadicField.TopologicalData.refinedLeviBlock B S i m) : ℝ≥0) : ℝ) : ℂ) := by
  rw [T.refinedLeviHalfModulus_apply, T.refinedLeviModulus_apply, Units.coe_prod]
  have h : NNReal.sqrt (∏ i, (T.leviModulus (S i) (PadicField.TopologicalData.refinedLeviBlock B S i m) : ℝ≥0)) =
      ∏ i, NNReal.sqrt (T.leviModulus (S i) (PadicField.TopologicalData.refinedLeviBlock B S i m) : ℝ≥0) :=
    map_prod NNReal.sqrtHom _ _
  rw [h, NNReal.coe_prod, Complex.ofReal_prod]

variable (A : ∀ i, Rep.{uV} ℂ (GeneralLinear (B.size i) F.Carrier))

/-- The coinvariant comparison, with the carriers of the general-linear opposite Jacquet
modules of the factors as target. -/
def refinedCoinvariantsEquiv :
    RefinedOppositeJacquetModule B S (FiniteTensor.external fun i => (A i).ρ) ≃ₗ[ℂ]
      PiTensorProduct ℂ (fun i => CuspidalJacquetMultiplicity.oppositeJacquet T (S i) (A i)) :=
  coinvariantsEquiv (fun i => (A i).ρ) (fun i => (S i).oppositeUnipotentSubgroup F.Carrier)

theorem refinedCoinvariantsEquiv_mk_tprod (v : ∀ i, A i) :
    refinedCoinvariantsEquiv T B S A
        (refinedOppositeJacquetMk B S _ (PiTensorProduct.tprod ℂ v)) =
      PiTensorProduct.tprod ℂ (fun i => PadicField.TopologicalData.oppositeJacquetMk T (S i) (A i) (v i)) :=
  coinvariantsEquiv_mk_tprod _ _ v

/-- The block coordinates of a refined Levi element embed back to its actual blocks. -/
theorem leviEmbedding_refinedLeviEquiv_symm (m : refinedLevi F.Carrier B S) (i : Fin B.length) :
    (S i).leviEmbedding F.Carrier ((refinedLeviEquiv F.Carrier B S).symm m i) = m.val i :=
  congrArg Subtype.val
    (((S i).leviEquiv F.Carrier).apply_symm_apply (refinedLeviEval F.Carrier B S i m))

theorem refinedCoinvariantsEquiv_comm (m : refinedLevi F.Carrier B S) (v : ∀ i, A i) :
    refinedCoinvariantsEquiv T B S A
        (T.normalizedRefinedOppositeJacquet B S (FiniteTensor.external fun i => (A i).ρ) m
          (refinedOppositeJacquetMk B S _ (PiTensorProduct.tprod ℂ v))) =
      FiniteTensor.external
          (fun i => (CuspidalJacquetMultiplicity.oppositeJacquet T (S i) (A i)).ρ)
          ((refinedLeviEquiv F.Carrier B S).symm m)
        (refinedCoinvariantsEquiv T B S A
          (refinedOppositeJacquetMk B S _ (PiTensorProduct.tprod ℂ v))) := by
  rw [T.normalizedRefinedOppositeJacquet_mk, FiniteTensor.external_tprod, map_smul,
    refinedCoinvariantsEquiv_mk_tprod, refinedCoinvariantsEquiv_mk_tprod,
    FiniteTensor.external_tprod]
  simp_rw [oppositeJacquet_mk]
  rw [MultilinearMap.map_smul_univ, refinedLeviHalfModulus_eq_prod T B S m]
  simp_rw [leviEmbedding_refinedLeviEquiv_symm]
  rfl

/-- The normalized refined opposite Jacquet module of an external tensor product is the
external tensor product of the general-linear opposite Jacquet modules of the factors,
pulled back along the block coordinates of the refined Levi. -/
def oppositeJacquetEquiv :
    Representation.Equiv
      (T.normalizedRefinedOppositeJacquet B S (FiniteTensor.external fun i => (A i).ρ))
      ((FiniteTensor.external fun i =>
        (CuspidalJacquetMultiplicity.oppositeJacquet T (S i) (A i)).ρ).comp
          (refinedLeviEquiv F.Carrier B S).symm.toMonoidHom) :=
  Representation.Equiv.mk (refinedCoinvariantsEquiv T B S A) (fun m => by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := refinedOppositeJacquetMk_surjective B S _ x
    induction y using PiTensorProduct.induction_on with
    | smul_tprod a v =>
      simp only [LinearMap.comp_apply, map_smul]
      exact congrArg (a • ·) (refinedCoinvariantsEquiv_comm T B S A m v)
    | add x y hx hy =>
      simp only [LinearMap.comp_apply, map_add] at hx hy ⊢
      rw [hx, hy])

end Opposite

end Langlands.RefinedOppositeJacquetTensor

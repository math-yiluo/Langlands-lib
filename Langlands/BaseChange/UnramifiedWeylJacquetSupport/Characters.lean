import Langlands.BaseChange.UnramifiedWeylJacquetSupportStatement
import Langlands.Group.GL.SingleBlock
import Langlands.Representation.CuspidalSupport.BlockPermutation
import Langlands.Representation.RankinSelberg.RankOneCharacterReductionProof
import Mathlib.RingTheory.PiTensorProduct

/-! The scalar inducing characters and Weyl transport for the singleton Levi. -/

noncomputable section

namespace Langlands.BaseChange.WeylJacquet

open GeneralLinear GeneralLinear.BlockShape Correspondence Unramified
open Unramified.SphericalExistence Geometric CuspidalSupport

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) {r : ℕ}

attribute [local instance] heckeFieldTopology heckeGeneralLinearTopology
  heckeGeneralLinearTopologicalGroup

set_option hygiene false in
local notation "B" => singletons (r + 1)
set_option hygiene false in
local notation "M" => (singletons (r + 1)).Levi F.Carrier

/-- Diagonal coordinates on the Borel Levi, with inverse given by singleton scalar blocks. -/
def singletonCoordinates (r : ℕ) : M ≃* (Fin (r + 1) → F.Carrierˣ) where
  toFun m i := determinant (m i)
  invFun a := singletonLevi F.Carrier a
  left_inv m := funext fun i => RankinSelberg.scalar_determinant_rankOne (m i)
  right_inv a := funext fun i => by
    change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) (a i)) = a i
    simp
  map_mul' m n := funext fun i => map_mul determinant (m i) (n i)

/-- Product of the unramified inducing characters on the diagonal blocks. -/
def borelCharacter (z : Fin (r + 1) → ℂˣ) : M →* ℂˣ where
  toFun m := ∏ i, character F (z i) (determinant (m i))
  map_one' := by
    apply Finset.prod_eq_one
    intro i _
    change character F (z i) (determinant (1 : GeneralLinear 1 F.Carrier)) = 1
    rw [map_one, map_one]
  map_mul' m n := by
    simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib]

@[simp]
theorem borelCharacter_singletonLevi (z : Fin (r + 1) → ℂˣ) (a : Fin (r + 1) → F.Carrierˣ) :
    borelCharacter F z (singletonLevi F.Carrier a) = ∏ i, character F (z i) (a i) := by
  change (∏ i, character F (z i) (determinant (singletonLevi F.Carrier a i))) = _
  exact Finset.prod_congr rfl fun i _ => congrArg (character F (z i))
    (congrFun ((singletonCoordinates F r).apply_symm_apply a) i)

theorem borelCharacter_eq_one_of_mem_integral (z : Fin (r + 1) → ℂˣ) {m : M}
    (hm : m ∈ borelIntegralDiagonal F r) : borelCharacter F z m = 1 := by
  obtain ⟨a, rfl⟩ := (singletonCoordinates F r).symm.surjective m
  change borelCharacter F z (singletonLevi F.Carrier a) = 1
  rw [borelCharacter_singletonLevi]
  have ha := (singletonLevi_mem_borelIntegralDiagonal_iff F a).mp hm
  apply Finset.prod_eq_one
  intro i _
  rw [character_apply, ha i, zpow_zero]

@[simp]
theorem borelCharacter_uniformizer (z : Fin (r + 1) → ℂˣ) (i : Fin (r + 1)) :
    borelCharacter F z (borelUniformizerLevi F r i) = z i := by
  classical
  rw [borelUniformizerLevi_eq_singletonLevi, borelCharacter_singletonLevi,
    Finset.prod_eq_single i (fun j _ hji => by rw [Pi.mulSingle_eq_of_ne hji, map_one])
      (fun hi => (hi (Finset.mem_univ i)).elim), Pi.mulSingle_eq_same, character_uniformizer]

set_option backward.isDefEq.respectTransparency false in
/-- The external tensor of the diagonal characters acts by their product on the whole line. -/
theorem blockTensor_eq_smul (z : Fin (r + 1) → ℂˣ) (m : (borelShape r).Levi F.Carrier)
    (v : PiTensorProduct ℂ (fun _ : Fin (borelShape r).length => ℂ)) :
    (borelShape r).blockTensor (blockCharacters F z) m v = (borelCharacter F z m : ℂ) • v := by
  suffices h : (borelShape r).blockTensor (blockCharacters F z) m =
      (borelCharacter F z m : ℂ) • 1 from
    LinearMap.congr_fun h v
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro f
  change (borelShape r).blockTensor (blockCharacters F z) m (PiTensorProduct.tprod ℂ f) =
    (borelCharacter F z m : ℂ) • PiTensorProduct.tprod ℂ f
  rw [blockTensor_tprod]
  change PiTensorProduct.tprod ℂ (fun i => (character F (z i) (determinant (m i)) : ℂ) • f i) = _
  rw [MultilinearMap.map_smul_univ]
  simp only [borelCharacter, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod]
  rfl

/-- Every permutation is minimal for two singleton block shapes. -/
theorem singleton_minimal (w : Equiv.Perm (Fin (r + 1))) : IsMinimalRepresentative B B w := by
  constructor <;> (intro i a b hab; exact (lt_irrefl _ ((Subsingleton.elim a b) ▸ hab)).elim)

private theorem singleton_blockIndex (a : Fin (r + 1)) : blockIndex B a = a := by
  have hi := singletons_index (n := r + 1) a 0
  exact (congrArg (blockIndex B) hi.symm).trans (blockIndex_index B a 0)

/-- Every permutation matrix normalizes the singleton Levi. -/
theorem singleton_conjugatesLevi (w : Equiv.Perm (Fin (r + 1))) :
    ConjugatesLevi (F := F.Carrier) B B w :=
  conjugatesLevi_of_blockIndex w (fun i => (w i).val) (Fin.val_injective.comp w.injective)
    (fun i => by rw [singleton_blockIndex, singleton_blockIndex])

/-- The diagonal Levi has no proper standard refinements. -/
theorem singleton_isLeviQuasicuspidal {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ M V) : IsLeviQuasicuspidal B ρ := by
  intro S hS
  have h (i : Fin (B).length) : (S i).parabolic F.Carrier = ⊤ := by
    let C : BlockShape 1 := S i
    have hlen : C.length ≤ 1 := C.length_le
    have hpos : 0 < C.length := by
      by_contra! hzero
      have hz : C.length = 0 := Nat.eq_zero_of_le_zero hzero
      have : IsEmpty (Fin C.length) := ⟨fun j => by have := j.isLt; omega⟩
      simpa using C.sum_eq.symm
    exact C.singleBlock_parabolic_eq_top (by omega) F.Carrier
  exact (hS (by rw [refinedParabolic, funext h, Subgroup.pi_top])).elim

/-- Inverse conjugation by a permutation matrix pulls a diagonal tuple back by the
 permutation. -/
theorem singleton_leviConjugation_symm (w : Equiv.Perm (Fin (r + 1)))
    (a : Fin (r + 1) → F.Carrierˣ) :
    (leviConjugation B B w (singleton_conjugatesLevi F w)).symm (singletonLevi F.Carrier a) =
      singletonLevi F.Carrier (a ∘ w) := by
  apply (B).leviEmbedding_injective F.Carrier
  rw [leviConjugation_symm_embedding]
  apply Units.ext
  ext i j
  have he := permutation_conjugate_entry (r + 1) F.Carrier w⁻¹
    ((B).leviEmbedding F.Carrier (singletonLevi F.Carrier a)) i j
  simp only [permutation_inv, inv_inv] at he
  change ((permutation _ _ w⁻¹ * (B).leviEmbedding F.Carrier (singletonLevi F.Carrier a) *
    permutation _ _ w).val) i j = _ at he
  rw [permutation_inv, he, leviEmbedding_singletonLevi_val, leviEmbedding_singletonLevi_val]
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    rfl
  · rw [Matrix.diagonal_apply_ne _ (w.injective.ne hij), Matrix.diagonal_apply_ne _ hij]

set_option backward.isDefEq.respectTransparency false in
/-- Weyl transport of the inducing tensor has diagonal character with permuted values at
 the uniformizer. -/
theorem transport_blockTensor_eq_smul (z : Fin (r + 1) → ℂˣ)
    (w : Equiv.Perm (Fin (r + 1))) (m : M)
    (v : PiTensorProduct ℂ (fun _ : Fin (B).length => ℂ)) :
    transport B B w (singleton_conjugatesLevi F w)
      ((borelShape r).blockTensor (blockCharacters F z)) m v =
      (borelCharacter F (z ∘ w.symm) m : ℂ) • v := by
  classical
  obtain ⟨a, rfl⟩ := (singletonCoordinates F r).symm.surjective m
  change (borelShape r).blockTensor (blockCharacters F z)
    ((leviConjugation B B w (singleton_conjugatesLevi F w)).symm (singletonLevi F.Carrier a)) v = _
  change _ = (borelCharacter F (z ∘ w.symm) (singletonLevi F.Carrier a) : ℂ) • v
  rw [singleton_leviConjugation_symm, blockTensor_eq_smul, borelCharacter_singletonLevi,
    borelCharacter_singletonLevi]
  apply congrArg (fun c : ℂˣ => (c : ℂ) • v)
  exact Fintype.prod_equiv w _ _ (fun i => by simp only [Function.comp_apply, Equiv.symm_apply_apply])

end Langlands.BaseChange.WeylJacquet

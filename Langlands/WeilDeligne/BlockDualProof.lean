import Langlands.WeilDeligne.BlockStatements
import Langlands.WeilDeligne.TensorDual

/-!
# The dual of a block

The dual of `block ν σ m = σ ⊗ S_m` is computed in three steps:

* duality distributes over the tensor product (`tensorDualEquiv`), and the dual
  of the zero-monodromy pair of `σ` is the zero-monodromy pair of `σ^∨`;
* the dual special block is `S_m^∨ ≅ ν^(1-m) ⊗ S_m`: the dual coordinate
  functional at weight `ν^(-j)` goes to `(-1)^j` times the coordinate vector at
  position `m-1-j`, whose twisted weight is `ν^(1-m) ν^(m-1-j) = ν^(-j)`; the sign
  turns the negative transpose of raising monodromy into raising monodromy;
* a character twist on the special-block factor moves to the Weil factor through
  the identity carrier map.
-/

noncomputable section

namespace Langlands.WeilDeligneRepresentation

universe uK uG uV uW

open scoped TensorProduct

variable {K : Type uK} {G : Type uG} [Field K] [Group G]

namespace Special

/-- The coordinate vector at `j` has weight `ν^j`: the published
`action_basisVector`, for `Pi.single j 1`. -/
theorem action_single (ν : G →* Kˣ) (m : ℕ) (g : G) (j : Fin m) :
    action ν m g (Pi.single j 1) = (ν g : K) ^ j.val • Pi.single j 1 := by
  have h : (Pi.single j 1 : Fin m → K) = basisVector K j := by
    funext k
    simp [Pi.single_apply, basisVector]
  rw [h]
  exact action_basisVector ν m g j

/-- Raising monodromy moves the coordinate vector at `j` to `j + 1`, and kills
the top coordinate vector. -/
theorem raising_single (m : ℕ) (j : Fin m) :
    raising K m (Pi.single j 1) =
      if h : j.val + 1 < m then Pi.single ⟨j.val + 1, h⟩ 1 else 0 := by
  funext k
  rw [raising_apply]
  by_cases hk : 0 < k.val
  · rw [dite_eq_left hk]
    by_cases hj : j.val + 1 < m
    · rw [dite_eq_left hj]
      by_cases hkj : k.val = j.val + 1
      · have h1 : (⟨k.val - 1, by omega⟩ : Fin m) = j := Fin.ext (by simp; omega)
        have h2 : k = ⟨j.val + 1, hj⟩ := Fin.ext hkj
        rw [h1, h2]
        simp
      · have h1 : (⟨k.val - 1, by omega⟩ : Fin m) ≠ j := by
          intro he
          have := congrArg Fin.val he
          simp at this
          omega
        have h2 : k ≠ ⟨j.val + 1, hj⟩ := by
          intro he
          exact hkj (congrArg Fin.val he)
        rw [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
    · rw [dite_eq_right hj]
      have h1 : (⟨k.val - 1, by omega⟩ : Fin m) ≠ j := by
        intro he
        have := congrArg Fin.val he
        simp at this
        omega
      rw [Pi.single_eq_of_ne h1]
      rfl
  · rw [dite_eq_right hk]
    split
    · rename_i hj
      have h2 : k ≠ ⟨j.val + 1, hj⟩ := by
        intro he
        have := congrArg Fin.val he
        simp at this
        omega
      rw [Pi.single_eq_of_ne h2]
    · rfl

/-- Reversal of coordinates with the alternating sign `(-1)^(m-1-i)`. -/
def signReverse (K : Type uK) [Field K] (m : ℕ) : (Fin m → K) ≃ₗ[K] (Fin m → K) where
  toFun w i := (-1) ^ (Fin.rev i).val * w (Fin.rev i)
  invFun u j := (-1) ^ j.val * u (Fin.rev j)
  map_add' w w' := by
    funext i
    simp [mul_add]
  map_smul' c w := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  left_inv w := by
    funext j
    simp only [Fin.rev_rev]
    rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp
  right_inv u := by
    funext i
    simp only [Fin.rev_rev]
    rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp

/-- The dual coordinates of a functional on `Fin m → K`, reversed and signed:
the functional `ℓ` goes to `i ↦ (-1)^(m-1-i) ℓ(e_(m-1-i))`. -/
def dualEquiv (K : Type uK) [Field K] (m : ℕ) : Module.Dual K (Fin m → K) ≃ₗ[K] (Fin m → K) :=
  (Pi.basisFun K (Fin m)).dualBasis.equivFun.trans (signReverse K m)

theorem dualEquiv_apply (m : ℕ) (ℓ : Module.Dual K (Fin m → K)) (i : Fin m) :
    dualEquiv K m ℓ i = (-1) ^ (Fin.rev i).val * ℓ (Pi.single (Fin.rev i) 1) := by
  change (-1) ^ (Fin.rev i).val *
      (Pi.basisFun K (Fin m)).dualBasis.equivFun ℓ (Fin.rev i) = _
  rw [Module.Basis.dualBasis_equivFun, Pi.basisFun_apply]

/-- The weight identity behind the dual special block:
`ν(g)^(-k) = ν(g)^(1-m) ν(g)^i` when `m = i + 1 + k`. -/
theorem units_inv_pow_eq (u : Kˣ) (i k : ℕ) :
    ((u⁻¹ : Kˣ) : K) ^ k = ((u ^ (1 - ((i + 1 + k : ℕ) : ℤ)) : Kˣ) : K) * (u : K) ^ i := by
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
  congr 1
  rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add]
  congr 1
  push_cast
  ring

end Special

/-- The dual special block: `S_m^∨ ≅ ν^(1-m) ⊗ S_m`. -/
def specialBlockDualEquiv (ν : G →* Kˣ) (m : ℕ) :
    Equiv (dual (specialBlock ν m)) (twist (ν ^ (1 - (m : ℤ))) (specialBlock ν m)) where
  representationEquiv :=
    Representation.Equiv.mk (Special.dualEquiv K m) (fun g => by
      apply LinearMap.ext
      intro (ℓ : Module.Dual K (Fin m → K))
      funext i
      change Special.dualEquiv K m (ℓ ∘ₗ Special.action ν m g⁻¹) i =
        ((ν ^ (1 - (m : ℤ))) g : K) * ((ν g : K) ^ i.val * Special.dualEquiv K m ℓ i)
      rw [Special.dualEquiv_apply, Special.dualEquiv_apply, LinearMap.comp_apply,
        Special.action_single, map_smul, smul_eq_mul, MonoidHom.zpow_apply, map_inv]
      have hm : m = i.val + 1 + (Fin.rev i).val := by
        rw [Fin.val_rev]
        omega
      have hw := Special.units_inv_pow_eq (ν g) i.val (Fin.rev i).val
      rw [← hm] at hw
      rw [hw]
      ring)
  comm_monodromy := by
    apply LinearMap.ext
    intro (ℓ : Module.Dual K (Fin m → K))
    funext i
    change Special.dualEquiv K m (-(ℓ ∘ₗ Special.raising K m)) i =
      Special.raising K m (Special.dualEquiv K m ℓ) i
    rw [Special.raising_apply, Special.dualEquiv_apply, LinearMap.neg_apply,
      LinearMap.comp_apply, Special.raising_single]
    by_cases hi : 0 < i.val
    · have hr : (Fin.rev i).val + 1 < m := by
        rw [Fin.val_rev]
        omega
      rw [dite_eq_left hr, dite_eq_left hi, Special.dualEquiv_apply]
      have he : (⟨(Fin.rev i).val + 1, hr⟩ : Fin m) = Fin.rev ⟨i.val - 1, by omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_rev]
        omega
      have hs : (Fin.rev (⟨i.val - 1, by omega⟩ : Fin m)).val = (Fin.rev i).val + 1 := by
        simp only [Fin.val_rev]
        omega
      rw [he, hs, pow_succ]
      ring
    · have hr : ¬ (Fin.rev i).val + 1 < m := by
        rw [Fin.val_rev]
        omega
      rw [dite_eq_right hr, dite_eq_right hi, map_zero, neg_zero, mul_zero]

/-- A character twist on the second tensor factor moves to the first, through
the identity carrier map. -/
def tensorTwistEquiv (ν χ : G →* Kˣ) (τ : FiniteRepresentation.{uK, uG, uV} K G)
    (B : WeilDeligneRepresentation.{uK, uG, uW} K G ν) :
    Equiv (tensor (zeroMonodromy ν τ) (twist χ B))
      (tensor (zeroMonodromy ν (FiniteRepresentation.twist χ τ)) B) where
  representationEquiv :=
    Representation.Equiv.mk (LinearEquiv.refl K (τ ⊗[K] B)) (fun g => by
      apply TensorProduct.ext'
      intro v w
      change τ.representation g v ⊗ₜ[K] ((χ g : K) • B.representation g w) =
        ((χ g : K) • τ.representation g v) ⊗ₜ[K] B.representation g w
      rw [TensorProduct.smul_tmul])
  comm_monodromy := rfl

namespace Blocks

/-- The dual block `(σ ⊗ S_m)^∨ ≅ (σ^∨ ⊗ ν^(1-m)) ⊗ S_m`. -/
def blockDualEquiv (ν : G →* Kˣ) (σ : FiniteRepresentation.{uK, uG, uV} K G) (m : ℕ) :
    Equiv (dual (block ν σ m))
      (block ν (FiniteRepresentation.twist (ν ^ (1 - (m : ℤ))) (FiniteRepresentation.dual σ)) m) :=
  (tensorDualEquiv (zeroMonodromy ν σ) (specialBlock ν m)).symm.trans
    ((tensorEquiv (dualZeroMonodromyEquiv σ) (specialBlockDualEquiv ν m)).trans
      (tensorTwistEquiv ν (ν ^ (1 - (m : ℤ))) (FiniteRepresentation.dual σ) (specialBlock ν m)))

/-- The corrected dual-block identity `(σ ⊗ S_m)^∨ ≅ (σ^∨ ⊗ ν^(1-m)) ⊗ S_m`. -/
theorem blockDual : BlockDual.{uK, uG, uV} :=
  fun _ _ _ _ ν σ m => ⟨blockDualEquiv ν σ m⟩

end Blocks

end Langlands.WeilDeligneRepresentation

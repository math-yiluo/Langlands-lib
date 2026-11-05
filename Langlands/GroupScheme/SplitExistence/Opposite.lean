import Langlands.GroupScheme.SplitExistence.Points
import Mathlib.LinearAlgebra.RootSystem.Hom
import Mathlib.LinearAlgebra.RootSystem.Base

/-! # Opposite Chevalley data

The negation `x ↦ -x` of a root pairing is an automorphism permuting the roots by `α ↦ -α`. It
sends a base `b` to the opposite base `-b`. For Chevalley data `D` on `b` we build Chevalley data
`D.neg` on `-b` with the same lattice, weights and root operators, the functional `-ℓ`, and the
`SL₂`-homomorphisms of the simple roots `-α_i` obtained by precomposing those of `α_i` with
conjugation by `[[0, 1], [1, 0]]`. -/

noncomputable section

universe u

open Matrix

namespace Langlands.GroupScheme.SplitExistence

section SL2Swap

variable {R : Type*} [CommRing R]

/-- The permutation matrix `[[0, 1], [1, 0]]`. -/
def swapMat : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]

theorem swapMat_mul_self : (swapMat : Matrix (Fin 2) (Fin 2) R) * swapMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat]

theorem det_swapMat : (swapMat : Matrix (Fin 2) (Fin 2) R).det = -1 := by
  simp [swapMat, det_fin_two]

/-- Conjugation by `[[0, 1], [1, 0]]`, an automorphism of `SL₂`. -/
def sl2Swap : SpecialLinearGroup (Fin 2) R →* SpecialLinearGroup (Fin 2) R where
  toFun g := ⟨swapMat * g.1 * swapMat, by
    rw [det_mul, det_mul, det_swapMat, g.prop]
    ring⟩
  map_one' := Subtype.ext (by
    change swapMat * (1 : Matrix (Fin 2) (Fin 2) R) * swapMat = 1
    rw [mul_one, swapMat_mul_self])
  map_mul' g h := Subtype.ext (by
    change swapMat * (g.1 * h.1) * swapMat = (swapMat * g.1 * swapMat) * (swapMat * h.1 * swapMat)
    have := (swapMat_mul_self : (swapMat : Matrix (Fin 2) (Fin 2) R) * swapMat = 1)
    calc swapMat * (g.1 * h.1) * swapMat
        = swapMat * g.1 * (swapMat * swapMat) * h.1 * swapMat := by
          rw [this]; simp [mul_assoc]
      _ = _ := by simp [mul_assoc])

theorem coe_sl2Swap (g : SpecialLinearGroup (Fin 2) R) :
    ((sl2Swap g : SpecialLinearGroup (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      swapMat * (g : Matrix (Fin 2) (Fin 2) R) * swapMat :=
  rfl

theorem sl2Swap_upper (s : R) : sl2Swap (sl2Upper s) = sl2Lower s := by
  apply Subtype.ext
  rw [coe_sl2Swap]
  change swapMat * !![1, s; 0, 1] * swapMat = !![1, 0; s, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat]

theorem sl2Swap_lower (s : R) : sl2Swap (sl2Lower s) = sl2Upper s := by
  apply Subtype.ext
  rw [coe_sl2Swap]
  change swapMat * !![1, 0; s, 1] * swapMat = !![1, s; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat]

theorem sl2Swap_diag (t : Rˣ) : sl2Swap (sl2Diag t) = sl2Diag t⁻¹ := by
  apply Subtype.ext
  rw [coe_sl2Swap]
  change swapMat * !![(t : R), 0; 0, ((t⁻¹ : Rˣ) : R)] * swapMat =
    !![((t⁻¹ : Rˣ) : R), 0; 0, (((t⁻¹)⁻¹ : Rˣ) : R)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat]

theorem sl2Swap_weyl :
    sl2Swap (sl2Weyl : SpecialLinearGroup (Fin 2) R) = sl2Weyl * sl2Diag (-1) := by
  apply Subtype.ext
  rw [coe_sl2Swap]
  change swapMat * !![(0 : R), 1; -1, 0] * swapMat =
    !![(0 : R), 1; -1, 0] * !![(((-1 : Rˣ)) : R), 0; 0, (((-1 : Rˣ)⁻¹ : Rˣ) : R)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat]

theorem sl2Swap_map {S : Type*} [CommRing S] (f : R →+* S) (g : SpecialLinearGroup (Fin 2) R) :
    (sl2Swap g).map f = sl2Swap (g.map f) := by
  apply Subtype.ext
  change ((swapMat * (g : Matrix (Fin 2) (Fin 2) R) * swapMat).map f) =
    swapMat * (g : Matrix (Fin 2) (Fin 2) R).map f * swapMat
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [swapMat]

end SL2Swap

section NegBase

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N)

/-- The index involution `α ↦ -α`. -/
def negIndex : Equiv.Perm ι :=
  letI := P.indexNeg
  Function.Involutive.toPerm (fun i => P.reflectionPerm i i) (fun i => neg_neg i)

@[simp] theorem negIndex_apply (i : ι) : negIndex P i = P.reflectionPerm i i := rfl

theorem negIndex_negIndex (i : ι) : negIndex P (negIndex P i) = i :=
  letI := P.indexNeg
  neg_neg i

/-- The negation automorphism of a root pairing. -/
def negEquiv : RootPairing.Equiv P P where
  weightMap := -LinearMap.id
  coweightMap := -LinearMap.id
  indexEquiv := negIndex P
  weight_coweight_transpose := by
    ext x y
    simp
  root_weightMap := by
    ext i
    simp [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  coroot_coweightMap := by
    ext i
    have h : (negIndex P).symm i = P.reflectionPerm i i := by
      rw [Equiv.symm_apply_eq]
      exact (negIndex_negIndex P i).symm
    simp [h, RootPairing.coroot_reflectionPerm, RootPairing.coreflection_apply_self]
  bijective_weightMap := (LinearEquiv.neg R : M ≃ₗ[R] M).bijective
  bijective_coweightMap := (LinearEquiv.neg R : N ≃ₗ[R] N).bijective

variable {P}

/-- The opposite base `-b`. -/
def negBase (b : P.Base) : P.Base := b.map (negEquiv P)

theorem mem_negBase_support {b : P.Base} {i : ι} :
    i ∈ (negBase b).support ↔ P.reflectionPerm i i ∈ b.support := by
  classical
  rw [negBase, RootPairing.Base.support_map_eq, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    change P.reflectionPerm (negIndex P j) (negIndex P j) ∈ b.support
    rw [← negIndex_apply, negIndex_negIndex]
    exact hj
  · intro h
    exact ⟨_, h, negIndex_negIndex P i⟩

theorem reflection_negIndex (i : ι) : P.reflection (P.reflectionPerm i i) = P.reflection i := by
  ext x
  simp [RootPairing.reflection_apply, RootPairing.root_reflectionPerm,
    RootPairing.coroot_reflectionPerm, RootPairing.coreflection_apply_self]
  module

theorem reflectionPerm_negIndex (i : ι) :
    P.reflectionPerm (P.reflectionPerm i i) = P.reflectionPerm i := by
  ext j
  apply P.root.injective
  rw [RootPairing.root_reflectionPerm, RootPairing.root_reflectionPerm, reflection_negIndex]

end NegBase

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  (D : ChevalleyData P b)

/-- The simple root `α_i` of `b` attached to the simple root `-α_i` of `-b`. -/
def negSimple (i : (negBase b).support) : b.support :=
  ⟨P.reflectionPerm i i, mem_negBase_support.1 i.2⟩

theorem reflectionPerm_negSimple (i : (negBase b).support) :
    P.reflectionPerm (negSimple i : J) (negSimple i) = i :=
  negIndex_negIndex P i

variable (P) in
/-- The character `x ↦ (-1) ^ ⟨x, coroot i⟩` of `X`. -/
def signChar (R : Type u) [CommRing R] (i : J) : Multiplicative X →* Rˣ where
  toFun x := (-1 : Rˣ) ^ (P.toLinearMap (Multiplicative.toAdd (x : Multiplicative X)) (P.coroot i))
  map_one' := by simp
  map_mul' x y := by simp [zpow_add]

theorem φ_sl2Diag_neg_one (i : b.support) (R : Type u) [CommRing R] :
    D.φ i R (sl2Diag (-1)) = D.torusHom (signChar P R (i : J)) := by
  apply Units.ext
  rw [D.φ_diag, coe_torusHom]
  rfl

/-- **Opposite Chevalley data** on the opposite base `-b`. -/
def neg : ChevalleyData P (negBase b) where
  ℓ := -D.ℓ
  ℓ_pos i hi := by
    have h := D.ℓ_pos _ (mem_negBase_support.1 hi)
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, map_neg] at h
    simpa using h
  n := D.n
  wt := D.wt
  closure_range_wt := D.closure_range_wt
  e := D.e
  e_zero := D.e_zero
  e_mul := D.e_mul
  e_eq_zero := D.e_eq_zero
  e_weight := D.e_weight
  e_one_map_ne_zero := D.e_one_map_ne_zero
  φ i R := (D.φ (negSimple i) R).comp sl2Swap
  φ_natural i R S _ _ f g := by
    have h := D.φ_natural (negSimple i) R S f (sl2Swap g)
    rw [sl2Swap_map] at h
    exact h
  φ_upper i R _ s := by
    change ((D.φ (negSimple i) R (sl2Swap (sl2Upper s)) : GL (Fin D.n) R) :
      Matrix (Fin D.n) (Fin D.n) R) = _
    rw [sl2Swap_upper, D.φ_lower, reflectionPerm_negSimple]
  φ_lower i R _ s := by
    change ((D.φ (negSimple i) R (sl2Swap (sl2Lower s)) : GL (Fin D.n) R) :
      Matrix (Fin D.n) (Fin D.n) R) = _
    rw [sl2Swap_lower, D.φ_upper]
    rfl
  φ_diag i R _ t := by
    change ((D.φ (negSimple i) R (sl2Swap (sl2Diag t)) : GL (Fin D.n) R) :
      Matrix (Fin D.n) (Fin D.n) R) = _
    rw [sl2Swap_diag, D.φ_diag]
    congr 1
    funext c
    have hc : P.coroot (negSimple i : J) = -P.coroot (i : J) := by
      change P.coroot (P.reflectionPerm i i) = _
      rw [RootPairing.coroot_reflectionPerm, RootPairing.coreflection_apply_self]
    rw [hc, map_neg, inv_zpow', neg_neg]
  weyl_weight i R _ c d h := by
    change ((D.φ (negSimple i) R (sl2Swap sl2Weyl) : GL (Fin D.n) R) :
      Matrix (Fin D.n) (Fin D.n) R) c d ≠ 0 at h
    rw [sl2Swap_weyl, map_mul, D.φ_sl2Diag_neg_one, Units.val_mul, coe_torusHom,
      Matrix.mul_diagonal] at h
    have h' : ((D.φ (negSimple i) R sl2Weyl : GL (Fin D.n) R) : Matrix (Fin D.n) (Fin D.n) R)
        c d ≠ 0 := left_ne_zero_of_mul h
    rw [D.weyl_weight _ R c d h']
    change (P.reflection (P.reflectionPerm i i)) (D.wt d) = _
    rw [reflection_negIndex]
  weyl_conj i j := by
    obtain ⟨ε, hε, hconj⟩ := D.weyl_conj (negSimple i) j
    let m : ℤ := P.toLinearMap (P.root j) (P.coroot (negSimple i : J))
    refine ⟨ε * (((-1 : ℤˣ) ^ m : ℤˣ) : ℤ), ?_, fun R _ s => ?_⟩
    · rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ m) with h | h <;> rw [h] <;>
        rcases hε with rfl | rfl <;> simp
    · have hGL : ∀ t : R, D.φ (negSimple i) R sl2Weyl * D.x j t *
          (D.φ (negSimple i) R sl2Weyl)⁻¹ =
            D.x (P.reflectionPerm (negSimple i) j) ((ε : R) * t) := by
        intro t
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, coe_x, coe_x]
        exact hconj R t
      have hsign : ((signChar P R (negSimple i : J) (Multiplicative.ofAdd (P.root j)) : Rˣ) : R) =
          ((((-1 : ℤˣ) ^ m : ℤˣ) : ℤ) : R) := by
        change (((-1 : Rˣ) ^ m : Rˣ) : R) = _
        have h1 : ((-1 : Rˣ) ^ m : Rˣ) = Units.map (Int.castRingHom R).toMonoidHom ((-1 : ℤˣ) ^ m) := by
          have hm1 : Units.map (Int.castRingHom R).toMonoidHom (-1 : ℤˣ) = -1 :=
            Units.ext (by simp)
          rw [map_zpow, hm1]
        rw [h1]
        rfl
      have key : D.φ (negSimple i) R (sl2Swap sl2Weyl) * D.x j s *
          (D.φ (negSimple i) R (sl2Swap sl2Weyl))⁻¹ =
            D.x (P.reflectionPerm i j) (((ε * (((-1 : ℤˣ) ^ m : ℤˣ) : ℤ) : ℤ) : R) * s) := by
        rw [sl2Swap_weyl, map_mul, D.φ_sl2Diag_neg_one]
        calc D.φ (negSimple i) R sl2Weyl * D.torusHom (signChar P R (negSimple i : J)) * D.x j s *
              (D.φ (negSimple i) R sl2Weyl * D.torusHom (signChar P R (negSimple i : J)))⁻¹
            = D.φ (negSimple i) R sl2Weyl * (D.torusHom (signChar P R (negSimple i : J)) * D.x j s *
              (D.torusHom (signChar P R (negSimple i : J)))⁻¹) *
                (D.φ (negSimple i) R sl2Weyl)⁻¹ := by group
          _ = D.φ (negSimple i) R sl2Weyl * D.x j (((signChar P R (negSimple i : J)
                (Multiplicative.ofAdd (P.root j)) : Rˣ) : R) * s) *
                (D.φ (negSimple i) R sl2Weyl)⁻¹ := by rw [torusHom_conj_x]
          _ = _ := by
            rw [hGL, hsign]
            change D.x (P.reflectionPerm (P.reflectionPerm i i) j) _ = _
            rw [reflectionPerm_negIndex]
            congr 1
            push_cast
            ring
      have h2 := congrArg Units.val key
      rw [Units.val_mul, Units.val_mul, coe_x, coe_x] at h2
      exact h2
  commutator := D.commutator

end ChevalleyData

end Langlands.GroupScheme.SplitExistence

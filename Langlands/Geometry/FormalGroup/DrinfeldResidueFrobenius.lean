import Langlands.Geometry.FormalGroup.DrinfeldFramedClassFunctor
import Mathlib.FieldTheory.Finite.Basic

/-! # Signed residue Frobenius shifts for Drinfeld's functor -/

noncomputable section

universe u v w s z

namespace Langlands.FormalGroup.LocalDivision.DrinfeldResidue

open CategoryTheory ModuleLaw ValuativeRel

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (κ : Type v) [Field κ] [Algebra 𝓀[K] κ] [Algebra.IsAlgebraic 𝓀[K] κ]
  [Algebra 𝒪[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ]

local instance : Fintype 𝓀[K] := Fintype.ofFinite _

/-- The arithmetic residue Frobenius of the frame field over the acting integer ring. -/
def frobenius : κ ≃ₐ[𝒪[K]] κ :=
  (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] κ).restrictScalars 𝒪[K]

/-- The residue Frobenius is the actual power by the cardinal of the scalar residue field. -/
theorem frobenius_apply (x : κ) : frobenius K κ x = x ^ Nat.card 𝓀[K] := by
  change (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] κ) x = _
  rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, Nat.card_eq_fintype_card]

/-- A nonnegative signed power is the corresponding ordinary residue-cardinal iterate. -/
theorem frobenius_natCast_apply (n : ℕ) (x : κ) :
    (frobenius K κ ^ (n : ℤ)) x = x ^ (Nat.card 𝓀[K] ^ n) := by
  have h : ⇑(frobenius K κ) = (· ^ Nat.card 𝓀[K]) := funext (frobenius_apply K κ)
  rw [zpow_natCast, AlgEquiv.coe_pow, h, pow_iterate]

omit [Algebra.IsAlgebraic 𝓀[K] κ] [Algebra 𝒪[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ] in
/-- The actual scalar residue cardinal is a positive power of the characteristic of the frame field. -/
theorem exists_expChar_card :
    ∃ (p : ℕ) (f : ℕ+), p.Prime ∧ ExpChar κ p ∧ Nat.card 𝓀[K] = p ^ (f : ℕ) := by
  obtain ⟨p, hpchar, f, hp, hf⟩ := FiniteField.card' 𝓀[K]
  let : CharP 𝓀[K] p := hpchar
  let : CharP κ p := charP_of_injective_algebraMap (algebraMap 𝓀[K] κ).injective p
  exact ⟨p, f, hp, ExpChar.prime hp, (Nat.card_eq_fintype_card (α := 𝓀[K])).trans hf⟩

/-- The nonnegative residue Frobenius has the actual coefficient ring map for relative Frobenius. -/
theorem frobenius_natCast_toRingHom (p : ℕ) [ExpChar κ p] {f : ℕ}
    (hcard : Nat.card 𝓀[K] = p ^ f) (n : ℕ) :
    (frobenius K κ ^ (n : ℤ)).toAlgHom.toRingHom = iterateFrobenius κ p (f * n) := by
  ext x
  change (frobenius K κ ^ (n : ℤ)) x = x ^ (p ^ (f * n))
  rw [frobenius_natCast_apply, hcard, pow_mul]

variable {K κ}
variable {S : Type w} [CommRing S] [Algebra 𝒪[K] S]
variable {T : Type z} [CommRing T] [Algebra 𝒪[K] T]

/-- Drinfeld's residue shift precomposes the actual residue map by inverse Frobenius. -/
def shift (n : ℤ) (ψ : κ →ₐ[𝒪[K]] S) : κ →ₐ[𝒪[K]] S :=
  ψ.comp (frobenius K κ ^ (-n)).toAlgHom

/-- Frobenius with signed exponent `n` takes the shifted frame coefficients back to `ψ`. -/
theorem shift_comp_frobenius (n : ℤ) (ψ : κ →ₐ[𝒪[K]] S) :
    (shift n ψ).comp (frobenius K κ ^ n).toAlgHom = ψ := by
  ext x
  change ψ ((frobenius K κ ^ (-n)) ((frobenius K κ ^ n) x)) = ψ x
  rw [← AlgEquiv.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero, AlgEquiv.one_apply]

@[simp]
theorem shift_zero (ψ : κ →ₐ[𝒪[K]] S) : shift 0 ψ = ψ := by
  ext x
  simp only [shift, neg_zero, zpow_zero, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgEquiv.one_apply]

/-- Addition of signed exponents is composition of the actual residue shifts. -/
theorem shift_shift (n m : ℤ) (ψ : κ →ₐ[𝒪[K]] S) :
    shift m (shift n ψ) = shift (n + m) ψ := by
  ext x
  change ψ ((frobenius K κ ^ (-n)) ((frobenius K κ ^ (-m)) x)) =
    ψ ((frobenius K κ ^ (-(n + m))) x)
  rw [neg_add, zpow_add, AlgEquiv.mul_apply]

/-- The same inverse shift commutes with any extension of the target coefficients. -/
theorem comp_shift (a : S →ₐ[𝒪[K]] T) (n : ℤ) (ψ : κ →ₐ[𝒪[K]] S) :
    a.comp (shift n ψ) = shift n (a.comp ψ) := by
  ext x
  rfl

/-- The opposite shift is the inverse on actual residue homomorphisms. -/
def shiftEquiv (n : ℤ) : (κ →ₐ[𝒪[K]] S) ≃ (κ →ₐ[𝒪[K]] S) where
  toFun := shift n
  invFun := shift (-n)
  left_inv ψ := by simpa only [add_neg_cancel, shift_zero] using shift_shift n (-n) ψ
  right_inv ψ := by simpa only [neg_add_cancel, shift_zero] using shift_shift (-n) n ψ

variable (K κ)
variable (R : Type s) [CommRing R] [Algebra 𝒪[K] R] (r : R)

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Signed inverse Frobenius is a natural automorphism of the actual Nilp residue-map functor. -/
def shiftNatIso (n : ℤ) :
    (Nilp.residueMapFunctor 𝒪[K] R r κ : Nilp.{s,w} R r ⥤ Type (max v w)) ≅
      Nilp.residueMapFunctor 𝒪[K] R r κ :=
  NatIso.ofComponents (fun A =>
    (shiftEquiv (K := K) (κ := κ) (S := ((Nilp.reductionFunctor R r).obj A).obj) n).toIso)
    (fun f => by
      apply ConcreteCategory.hom_ext
      intro ψ
      exact (comp_shift (Nilp.reducedScalarMap 𝒪[K] f) n ψ).symm)

/-- The natural automorphism acts by the exact original inverse Frobenius formula. -/
@[simp]
theorem shiftNatIso_hom_app {A : Nilp.{s,w} R r} (n : ℤ)
    (ψ : κ →ₐ[𝒪[K]] ((Nilp.reductionFunctor R r).obj A).obj) :
    (shiftNatIso K κ R r n).hom.app A ψ = shift n ψ := rfl

end Langlands.FormalGroup.LocalDivision.DrinfeldResidue

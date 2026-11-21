import Langlands.Correspondence.HenniartRefinedStrata
import Langlands.Weil.Representation.Determinant
import Langlands.Weil.Representation.RankDeterminantProof
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! # Finite unramified-twist stabilizers -/

noncomputable section

namespace Langlands.Henniart.Numerical

open Correspondence FiniteRepresentation Weil.Local

universe uK uW

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) {k : ℕ}

/-- The actual unramified-twist stabilizer regarded as a subgroup of complex units. -/
def weilTwistStabilizer (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat) : Subgroup ℂˣ where
  carrier := {z | weilUnramifiedTwist K k z σ = σ}
  one_mem' := by
    exact Equiv.congr_fun (continuousIrreducibleUnramifiedTwistEquiv_one
      (localDegree K) (k + 1)) σ
  mul_mem' {z w} hz hw := by
    calc
      weilUnramifiedTwist K k (z * w) σ =
          weilUnramifiedTwist K k z (weilUnramifiedTwist K k w σ) :=
        (Equiv.congr_fun (continuousIrreducibleUnramifiedTwistEquiv_mul
          (localDegree K) z w (k + 1)) σ).symm
      _ = weilUnramifiedTwist K k z σ := congrArg (weilUnramifiedTwist K k z) hw
      _ = σ := hz
  inv_mem' {z} hz := by
    change weilUnramifiedTwist K k z⁻¹ σ = σ
    nth_rw 1 [← show weilUnramifiedTwist K k z σ = σ from hz]
    exact continuousIrreducibleUnramifiedTwistEquiv_inv_apply (localDegree K) z (k + 1) σ

@[simp] theorem mem_weilTwistStabilizer (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat)
    (z : ℂˣ) : z ∈ weilTwistStabilizer K σ ↔ weilUnramifiedTwist K k z σ = σ := Iff.rfl

/-- Evaluating the determinant at a degree-one lift bounds the whole stabilizer. -/
theorem weilTwistStabilizer_le_rootsOfUnity
    (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat) :
    weilTwistStabilizer K σ ≤ rootsOfUnity (k + 1) ℂ := by
  intro z hz
  obtain ⟨A, hA⟩ := Quotient.exists_rep σ.val
  have hrank : A.val.rank = k + 1 := by
    exact (congrArg (fun c => classRank (forgetPropertyClass _ c)) hA).trans σ.property
  let χ := unramifiedCharacter (localDegree K) z
  have h : twistClass χ.toMonoidHom (forgetPropertyClass _ σ.val) =
      forgetPropertyClass _ σ.val :=
    (forget_continuousIrreducibleTwistEquiv χ (k + 1) σ).symm.trans
      (congrArg (fun c => forgetPropertyClass _ c.val) ((mem_weilTwistStabilizer K σ z).mp hz))
  rw [← hA] at h
  change classOf (FiniteRepresentation.twist χ.toMonoidHom A.val) = classOf A.val at h
  obtain ⟨e⟩ := (classOf_eq_iff _ _).mp h
  let φ := localGeometricFrobenius K
  have hd := congrArg (fun χ : localWeilGroup K →* ℂˣ => (χ φ : ℂ)) (determinantCharacter_eq e)
  change LinearMap.det (Langlands.twist χ.toMonoidHom A.val.representation φ) =
    LinearMap.det (A.val.representation φ) at hd
  rw [det_twist] at hd
  have hφ : unramifiedCharacter (localDegree K) z φ = z :=
    unramifiedCharacter_degree_one _ _ (localGeometricFrobenius_degree K)
  change ((unramifiedCharacter (localDegree K) z φ : ℂ) ^ A.val.rank) *
    LinearMap.det (A.val.representation φ) = _ at hd
  rw [hφ, hrank] at hd
  have hne : LinearMap.det (A.val.representation φ) ≠ 0 :=
    (determinantCharacter A.val φ).ne_zero
  have hz₀ : (z : ℂ) ^ (k + 1) = 1 :=
    mul_right_cancel₀ hne (by simpa only [one_mul] using hd)
  exact Units.ext (by simpa using hz₀)

instance finite_weilTwistStabilizer (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat) :
    Finite (weilTwistStabilizer K σ) :=
  Finite.of_injective _ (Subgroup.inclusion_injective (weilTwistStabilizer_le_rootsOfUnity K σ))

/-- The twist stabilizer has positive order and that order divides the rank. -/
theorem weilTorsionNumber_pos_dvd_rank (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat) :
    0 < weilTorsionNumber K σ ∧ weilTorsionNumber K σ ∣ k + 1 := by
  let S := weilTwistStabilizer K σ
  have h := weilTwistStabilizer_le_rootsOfUnity K σ
  have hcard := Subgroup.card_dvd_of_le h
  rw [Complex.card_rootsOfUnity] at hcard
  exact ⟨Nat.card_pos (α := S), hcard⟩

/-- A subgroup of complex units of finite order `f` is exactly the group of `f`th roots. -/
theorem weilTwistStabilizer_eq_rootsOfUnity
    (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat) :
    weilTwistStabilizer K σ = rootsOfUnity (weilTorsionNumber K σ) ℂ := by
  have hn : 0 < weilTorsionNumber K σ := (weilTorsionNumber_pos_dvd_rank K σ).1
  let : NeZero (weilTorsionNumber K σ) := ⟨hn.ne'⟩
  have hle : weilTwistStabilizer K σ ≤ rootsOfUnity (weilTorsionNumber K σ) ℂ := by
    intro z hz
    change z ^ Nat.card (weilTwistStabilizer K σ) = 1
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨z, hz⟩ : weilTwistStabilizer K σ)))
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [Complex.card_rootsOfUnity]; rfl)

end Langlands.Henniart.Numerical

import Langlands.HarmonicAnalysis.Distribution.GeneralLinear
import Langlands.Representation.Whittaker.GeneralLinear

/-! # Whittaker bi-equivariant distributions and Weyl-conjugated transpose -/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis
open HarmonicAnalysis.Distribution Hecke.TestFunction

universe uR uF

variable (n : ℕ) (R : Type uR) [CommRing R] [TopologicalSpace R]
variable [IsTopologicalRing R]

/-- The actual involution `g ↦ w * gᵀ * w` in positive rank `n + 1`. -/
def weylTransposeHomeomorph : GeneralLinear (n + 1) R ≃ₜ GeneralLinear (n + 1) R :=
  (transposeHomeomorph (n + 1) R).trans
    (conjugationHomeomorph (weylLong (n + 1) R))

@[simp] theorem weylTransposeHomeomorph_apply (g : GeneralLinear (n + 1) R) :
    weylTransposeHomeomorph n R g =
      weylLong (n + 1) R * transposeHomeomorph (n + 1) R g * weylLong (n + 1) R := by
  simp [weylTransposeHomeomorph]

/-- Reverse both indices and interchange them. -/
@[simp] theorem weylTransposeHomeomorph_entry (g : GeneralLinear (n + 1) R)
    (i j : Fin (n + 1)) : weylTransposeHomeomorph n R g i j = g j.rev i.rev := by
  rw [weylTransposeHomeomorph_apply, weylLong_conjugate_entry,
    transposeHomeomorph_entry]

@[simp] theorem weylTransposeHomeomorph_involutive (g : GeneralLinear (n + 1) R) :
    weylTransposeHomeomorph n R (weylTransposeHomeomorph n R g) = g := by
  apply Units.ext
  ext i j
  simp only [weylTransposeHomeomorph_entry, Fin.rev_rev]

/-- Weyl-conjugated transpose reverses multiplication. -/
theorem weylTransposeHomeomorph_mul (g h : GeneralLinear (n + 1) R) :
    weylTransposeHomeomorph n R (g * h) =
      weylTransposeHomeomorph n R h * weylTransposeHomeomorph n R g := by
  simp only [weylTransposeHomeomorph_apply, transposeHomeomorph_mul]
  simp only [mul_assoc, ← mul_assoc (weylLong (n + 1) R) (weylLong (n + 1) R),
    weylLong_mul_self, one_mul]

/-- In rank one this homeomorphism is the identity. -/
@[simp] theorem weylTransposeHomeomorph_rankOne (g : GeneralLinear 1 R) :
    weylTransposeHomeomorph 0 R g = g := by
  apply Units.ext
  ext i j
  have h (a b : Fin (0 + 1)) : a = b := Fin.ext (by omega)
  rw [weylTransposeHomeomorph_entry, h j.rev i, h i.rev j]

/-- Upper unipotence is preserved, including over rings with zero divisors. -/
theorem weylTransposeHomeomorph_mem_upperUnipotent
    {g : GeneralLinear (n + 1) R} (hg : g ∈ upperUnipotent (n + 1) R) :
    weylTransposeHomeomorph n R g ∈ upperUnipotent (n + 1) R := by
  constructor
  · intro i j hji
    rw [weylTransposeHomeomorph_entry]
    exact hg.1 (Fin.rev_lt_rev.mpr hji)
  · intro i
    rw [weylTransposeHomeomorph_entry]
    exact hg.2 i.rev

/-- The same involution on the actual upper-unipotent subgroup. -/
def weylTransposeUnipotent :
    upperUnipotent (n + 1) R ≃ₜ upperUnipotent (n + 1) R where
  toFun u := ⟨weylTransposeHomeomorph n R u.val,
    weylTransposeHomeomorph_mem_upperUnipotent n R u.property⟩
  invFun u := ⟨weylTransposeHomeomorph n R u.val,
    weylTransposeHomeomorph_mem_upperUnipotent n R u.property⟩
  left_inv u := Subtype.ext (weylTransposeHomeomorph_involutive n R u.val)
  right_inv u := Subtype.ext (weylTransposeHomeomorph_involutive n R u.val)
  continuous_toFun := ((weylTransposeHomeomorph n R).continuous.comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := ((weylTransposeHomeomorph n R).continuous.comp
    continuous_subtype_val).subtype_mk _

@[simp] theorem weylTransposeUnipotent_val (u : upperUnipotent (n + 1) R) :
    (weylTransposeUnipotent n R u).val = weylTransposeHomeomorph n R u.val := rfl

@[simp] theorem weylTransposeUnipotent_involutive (u : upperUnipotent (n + 1) R) :
    weylTransposeUnipotent n R (weylTransposeUnipotent n R u) = u :=
  (weylTransposeUnipotent n R).left_inv u

/-- The adjacent entry indexed by `i` becomes the adjacent entry indexed by `i.rev`. -/
theorem weylTransposeUnipotent_adjacent_entry (u : upperUnipotent (n + 1) R)
    (i : Fin n) :
    (weylTransposeUnipotent n R u).val i.castSucc i.succ =
      u.val i.rev.castSucc i.rev.succ := by
  simp only [weylTransposeUnipotent_val, weylTransposeHomeomorph_entry,
    Fin.rev_succ, Fin.rev_castSucc]

/-- Reversing the adjacent indices preserves their sum, also when the sum is empty. -/
theorem weylTransposeUnipotent_superdiagonalSum (u : upperUnipotent (n + 1) R) :
    (∑ i : Fin n, (weylTransposeUnipotent n R u).val i.castSucc i.succ) =
      ∑ i : Fin n, u.val i.castSucc i.succ := by
  simp only [weylTransposeUnipotent_adjacent_entry]
  exact Equiv.sum_comp Fin.revPerm (fun i : Fin n => u.val i.castSucc i.succ)

@[simp] theorem standardCharacter_weylTranspose (ψ : UnitaryAdditiveCharacter R)
    (u : upperUnipotent (n + 1) R) :
    standardCharacter ψ n (weylTransposeUnipotent n R u) = standardCharacter ψ n u := by
  apply Units.ext
  simp only [standardCharacter_apply, weylTransposeUnipotent_superdiagonalSum]

/-- The specified left/right translations evaluate as `f (u₁ * g * u₂)`. -/
theorem biTranslate_apply (u₁ u₂ : upperUnipotent (n + 1) R)
    (f : SchwartzBruhat (GeneralLinear (n + 1) R)) (g : GeneralLinear (n + 1) R) :
    leftTranslate u₁.val⁻¹ (rightTranslate u₂.val f) g = f (u₁.val * g * u₂.val) := by
  simp only [leftTranslate_apply, rightTranslate_apply, inv_inv]

/-- Pullback and translation presentations are the same actual test function. -/
theorem biTranslate_eq_pullback (u₁ u₂ : upperUnipotent (n + 1) R)
    (f : SchwartzBruhat (GeneralLinear (n + 1) R)) :
    leftTranslate u₁.val⁻¹ (rightTranslate u₂.val f) =
      pullback ((Homeomorph.mulLeft u₁.val).trans (Homeomorph.mulRight u₂.val)) f := by
  ext g
  exact biTranslate_apply n R u₁ u₂ f g

variable {R} in
/-- Whittaker bi-equivariance with the test-function convention of Shalika, Proposition 1.8. -/
def IsBiEquivariantDistribution (ψ : UnitaryAdditiveCharacter R) (n : ℕ)
    (D : Distribution (GeneralLinear (n + 1) R)) : Prop :=
  ∀ (u₁ u₂ : upperUnipotent (n + 1) R) (f : SchwartzBruhat (GeneralLinear (n + 1) R)),
    D (leftTranslate u₁.val⁻¹ (rightTranslate u₂.val f)) =
      ((standardCharacter ψ n u₁ : ℂ) * (standardCharacter ψ n u₂ : ℂ)) * D f

/-- Equivalent evaluation on pullback by `g ↦ u₁ * g * u₂`. -/
theorem isBiEquivariantDistribution_iff (ψ : UnitaryAdditiveCharacter R)
    (D : Distribution (GeneralLinear (n + 1) R)) :
    IsBiEquivariantDistribution ψ n D ↔
      ∀ (u₁ u₂ : upperUnipotent (n + 1) R)
        (f : SchwartzBruhat (GeneralLinear (n + 1) R)),
        D (pullback ((Homeomorph.mulLeft u₁.val).trans (Homeomorph.mulRight u₂.val)) f) =
          ((standardCharacter ψ n u₁ : ℂ) * (standardCharacter ψ n u₂ : ℂ)) * D f := by
  simp only [IsBiEquivariantDistribution, biTranslate_eq_pullback]

/-- Invariance under the actual distribution pushforward by Weyl-conjugated transpose. -/
def IsWeylTransposeInvariant (D : Distribution (GeneralLinear (n + 1) R)) : Prop :=
  pushforward (weylTransposeHomeomorph n R) D = D

theorem isWeylTransposeInvariant_iff (D : Distribution (GeneralLinear (n + 1) R)) :
    IsWeylTransposeInvariant n R D ↔
      ∀ f : SchwartzBruhat (GeneralLinear (n + 1) R),
        D (pullback (weylTransposeHomeomorph n R) f) = D f := by
  constructor
  · intro h f
    exact congrArg (fun E : Distribution (GeneralLinear (n + 1) R) => E f) h
  · intro h
    ext f
    exact h f

@[simp] theorem pushforward_weylTranspose_involutive
    (D : Distribution (GeneralLinear (n + 1) R)) :
    pushforward (weylTransposeHomeomorph n R)
      (pushforward (weylTransposeHomeomorph n R) D) = D := by
  rw [← pushforward_trans]
  have he : (weylTransposeHomeomorph n R).trans (weylTransposeHomeomorph n R) =
      Homeomorph.refl _ := by
    apply Homeomorph.ext
    intro g
    exact weylTransposeHomeomorph_involutive n R g
  rw [he, pushforward_refl]

/-- Specialization uses the existing canonical topology in an arbitrary field universe. -/
example {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (n : ℕ) :
    letI := F.canonicalNormedField
    GeneralLinear (n + 1) F.Carrier ≃ₜ GeneralLinear (n + 1) F.Carrier := by
  letI := F.canonicalNormedField
  exact weylTransposeHomeomorph n F.Carrier

end Langlands.Whittaker

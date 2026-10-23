import Langlands.Representation.Shahidi.Geometry
import Langlands.Representation.Whittaker.GeneralLinear

/-! # The standard Whittaker character on Shahidi's rectangular radicals -/

noncomputable section

namespace Langlands.Shahidi

open GeneralLinear HarmonicAnalysis

universe u

variable (m n : ℕ) (R : Type u) [CommRing R]

theorem upper_mem_upperUnipotent (a : Matrix (Fin m) (Fin n) R) :
    upper m n R a ∈ upperUnipotent (m + n) R := by
  constructor
  · intro i j hij
    induction i using Fin.addCases <;> induction j using Fin.addCases
    · rw [upper_first_first]
      apply ite_eq_right
      intro he
      subst he
      exact (lt_irrefl _ hij)
    · simp only [id_eq, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd] at hij
      omega
    · exact upper_second_first m n R a _ _
    · rw [upper_second_second]
      apply ite_eq_right
      intro he
      subst he
      exact (lt_irrefl _ hij)
  · intro i
    induction i using Fin.addCases <;> simp

theorem swapRank_mem_upperUnipotent
    {g : Langlands.GeneralLinear (n + m) R}
    (hg : g ∈ upperUnipotent (n + m) R) :
    swapRank m n R g ∈ upperUnipotent (m + n) R := by
  constructor
  · intro i j hij
    change g (Fin.cast (Nat.add_comm m n) i) (Fin.cast (Nat.add_comm m n) j) = 0
    exact hg.1 (by simpa only [id_eq, Fin.lt_def, Fin.val_cast] using hij)
  · intro i
    exact hg.2 (Fin.cast (Nat.add_comm m n) i)

theorem intertwiningUnipotent_mem_upperUnipotent
    (a : Matrix (Fin n) (Fin m) R) :
    intertwiningUnipotent m n R a ∈ upperUnipotent (m + n) R :=
  swapRank_mem_upperUnipotent m n R (upper_mem_upperUnipotent n m R a)

/-- The original radical coordinates mapped into the full upper unipotent group. -/
def upperToUnipotent :
    Multiplicative (Matrix (Fin m) (Fin n) R) →* upperUnipotent (m + n) R :=
  (upperHom m n R).codRestrict _ (fun a => upper_mem_upperUnipotent m n R a.toAdd)

/-- The exchanged radical coordinates mapped into the same full upper unipotent group. -/
def intertwiningToUnipotent :
    Multiplicative (Matrix (Fin n) (Fin m) R) →* upperUnipotent (m + n) R :=
  (intertwiningHom m n R).codRestrict _
    (fun a => intertwiningUnipotent_mem_upperUnipotent m n R a.toAdd)

section Characters

variable {F : Type u} [CommRing F] [TopologicalSpace F]
variable (ψ : UnitaryAdditiveCharacter F)

/-- The source's character on `U` at positive ranks `m+1,n+1`. -/
def upperCharacter :
    Multiplicative (Matrix (Fin (m + 1)) (Fin (n + 1)) F) →* ℂˣ :=
  (Whittaker.standardCharacter ψ (m + 1 + n)).comp
    (upperToUnipotent (m + 1) (n + 1) F)

/-- The source's character on `U'`, with the exchanged rectangular coordinates. -/
def intertwiningCharacter :
    Multiplicative (Matrix (Fin (n + 1)) (Fin (m + 1)) F) →* ℂˣ :=
  (Whittaker.standardCharacter ψ (m + 1 + n)).comp
    (intertwiningToUnipotent (m + 1) (n + 1) F)

@[simp] theorem upperCharacter_apply
    (a : Matrix (Fin (m + 1)) (Fin (n + 1)) F) :
    (upperCharacter m n ψ (Multiplicative.ofAdd a) : ℂ) =
      ψ.complex (∑ i : Fin (m + 1 + n),
        upper (m + 1) (n + 1) F a i.castSucc i.succ) := rfl

@[simp] theorem intertwiningCharacter_apply
    (a : Matrix (Fin (n + 1)) (Fin (m + 1)) F) :
    (intertwiningCharacter m n ψ (Multiplicative.ofAdd a) : ℂ) =
      ψ.complex (∑ i : Fin (m + 1 + n),
        intertwiningUnipotent (m + 1) (n + 1) F a i.castSucc i.succ) := rfl

@[simp] theorem norm_upperCharacter
    (a : Matrix (Fin (m + 1)) (Fin (n + 1)) F) :
    ‖(upperCharacter m n ψ (Multiplicative.ofAdd a) : ℂ)‖ = 1 := by
  simp

@[simp] theorem norm_intertwiningCharacter
    (a : Matrix (Fin (n + 1)) (Fin (m + 1)) F) :
    ‖(intertwiningCharacter m n ψ (Multiplicative.ofAdd a) : ℂ)‖ = 1 := by
  simp

/-- The conjugate-character factor for the swapped Jacquet functional on `U`. -/
def upperJacquetKernel (a : Matrix (Fin (m + 1)) (Fin (n + 1)) F) : ℂ :=
  starRingEnd ℂ (upperCharacter m n ψ (Multiplicative.ofAdd a) : ℂ)

/-- The conjugate-character factor in the source Jacquet functional on `U'`. -/
def intertwiningJacquetKernel (a : Matrix (Fin (n + 1)) (Fin (m + 1)) F) : ℂ :=
  starRingEnd ℂ (intertwiningCharacter m n ψ (Multiplicative.ofAdd a) : ℂ)

theorem upperJacquetKernel_eq_inv
    (a : Matrix (Fin (m + 1)) (Fin (n + 1)) F) :
    upperJacquetKernel m n ψ a =
      (upperCharacter m n ψ (Multiplicative.ofAdd a) : ℂ)⁻¹ :=
  (Complex.inv_eq_conj (norm_upperCharacter m n ψ a)).symm

theorem intertwiningJacquetKernel_eq_inv
    (a : Matrix (Fin (n + 1)) (Fin (m + 1)) F) :
    intertwiningJacquetKernel m n ψ a =
      (intertwiningCharacter m n ψ (Multiplicative.ofAdd a) : ℂ)⁻¹ :=
  (Complex.inv_eq_conj (norm_intertwiningCharacter m n ψ a)).symm

variable [IsTopologicalRing F]

theorem continuous_upperJacquetKernel :
    Continuous (upperJacquetKernel m n ψ) := by
  apply Continuous.star
  apply ψ.continuous_complex.comp
  change Continuous (fun a : Matrix (Fin (m + 1)) (Fin (n + 1)) F =>
    ∑ i : Fin (m + 1 + n), upper (m + 1) (n + 1) F a i.castSucc i.succ)
  apply continuous_finsetSum
  intro i _
  exact (GeneralLinear.entry i.castSucc i.succ).continuous.comp
    (continuous_upper (m + 1) (n + 1) F)

theorem continuous_intertwiningJacquetKernel :
    Continuous (intertwiningJacquetKernel m n ψ) := by
  apply Continuous.star
  apply ψ.continuous_complex.comp
  change Continuous (fun a : Matrix (Fin (n + 1)) (Fin (m + 1)) F =>
    ∑ i : Fin (m + 1 + n),
      intertwiningUnipotent (m + 1) (n + 1) F a i.castSucc i.succ)
  apply continuous_finsetSum
  intro i _
  exact (GeneralLinear.entry i.castSucc i.succ).continuous.comp
    (continuous_intertwiningUnipotent (m + 1) (n + 1) F)

end Characters

end Langlands.Shahidi

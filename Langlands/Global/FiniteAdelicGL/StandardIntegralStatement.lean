import Langlands.Global.AdelicGL
import Langlands.Global.IntegralFiniteAdeles
import Langlands.Group.GL.IntegralSubgroup

/-!
# The standard integral finite adelic matrix subgroup

The subgroup consists of matrix units integral in both directions at every
finite place. Compactness is stated here as a separate proposition target.
-/

noncomputable section

universe u

namespace Langlands.Global.FiniteAdelicGL

open NumberField IsDedekindDomain

variable (K : Type u) [Field K] [NumberField K]

variable (n : ℕ)

/-- Matrices whose entries are integral finite adeles, as a multiplicative submonoid. -/
def integralMatrices :
    Submonoid (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) :=
  ((integralAdeles K).matrix (n := Fin n)).toSubmonoid

@[simp]
theorem mem_integralMatrices
    (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) :
    A ∈ integralMatrices K n ↔ ∀ i j, A i j ∈ integralAdeles K :=
  Iff.rfl

theorem mem_integralMatrices_iff
    (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) :
    A ∈ integralMatrices K n ↔
      ∀ i j (v : HeightOneSpectrum (𝓞 K)), A i j v ∈ v.adicCompletionIntegers K :=
  Iff.rfl

/-- The matrix carrier is two finite products of the integral-adele carrier. -/
theorem integralMatrices_eq_pi :
    (integralMatrices K n : Set (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K))) =
      Set.pi Set.univ (fun _ : Fin n =>
        Set.pi Set.univ (fun _ : Fin n =>
          (integralAdeles K : Set (FiniteAdeleRing (𝓞 K) K)))) := by
  ext A
  change (∀ i j, A i j ∈ integralAdeles K) ↔
    ∀ i ∈ (Set.univ : Set (Fin n)), ∀ j ∈ (Set.univ : Set (Fin n)),
      A i j ∈ integralAdeles K
  simp only [Set.mem_univ, forall_const]

theorem mem_integralMatrices_pi
    (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) :
    A ∈ integralMatrices K n ↔
      A ∈ Set.pi Set.univ (fun _ : Fin n =>
        Set.pi Set.univ (fun _ : Fin n =>
          (integralAdeles K : Set (FiniteAdeleRing (𝓞 K) K)))) := by
  rw [← integralMatrices_eq_pi K n]
  rfl

/-- The standard integral subgroup, with the inherited matrix-units topology. -/
def standardIntegral : OpenSubgroup (Langlands.Global.FiniteAdelicGL K n) :=
  Langlands.GeneralLinearGroup.integralOpenSubgroup
    (Fin n) (integralAdeles K) (isOpen_integralAdeles K)

theorem standardIntegral_toSubgroup :
    (standardIntegral K n).toSubgroup = (integralMatrices K n).units :=
  rfl

theorem mem_standardIntegral_iff (g : Langlands.Global.FiniteAdelicGL K n) :
    g ∈ standardIntegral K n ↔
      g.val ∈ integralMatrices K n ∧ g.inv ∈ integralMatrices K n :=
  Iff.rfl

@[simp]
theorem mem_standardIntegral (g : Langlands.Global.FiniteAdelicGL K n) :
    g ∈ standardIntegral K n ↔
      (∀ i j (v : HeightOneSpectrum (𝓞 K)), g i j v ∈ v.adicCompletionIntegers K) ∧
      (∀ i j (v : HeightOneSpectrum (𝓞 K)), g⁻¹ i j v ∈ v.adicCompletionIntegers K) :=
  Iff.rfl

@[simp]
theorem standardIntegral_zero : standardIntegral K 0 = ⊤ := by
  ext g
  simp

/-- Compactness of the actual standard integral subgroup in every natural rank. -/
def StandardIntegralCompactStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ),
    IsCompact (standardIntegral K n : Set (Langlands.Global.FiniteAdelicGL K n))

end Langlands.Global.FiniteAdelicGL

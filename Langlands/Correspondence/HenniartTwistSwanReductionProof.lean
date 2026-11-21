import Langlands.Correspondence.HenniartTwistSwanReductionStatement

/-! # Proof of the reduction of the supercuspidal twist Swan bound -/

noncomputable section

namespace Langlands.Henniart

open Langlands.Correspondence

universe uK uV

local instance twistSwanFieldTopology {p : ℕ} [Fact p.Prime] (K : PadicField p) :
    TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

local instance twistSwanGLTopology {p : ℕ} [Fact p.Prime] (K : PadicField p) (n : ℕ) :
    TopologicalSpace (GeneralLinear n K.Carrier) :=
  K.canonicalGeneralLinearTopology n

private theorem supercuspidalToAutomorphic_characterTwist {p : ℕ} [Fact p.Prime]
    (K : PadicField.{uK} p) (k : ℕ) (χ : QuasiCharacter K)
    (π : SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat) :
    supercuspidalToAutomorphic K (Numerical.supercuspidalCharacterTwist K k χ π) =
      SmoothDualClass.twist (χ.toMonoidHom.comp (GeneralLinear.determinant (n := k + 1)))
        (BushnellKutzko.isOpen_ker_determinantCharacter K (k + 1) χ)
        (supercuspidalToAutomorphic K π) :=
  GeneralLinear.SupercuspidalClass.toSmoothDualClass_twist _ _ _ π

/-- L0, L2 and T2 imply the Swan bound for twists of supercuspidal classes. -/
theorem supercuspidalTwistSwanBoundReduction :
    SupercuspidalTwistSwanBoundReductionStatement.{uK, uV} := by
  intro hL0 hL2 hT2 p _ K k χ π s hs
  have hrank : 1 ≤ k + 1 := Nat.succ_pos k
  obtain ⟨x, hx⟩ := hL0 p K (k + 1) hrank (supercuspidalToAutomorphic K π)
  obtain ⟨y, hy⟩ := hL0 p K (k + 1) hrank
    (supercuspidalToAutomorphic K (Numerical.supercuspidalCharacterTwist K k χ π))
  obtain ⟨c, hc, hcx⟩ := hT2 p K k π x hx
  obtain ⟨c', hc', hcy⟩ := hT2 p K k _ y hy
  obtain ⟨a, ha, has⟩ := hs
  have hac : a = c := WithTop.coe_injective (ha.symm.trans hc)
  rw [hac] at has
  have hsx : (s : ℚ) = ((k + 1 : ℕ) : ℚ) * x := by
    rw [← has]
    exact hcx
  rw [supercuspidalToAutomorphic_characterTwist] at hy
  let t := Numerical.characterSwanExponent K χ
  obtain ⟨hlevelLe, hlevelEq⟩ := hL2 p K (k + 1) hrank χ t rfl _ x y hx hy
  have hn : (0 : ℚ) ≤ ((k + 1 : ℕ) : ℚ) := Nat.cast_nonneg _
  have hmax :
      ((max s ((k + 1) * t) : ℕ) : ℚ) = ((k + 1 : ℕ) : ℚ) * max x (t : ℚ) := by
    rw [Nat.cast_max, Nat.cast_mul, hsx, mul_max_of_nonneg _ _ hn]
  refine ⟨c' - (k + 1), ⟨c', hc', rfl⟩, ?_, ?_⟩
  · have hle : ((c' - (k + 1) : ℕ) : ℚ) ≤ ((max s ((k + 1) * t) : ℕ) : ℚ) := by
      rw [hcy, hmax]
      exact mul_le_mul_of_nonneg_left hlevelLe hn
    exact_mod_cast hle
  · intro hne
    have hxt : x ≠ (t : ℚ) := by
      intro heq
      apply hne
      have hst : (s : ℚ) = (((k + 1) * t : ℕ) : ℚ) := by
        rw [hsx, heq, Nat.cast_mul]
      exact_mod_cast hst
    have heq : ((c' - (k + 1) : ℕ) : ℚ) = ((max s ((k + 1) * t) : ℕ) : ℚ) := by
      rw [hcy, hmax, hlevelEq hxt]
    exact_mod_cast heq

end Langlands.Henniart

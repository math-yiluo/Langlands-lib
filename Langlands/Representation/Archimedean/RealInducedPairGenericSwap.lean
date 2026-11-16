import Langlands.Representation.Archimedean.RealInducedPairIntertwiner
import Langlands.Representation.Archimedean.RealInducedPairKTypeTransport
import Langlands.Representation.Archimedean.RealBlockMultiplierGeneric

/-!
# Generic exchange of two real induction blocks

Nonvanishing of the four multipliers gives injectivity. Compact type counting
then gives a bijective exact intertwiner and a one-piece adjacent filtration.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

set_option backward.isDefEq.respectTransparency false

namespace RealInducedPairGenericSwap

open RealBlockFrobeniusMap RealBlockMultiplier RealSwapLandingMirror
open RealInducedPairFrobenius RealStandardFiltration

/-- Nonvanishing on the actual parity class makes a Frobenius map injective. -/
theorem blockFrobMap_injective {n : ℕ} {ds es : List RealBlock} {p : ℕ}
    {ε : ℤ} {σ : ℂ} {μ : ℤ → ℂ} (h : IsBlockFrobData n ds es p ε σ μ)
    (hμ : ∀ k : ℤ, Even (k - ε) → μ k ≠ 0) :
    Function.Injective (blockFrobMap h) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf => ?_
  refine eq_of_blockFourierCoefficient_eq h.lt fun j x hx => ?_
  rw [ZeroMemClass.coe_zero, RealBlockJacquet.blockFourierCoefficient_zero_fun]
  by_cases hj : Even (j - ε)
  · have heq := blockFourierCoefficient_blockFrobMap h f hx j
    rw [hf, ZeroMemClass.coe_zero, RealBlockJacquet.blockFourierCoefficient_zero_fun] at heq
    exact (mul_eq_zero.mp heq.symm).resolve_left (hμ j hj)
  · exact RealBlockJacquet.blockFourierCoefficient_eq_zero_of_not_even h.lt h.par f hj x

/-- The four nonvanishing conditions needed for the full-character crossings. -/
def Nonvanishing (d e : ComplexCharacterData) (μ₁ μ₀ μ₂ μ₃ : ℤ → ℂ) : Prop :=
  (∀ k : ℤ, Even (k - ((e.weight.natAbs + 1 : ℕ) : ℤ)) → μ₁ k ≠ 0) ∧
  (∀ k : ℤ, Even (k - ((d.weight.natAbs + e.weight.natAbs + 2 : ℕ) : ℤ)) → μ₀ k ≠ 0) ∧
  (∀ k : ℤ, Even (k - 0) → μ₂ k ≠ 0) ∧
  (∀ k : ℤ, Even (k - ((d.weight.natAbs + 1 : ℕ) : ℤ)) → μ₃ k ≠ 0)

theorem swap_injective {d e : ComplexCharacterData} {δ : ℂ}
    {μ₁ μ₀ μ₂ μ₃ : ℤ → ℂ} (h : MultiplierData d e δ μ₁ μ₀ μ₂ μ₃)
    (hμ : Nonvanishing d e μ₁ μ₀ μ₂ μ₃) : Function.Injective h.swap := by
  have h1 : Function.Injective h.to1 :=
    (blockFrobMap_injective h.data1 hμ.1).comp (Submodule.inclusion_injective _)
  have h0 : Function.Injective h.to10 :=
    (blockFrobMap_injective h.data0 hμ.2.1).comp h1
  have h2 : Function.Injective h.to3 :=
    (blockFrobMap_injective h.data20 hμ.2.2.1).comp h0
  have h3 : Function.Injective h.to4 :=
    (blockFrobMap_injective h.data3 hμ.2.2.2).comp h2
  intro f g hfg
  apply h3
  apply Subtype.ext
  exact congrArg (fun z : RealInducedPairFrobenius.KF (dst d e) =>
    (z : Langlands.GeneralLinear 4 ℝ → ℂ)) hfg

/-- At the actual exponent parameter, nonvanishing gives a bijective exact intertwiner. -/
theorem swap_bijective {d e : ComplexCharacterData} {μ₁ μ₀ μ₂ μ₃ : ℤ → ℂ}
    (h : MultiplierData d e (swapParameter d e) μ₁ μ₀ μ₂ μ₃)
    (hμ : Nonvanishing d e μ₁ μ₀ μ₂ μ₃) : Function.Bijective h.swap :=
  ⟨swap_injective h hμ, RealInducedPairKTypeTransport.surjective_of_injective d e
    (h.swap_isRealIntertwinerModulo ⊥).isRealKEquivariant (swap_injective h hμ)⟩

/-- The four actual exponent differences avoid their rank-one singular sets.
The parity representatives are reduced to zero or one. -/
def IsGenericPair (d e : ComplexCharacterData) : Prop :=
  IsGenericParameter (swapParameter d e - 1) (((e.weight.natAbs + 1) % 2 : ℕ) : ℤ) ∧
  IsGenericParameter (swapParameter d e - 1 + (d.weight.natAbs : ℂ))
    (((d.weight.natAbs + e.weight.natAbs + 2) % 2 : ℕ) : ℤ) ∧
  IsGenericParameter (swapParameter d e - 1 + (e.weight.natAbs : ℂ)) 0 ∧
  IsGenericParameter
    (swapParameter d e - 1 + (d.weight.natAbs : ℂ) + (e.weight.natAbs : ℂ))
    (((d.weight.natAbs + 1) % 2 : ℕ) : ℤ)

/-- Transfer a generic multiplier from a reduced parity representative. -/
theorem exists_multiplier {ν : ℂ} (ε : ℕ)
    (hν : IsGenericParameter ν ((ε % 2 : ℕ) : ℤ)) :
    ∃ μ : ℤ → ℂ, IsRecurrent (ν + 1) (ε : ℤ) μ ∧
      IsSymmetric (ε : ℤ) ((-1 : ℂ) ^ ε) μ ∧
      ∀ k : ℤ, Even (k - (ε : ℤ)) → μ k ≠ 0 := by
  have hε : ((ε % 2 : ℕ) : ℤ) = 0 ∨ ((ε % 2 : ℕ) : ℤ) = 1 := by omega
  obtain ⟨μ, hr, hs, hn⟩ := hν.exists_generic hε
  have heven : Even (((ε % 2 : ℕ) : ℤ) - (ε : ℤ)) := by
    simpa only [neg_sub] using (even_sub_mod ε).neg
  have hsign : (-1 : ℂ) ^ (((ε % 2 : ℕ) : ℤ).natAbs) = (-1) ^ ε := by
    simp only [Int.natAbs_natCast]
    exact neg_one_pow_congr (by omega)
  refine ⟨μ, isRecurrent_congr hr heven, isSymmetric_congr hs heven hsign, ?_⟩
  intro k hk
  exact hn k (by
    rw [Int.even_iff] at hk ⊢
    omega)

theorem exists_multiplierData {d e : ComplexCharacterData} (h : IsGenericPair d e) :
    ∃ μ₁ μ₀ μ₂ μ₃ : ℤ → ℂ,
      MultiplierData d e (swapParameter d e) μ₁ μ₀ μ₂ μ₃ ∧
      Nonvanishing d e μ₁ μ₀ μ₂ μ₃ := by
  obtain ⟨μ₁, hr1, hs1, hn1⟩ := exists_multiplier (e.weight.natAbs + 1) h.1
  obtain ⟨μ₀, hr0, hs0, hn0⟩ :=
    exists_multiplier (d.weight.natAbs + e.weight.natAbs + 2) h.2.1
  obtain ⟨μ₂, hr2, hs2, hn2⟩ := exists_multiplier 0 h.2.2.1
  obtain ⟨μ₃, hr3, hs3, hn3⟩ := exists_multiplier (d.weight.natAbs + 1) h.2.2.2
  refine ⟨μ₁, μ₀, μ₂, μ₃, ⟨?_, hs1, ?_, hs0, ?_, ?_, ?_, hs3⟩,
    hn1, hn0, hn2, hn3⟩
  · convert hr1 using 1; ring
  · convert hr0 using 1; ring
  · convert hr2 using 1; ring
  · simpa using hs2
  · convert hr3 using 1; ring

/-- Generic pairs admit a bijective exact intertwiner in the displayed direction. -/
theorem exists_bijective_intertwiner {d e : ComplexCharacterData} (h : IsGenericPair d e) :
    ∃ T : RealInducedPairFrobenius.KF (src d e) →ₗ[ℂ]
        RealInducedPairFrobenius.KF (dst d e),
      IsRealIntertwinerModulo 4 (src d e) (dst d e) ⊥ T ∧ Function.Bijective T := by
  obtain ⟨μ₁, μ₀, μ₂, μ₃, hdata, hn⟩ := exists_multiplierData h
  exact ⟨hdata.swap, hdata.swap_isRealIntertwinerModulo ⊥, swap_bijective hdata hn⟩

/-- A bijective exact intertwiner can be inverted within the same intertwining calculus. -/
theorem inverse_intertwiner {d e : ComplexCharacterData}
    {T : RealInducedPairFrobenius.KF (src d e) →ₗ[ℂ]
      RealInducedPairFrobenius.KF (dst d e)}
    (hT : IsRealIntertwinerModulo 4 (src d e) (dst d e) ⊥ T)
    (hTb : Function.Bijective T) :
    IsRealIntertwinerModulo 4 (dst d e) (src d e) ⊥
      (LinearEquiv.ofBijective T hTb).symm.toLinearMap :=
  modulo_of_comp_surjective (modulo_id (src d e)) hT hTb.2
    (LinearMap.ext fun f => (LinearEquiv.ofBijective T hTb).symm_apply_apply f)

/-- The inverse exchange map supplies the one-piece adjacent filtration. -/
theorem filtration {d e : ComplexCharacterData} (h : IsGenericPair d e) :
    RealAdjacentFiltration 4 [] [] (.induced d) (.induced e) := by
  obtain ⟨T, hT, hTb⟩ := exists_bijective_intertwiner h
  let E := LinearEquiv.ofBijective T hTb
  refine (realAdjacentFiltration_iff 4 [] [] _ _).mpr ?_
  refine ((HasFiltration.self (n := 4) (P := fun es => es = dst d e) rfl).map
    E.symm.toLinearMap (inverse_intertwiner hT hTb) E.symm.surjective).mono ?_
  rintro es rfl
  exact ⟨dst d e, rfl, Or.inl rfl⟩

end RealInducedPairGenericSwap

/-- The adjacent filtration for pairs satisfying the four explicit generic conditions. -/
def RealInducedPairGenericFiltrationStatement : Prop :=
  ∀ d e : ComplexCharacterData, RealInducedPairGenericSwap.IsGenericPair d e →
    RealAdjacentFiltration 4 [] [] (.induced d) (.induced e)

theorem realInducedPairGenericFiltration : RealInducedPairGenericFiltrationStatement :=
  fun _ _ h => RealInducedPairGenericSwap.filtration h

end Langlands.Archimedean

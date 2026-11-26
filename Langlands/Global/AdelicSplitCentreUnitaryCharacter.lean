import Langlands.Global.AdelicRestrictionSplitCentreCanonical
import Langlands.Global.AdelicLogSection
import Langlands.Global.AdelicComplexParameters
import Langlands.Global.AdelicSquareIntegrableInducedForms
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Langlands.GroupScheme.Rational.CharacterLatticeProof
import Langlands.Analysis.ContinuousCharacterReal

/-!
# Unitary characters of `A_G`

For a connected reductive group `G` over a number field `F`, the canonical split-centre subgroup
`A_G = RestrictionSplitCentre.canonicalSubgroup F G` of `G(𝔸)` is central, and every continuous
unitary character of `A_G` is `a ↦ a^{iν} = parameterPower F G (imaginaryParameter F G ν) a` for
some `ν ∈ X^*(G) ⊗ ℝ`.

The proof composes the character with the continuous section `PositiveRealTorus.logSection` of
`H_G = characterLog`, whose range is `A_G`, obtaining a continuous unitary character of the real
vector space `Hom(X^*(G), ℝ)`. In the coordinates given by a `ℤ`-basis of the free module
`X^*(G)` each one-parameter restriction is `t ↦ exp(i a t)`
(`ContinuousCharacterReal.exists_eq_exp`), and `ν = ∑ aᵢ ⊗ χᵢ`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme Langlands.Global.AdelicGroupPoints

variable (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- `A_G` is central in `G(𝔸)`. -/
theorem canonicalSubgroup_le_center :
    canonicalSubgroup F G ≤ Subgroup.center (AdelicGroupPoints F G) := by
  have hc : IsCentral (canonicalComponent F G) :=
    (isSplitComponent_canonicalComponent F G).isCentralSplitTorus.isCentral
  rw [canonicalSubgroup_eq_imageSubgroup]
  rintro y ⟨a, ha, rfl⟩
  exact Subgroup.mem_center_iff.mpr fun x => (commute_of_mem_center (hc _ a) x).eq.symm

/-- **Unitary characters of `A_G`.** A continuous function on `G(𝔸)` which is multiplicative and
of modulus one on `A_G` agrees on `A_G` with `a ↦ a^{iν}` for some `ν ∈ X^*(G) ⊗ ℝ`. -/
theorem exists_realParameter_of_unitary (hG : IsConnectedReductive G)
    (c : AdelicGroupPoints F G → ℂ) (hc : Continuous c)
    (hmul : ∀ a ∈ canonicalSubgroup F G, ∀ b ∈ canonicalSubgroup F G, c (a * b) = c a * c b)
    (hnorm : ∀ a ∈ canonicalSubgroup F G, ‖c a‖ = 1) :
    ∃ ν : RealCharacterParameter F G, ∀ a ∈ canonicalSubgroup F G,
      c a = parameterPower F G (imaginaryParameter F G ν) a := by
  classical
  -- the logarithmic section of `A_G`
  obtain ⟨I, hI, ⟨e⟩⟩ := (isSplitComponent_canonicalComponent F G).1.1.1
  have := Fintype.ofFinite I
  have := canonical_finiteIndex F G hG
  have hi := canonical_characterRestrict_injective F G centralSplitTorusCharacter hG
  let s := PositiveRealTorus.logSection F G (canonicalTorus F G) (canonicalComponent F G) hi I e
  have hs_mem (H : RealCharacterDual F G) : s (Multiplicative.ofAdd H) ∈ canonicalSubgroup F G := by
    rw [canonicalSubgroup_eq_imageSubgroup, ← PositiveRealTorus.logSection_range F G _ _ hi I e]
    exact ⟨_, rfl⟩
  have hs_log (a : AdelicGroupPoints F G) (ha : a ∈ canonicalSubgroup F G) :
      s (Multiplicative.ofAdd (characterLog F G a)) = a := by
    rw [canonicalSubgroup_eq_imageSubgroup, ← PositiveRealTorus.logSection_range F G _ _ hi I e]
      at ha
    obtain ⟨x, rfl⟩ := ha
    have h := PositiveRealTorus.characterLogHom_logSection F G _ _ hi I e x
    change Multiplicative.ofAdd (characterLog F G (s x)) = x at h
    change s (Multiplicative.ofAdd (characterLog F G (s x))) = s x
    rw [h]
  -- the character of the real dual
  let ψ : RealCharacterDual F G → ℂ := fun H => c (s (Multiplicative.ofAdd H))
  have hψc : Continuous ψ := hc.comp (s.continuous.comp continuous_ofAdd)
  have hψadd (H H' : RealCharacterDual F G) : ψ (H + H') = ψ H * ψ H' := by
    change c (s (Multiplicative.ofAdd H * Multiplicative.ofAdd H')) = _
    rw [map_mul]
    exact hmul _ (hs_mem H) _ (hs_mem H')
  have hc1 : c 1 = 1 := by
    have h1 := hmul 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
    rw [mul_one] at h1
    have hne : c 1 ≠ 0 := by
      intro h0
      have := hnorm 1 (Subgroup.one_mem _)
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    exact (mul_eq_left₀ hne).mp h1.symm
  have hψ0 : ψ 0 = 1 := by
    change c (s 1) = 1
    rw [map_one, hc1]
  have hψnorm (H : RealCharacterDual F G) : ‖ψ H‖ = 1 := hnorm _ (hs_mem H)
  -- a basis of the free module of rational characters
  obtain ⟨hfree, hfin⟩ := rationalCharacterLattice F G hG
  let Idx := Module.Free.ChooseBasisIndex ℤ (rationalCharacters G)
  let b : Module.Basis Idx ℤ (rationalCharacters G) := Module.Free.chooseBasis ℤ _
  let dual : Idx → RealCharacterDual F G := fun i =>
    (Int.castAddHom ℝ).comp (b.coord i).toAddMonoidHom
  have hdual (i : Idx) (χ : rationalCharacters G) : dual i χ = ((b.repr χ i : ℤ) : ℝ) := rfl
  have hexpand (H : RealCharacterDual F G) : H = ∑ i, H (b i) • dual i := by
    let H' : rationalCharacters G →+ ℝ := H
    apply AddMonoidHom.ext
    intro χ
    have hχ : H' χ = ∑ i, ((b.repr χ i : ℤ) : ℝ) * H' (b i) := by
      conv_lhs => rw [← b.sum_repr χ]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, zsmul_eq_mul]
    change H' χ = dualEval F G χ (∑ i, H (b i) • dual i)
    rw [hχ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    rfl
  -- one-parameter restrictions
  have hone (i : Idx) : ∃ a : ℝ, ∀ t : ℝ,
      ψ (t • dual i) = Complex.exp (((a : ℂ) * Complex.I) * t) := by
    obtain ⟨z, hz⟩ := ContinuousCharacterReal.exists_eq_exp
      (φ := fun t : ℝ => ψ (t • dual i))
      (hψc.comp (continuous_id.smul continuous_const)) (by simp [hψ0])
      (fun u v => by simp only [add_smul, hψadd])
    have hre : z.re = 0 := by
      have h1 := hψnorm ((1 : ℝ) • dual i)
      rw [hz 1, Complex.norm_exp] at h1
      simpa using h1
    refine ⟨z.im, fun t => ?_⟩
    rw [hz t]
    congr 2
    apply Complex.ext <;> simp [hre]
  choose a ha using hone
  refine ⟨∑ i, a i ⊗ₜ[ℤ] b i, fun x hx => ?_⟩
  let Ψ : Multiplicative (RealCharacterDual F G) →* ℂ :=
    { toFun := fun y => ψ y.toAdd
      map_one' := hψ0
      map_mul' := fun y y' => hψadd y.toAdd y'.toAdd }
  set H := characterLog F G x with hH
  have hcx : c x = ψ H := by
    change c x = c (s (Multiplicative.ofAdd (characterLog F G x)))
    rw [hs_log x hx]
  rw [hcx, hexpand H]
  have hprod : ψ (∑ i, H (b i) • dual i) = ∏ i, ψ (H (b i) • dual i) := by
    change Ψ (Multiplicative.ofAdd (∑ i, H (b i) • dual i)) = _
    rw [ofAdd_sum, map_prod]
    rfl
  rw [hprod]
  simp_rw [ha]
  rw [← Complex.exp_sum, parameterPower, ← hH]
  congr 1
  rw [map_sum, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [imaginaryParameter, TensorProduct.AlgebraTensorModule.map_tmul,
    LinearMap.toSpanSingleton_apply, LinearMap.id_apply, complexParameterPairing_tmul]
  simp [Complex.real_smul]

end Langlands.Global.RestrictionSplitCentre

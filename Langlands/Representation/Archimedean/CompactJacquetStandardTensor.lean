import Langlands.Automorphic.ArchimedeanStandardAdmissibleProof
import Langlands.Representation.Archimedean.AdmissibleProductTensor
import Langlands.Representation.Archimedean.ComplexJacquetFrobeniusProof
import Langlands.Representation.Archimedean.RealBlockPositionData
import Langlands.Representation.Archimedean.RealLeviProducts

/-! # Standard tensors from algebraic coefficient functionals in the compact picture -/

noncomputable section

open scoped BigOperators TensorProduct Matrix.Norms.Operator

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

universe uW uI uV uK uD

variable {W : Type uW} [AddCommGroup W] [Module ℂ W] {I : Type uI}

private theorem exists_tensor_of_intertwiners
    {K : Type uK} [Group K] [TopologicalSpace K] {D : Type uD}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (κ : Representation ℂ K W) (π : D → Module.End ℂ W)
    (ρ : Representation ℂ K V) (τ : D → Module.End ℂ V)
    (hadm : IsAdmissibleGKModule ρ)
    (hfin : ∀ w, FiniteVectors.IsFiniteVector κ w)
    (hcont : ∀ (w : W) (μ : W →ₗ[ℂ] ℂ), Continuous fun k => μ (κ k w))
    (q : I → W →ₗ[ℂ] V)
    (hK : ∀ k w i, q i (κ k w) = ρ k (q i w))
    (hD : ∀ X w i, q i (π X w) = τ X (q i w))
    (hsep : ∀ w, (∀ i, q i w = 0) → w = 0) :
    ∃ e : W →ₗ[ℂ] V ⊗[ℂ] (I → ℂ), Function.Injective e ∧
      (∀ k w, e (κ k w) = TensorProduct.map (ρ k) LinearMap.id (e w)) ∧
      ∀ X w, e (π X w) = TensorProduct.map (τ X) LinearMap.id (e w) := by
  let coord : W →ₗ[ℂ] I → V := LinearMap.pi q
  have hspan (w : W) : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (coord w))) :=
    finiteDimensional_span_range_of_compactCoordinates κ ρ hadm hcont coord hK w (hfin w)
  refine ⟨toMultiplicityTensor coord hspan, toMultiplicityTensor_injective coord hspan ?_,
    fun k w => toMultiplicityTensor_equivariant coord hspan (κ k) (ρ k) (hK k) w,
    fun X w => toMultiplicityTensor_equivariant coord hspan (π X) (τ X) (hD X) w⟩
  intro w w' h
  apply sub_eq_zero.mp
  apply hsep
  intro i
  rw [map_sub]
  exact sub_eq_zero.mpr (congrFun h i)

section Real

open RealLeviChart RealLeviSlices RealJacquetFrobenius RealBlockPosition

variable {c : ℕ} (ds : Fin c → List RealBlock)

local notation "N" => (∑ i, sz ds i)
local notation "RK" => Matrix.unitaryGroup (Fin N) ℝ
local notation "RM" => Matrix (Fin N) (Fin N) ℝ
local notation "V₀" => kFiniteFunctions (realStandardModule N (flat ds)) (unitaryCompact ℝ N)
local notation "shifts" => RealBlockPosition.shiftedExponent N (flat ds)
local notation "signs" => positionSign N (flat ds)

variable (κ : Representation ℂ (Matrix.unitaryGroup (Fin (∑ i, sz ds i)) ℝ) W)
variable (π : (ℂ ⊗[ℝ] Matrix (Fin (∑ i, sz ds i)) (Fin (∑ i, sz ds i)) ℝ) →ₗ⁅ℂ⁆
  Module.End ℂ W)

/-- Each single compact Levi block of an algebraic coefficient functional is the
restriction of a function in the corresponding real block standard module. -/
def HasRealCompactBlockSlices (ℓ : W →ₗ[ℂ] ℂ) : Prop :=
  ∀ (i : Fin c) (w : W), ∃ φ ∈ realStandardModule (sz ds i) (ds i),
    ∀ k : Matrix.unitaryGroup (Fin (sz ds i)) ℝ,
      ℓ (κ (embK (sz ds) i k) w) = φ (Unitary.toUnits k)

variable {κ π} {ℓ : W →ₗ[ℂ] ℂ}

private theorem realFrobenius_compact
    (hℓ : IsRealJacquetFunctional N κ π ℓ shifts signs) (w : W) (k : RK) :
    frobLin κ ℓ shifts signs w (Unitary.toUnits k) = ℓ (κ k w) := by
  have hsign := fun j w => (hℓ.2 j w).2
  rw [frobLin_apply, frobFun_eq (b := 1) (k := k.val) hsign Matrix.blockTriangular_one
    k.property (by rw [Matrix.one_mul]; rfl) w, diagChar_one, one_mul]

private theorem realFrobenius_mem_standard
    (hgk : IsRealGKModule N κ π) (hℓ : IsRealJacquetFunctional N κ π ℓ shifts signs)
    (hs : HasRealCompactBlockSlices ds κ ℓ) (w : W) :
    frobLin κ ℓ shifts signs w ∈ V₀ := by
  have hsign := fun j w => (hℓ.2 j w).2
  refine ⟨mem_realStandardModule_of_unitaryCompact (realRank_flat ds) ?_ ?_,
    frobFun_mem_kFiniteVectors hsign w (hgk.1 w)⟩
  · rw [← principalSeries_posChar_shiftedExponent]
    exact ⟨contMDiff_frobFun hsign hgk.1 hgk.2.1 w, frobFun_left hsign w⟩
  · intro p d hp m hm g hg
    have hpos := realInducedBlockAt_lt hp
    rw [realRank_flat ds] at hpos
    have hp' : p < N := lt_trans (Nat.lt_succ_self p) hpos
    obtain ⟨⟨i, a⟩, ha⟩ := finSigmaFinEquiv.surjective (⟨p, hp'⟩ : Fin N)
    have hpa : start (sz ds) i + a = p := by
      have h := congrArg Fin.val ha
      change (pos (sz ds) i a : ℕ) = p at h
      simpa only [val_pos] using h
    have hd : realInducedBlockAt (ds i) a = some d := by
      rw [← realInducedBlockAt_flat ds i a a.isLt, hpa]
      exact hp
    have ha' : (a : ℕ) + 1 < sz ds i := realInducedBlockAt_lt hd
    let k₀ : RK := ⟨g.val, hg⟩
    have hg₀ : Unitary.toUnits k₀ = g := Units.ext rfl
    obtain ⟨φ, hφ, hφk⟩ := hs i (κ k₀ w)
    have hrot (θ : ℝ) :
        frobLin κ ℓ shifts signs w (blockRotation N p θ * g) = φ (blockRotation (sz ds i) a θ) := by
      let k : Matrix.unitaryGroup (Fin (sz ds i)) ℝ :=
        ⟨(blockRotation (sz ds i) a θ).val, blockRotation_mem_unitaryCompact _ _ _⟩
      have hk : Unitary.toUnits k = blockRotation (sz ds i) a θ := Units.ext rfl
      have hprod : Unitary.toUnits (embK (sz ds) i k * k₀) = blockRotation N p θ * g := by
        rw [map_mul, toUnits_embK, hg₀, hk, ← RealLeviProducts.blockRotation_start_add _ _ ha', hpa]
      rw [← hprod, realFrobenius_compact ds hℓ w, map_mul, Module.End.mul_apply, hφk, hk]
    have hzero := hφ.2 a d hd m hm 1
    unfold blockFourierCoefficient at hzero ⊢
    simpa only [hrot, mul_one] using hzero

/-- The Frobenius extension of a Jacquet coefficient with the compact block
relations takes values in the concatenated real standard module. -/
def realCompactJacquetMap
    (hgk : IsRealGKModule N κ π) (hℓ : IsRealJacquetFunctional N κ π ℓ shifts signs)
    (hs : HasRealCompactBlockSlices ds κ ℓ) : W →ₗ[ℂ] V₀ :=
  (frobLin κ ℓ shifts signs).codRestrict _ (realFrobenius_mem_standard ds hgk hℓ hs)

theorem realCompactJacquetMap_compact
    (hgk : IsRealGKModule N κ π) (hℓ : IsRealJacquetFunctional N κ π ℓ shifts signs)
    (hs : HasRealCompactBlockSlices ds κ ℓ) (w : W) (k : RK) :
    (realCompactJacquetMap ds hgk hℓ hs w : Langlands.GeneralLinear N ℝ → ℂ)
      (Unitary.toUnits k) = ℓ (κ k w) :=
  realFrobenius_compact ds hℓ w k

private theorem realCompactJacquetMap_K
    (hgk : IsRealGKModule N κ π) (hℓ : IsRealJacquetFunctional N κ π ℓ shifts signs)
    (hs : HasRealCompactBlockSlices ds κ ℓ) (w : W) (k : RK) :
    realCompactJacquetMap ds hgk hℓ hs (κ k w) =
      realStandardRep N (flat ds) k (realCompactJacquetMap ds hgk hℓ hs w) := by
  apply Subtype.ext
  rw [realStandardRep_apply_coe]
  exact frobFun_rightTranslation (fun j w => (hℓ.2 j w).2) ⟨Unitary.toUnits k, k.property⟩ w

private theorem realCompactJacquetMap_lie
    (hgk : IsRealGKModule N κ π) (hℓ : IsRealJacquetFunctional N κ π ℓ shifts signs)
    (hs : HasRealCompactBlockSlices ds κ ℓ) (w : W) (X : RM) :
    realCompactJacquetMap ds hgk hℓ hs (π (1 ⊗ₜ X) w) =
      realStandardLie N (flat ds) (1 ⊗ₜ X) (realCompactJacquetMap ds hgk hℓ hs w) := by
  apply Subtype.ext
  rw [realStandardLie_one_tmul_apply_coe]
  funext g
  exact frobFun_rightDerivative hgk hℓ X w g

/-- Separating Jacquet probes with the block compact relations embed the source
into an algebraic tensor of the concatenated real standard module. -/
theorem exists_realStandardTensor_of_compactJacquet
    (hgk : IsRealGKModule N κ π) (probe : I → W →ₗ[ℂ] ℂ)
    (hJ : ∀ a, IsRealJacquetFunctional N κ π (probe a) shifts signs)
    (hs : ∀ a, HasRealCompactBlockSlices ds κ (probe a))
    (hsep : ∀ w, (∀ a k, probe a (κ k w) = 0) → w = 0) :
    ∃ e : W →ₗ[ℂ] V₀ ⊗[ℂ] (I → ℂ), Function.Injective e ∧
      (∀ k w, e (κ k w) = TensorProduct.map (realStandardRep N (flat ds) k) LinearMap.id (e w)) ∧
      ∀ X, ∀ w, e (π (1 ⊗ₜ X) w) =
        TensorProduct.map (realStandardLie N (flat ds) (1 ⊗ₜ X)) LinearMap.id (e w) := by
  let q (a : I) := realCompactJacquetMap ds hgk (hJ a) (hs a)
  refine exists_tensor_of_intertwiners κ (fun X : RM => π (1 ⊗ₜ X))
    (realStandardRep N (flat ds)) (fun X => realStandardLie N (flat ds) (1 ⊗ₜ X))
    (realStandardAdmissible N (flat ds)) hgk.1 hgk.2.1 q
    (fun k w a => realCompactJacquetMap_K ds hgk (hJ a) (hs a) w k)
    (fun X w a => realCompactJacquetMap_lie ds hgk (hJ a) (hs a) w X) ?_
  intro w hw
  apply hsep
  intro a k
  rw [← realCompactJacquetMap_compact ds hgk (hJ a) (hs a)]
  exact congrArg (fun v : V₀ => (v : Langlands.GeneralLinear N ℝ → ℂ) (Unitary.toUnits k)) (hw a)

end Real

section Complex

variable {n : ℕ} (d : Fin n → ComplexCharacterData)

local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ
local notation "V₀" =>
  kFiniteFunctions (complexStandardModule n (List.ofFn d)) (unitaryCompact ℂ n)

/-- The normalized real-diagonal differential for the complex principal series. -/
def complexShiftedExponent (j : Fin n) : ℂ :=
  2 * (d j).exponent + ((n : ℂ) - 1) - 2 * ((j : ℕ) : ℂ)

variable {κ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) W}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ W}
  {ℓ : W →ₗ[ℂ] ℂ}

local notation "weights" => (fun j => ComplexCharacterData.weight (d j))
local notation "phaseDirs" => (fun j => Complex.I * (ComplexCharacterData.weight (d j) : ℂ))

private theorem torusEigenfunctional_of_jacquet
    (hgk : IsComplexGKModule n κ π)
    (hℓ : IsComplexJacquetFunctional n π ℓ (complexShiftedExponent d) phaseDirs) :
    IsTorusEigenfunctional κ ℓ weights := by
  by_cases he : ℓ = 0
  · subst ℓ
    intro m hm w
    simp
  · obtain ⟨l, hl, hT⟩ := hℓ.exists_weight hgk he
    have hw : l = weights := by
      funext j
      have heq := mul_left_cancel₀ Complex.I_ne_zero (hl j).symm
      exact_mod_cast heq
    rw [← hw]
    exact hT

private theorem complexFrobenius_mem_standard
    (hgk : IsComplexGKModule n κ π) (hT : IsTorusEigenfunctional κ ℓ weights) (w : W) :
    frobeniusMap κ ℓ weights (complexShiftedExponent d) w ∈ V₀ := by
  refine ⟨⟨contMDiff_frobeniusFunction hgk hT (complexShiftedExponent d) w, fun a u g => ?_⟩,
    frobeniusFunction_mem_kFiniteVectors hT (complexShiftedExponent d) w (hgk.1 w)⟩
  change frobeniusFunction κ ℓ weights (complexShiftedExponent d) w _ = _
  rw [frobeniusFunction_diagonal_mul hT, principalSeriesCharacter_ofFn]
  rfl

/-- Extend a complex Jacquet coefficient to the standard module of the indicated character
list, keeping its exact weights and exponents. -/
def complexCompactJacquetMap
    (hgk : IsComplexGKModule n κ π)
    (hℓ : IsComplexJacquetFunctional n π ℓ (complexShiftedExponent d) phaseDirs) : W →ₗ[ℂ] V₀ :=
  (frobeniusMap κ ℓ weights (complexShiftedExponent d)).codRestrict _
    (complexFrobenius_mem_standard d hgk (torusEigenfunctional_of_jacquet d hgk hℓ))

theorem complexCompactJacquetMap_compact
    (hgk : IsComplexGKModule n κ π)
    (hℓ : IsComplexJacquetFunctional n π ℓ (complexShiftedExponent d) phaseDirs)
    (w : W) (k : CK) :
    (complexCompactJacquetMap d hgk hℓ w : Langlands.GeneralLinear n ℂ → ℂ)
      (Unitary.toUnits k) = ℓ (κ k w) := by
  change frobeniusFunction κ ℓ weights (complexShiftedExponent d) w (Unitary.toUnits k) = _
  rw [frobeniusFunction_eq (b := 1) (torusEigenfunctional_of_jacquet d hgk hℓ)
    (complexShiftedExponent d) w _ k Matrix.blockTriangular_one isUnit_one (by simp),
    borelChar_one, one_mul]

private theorem complexCompactJacquetMap_K
    (hgk : IsComplexGKModule n κ π)
    (hℓ : IsComplexJacquetFunctional n π ℓ (complexShiftedExponent d) phaseDirs)
    (w : W) (k : CK) :
    complexCompactJacquetMap d hgk hℓ (κ k w) =
      complexStandardRep n (List.ofFn d) k (complexCompactJacquetMap d hgk hℓ w) := by
  apply Subtype.ext
  rw [principalSeriesRep_apply_coe]
  funext g
  exact (frobeniusFunction_mul_unitary (torusEigenfunctional_of_jacquet d hgk hℓ)
    (complexShiftedExponent d) w g (Unitary.toUnits k) k rfl).symm

private theorem complexCompactJacquetMap_lie
    (hgk : IsComplexGKModule n κ π)
    (hℓ : IsComplexJacquetFunctional n π ℓ (complexShiftedExponent d) phaseDirs)
    (w : W) (X : CM) :
    complexCompactJacquetMap d hgk hℓ (π (1 ⊗ₜ X) w) =
      complexStandardLie n (List.ofFn d) (1 ⊗ₜ X) (complexCompactJacquetMap d hgk hℓ w) := by
  apply Subtype.ext
  rw [principalSeriesLie_one_tmul_apply_coe]
  funext g
  exact (rightDerivative_frobeniusFunction hgk hℓ (torusEigenfunctional_of_jacquet d hgk hℓ)
    w X g).symm

/-- A separating family of algebraic Jacquet coefficients embeds the source in the
complex standard module with a scalar multiplicity factor. -/
theorem exists_complexStandardTensor_of_compactJacquet
    (hgk : IsComplexGKModule n κ π) (probe : I → W →ₗ[ℂ] ℂ)
    (hJ : ∀ a, IsComplexJacquetFunctional n π (probe a) (complexShiftedExponent d) phaseDirs)
    (hsep : ∀ w, (∀ a k, probe a (κ k w) = 0) → w = 0) :
    ∃ e : W →ₗ[ℂ] V₀ ⊗[ℂ] (I → ℂ), Function.Injective e ∧
      (∀ k w, e (κ k w) =
        TensorProduct.map (complexStandardRep n (List.ofFn d) k) LinearMap.id (e w)) ∧
      ∀ X, ∀ w, e (π (1 ⊗ₜ X) w) =
        TensorProduct.map (complexStandardLie n (List.ofFn d) (1 ⊗ₜ X)) LinearMap.id (e w) := by
  let q (a : I) := complexCompactJacquetMap d hgk (hJ a)
  refine exists_tensor_of_intertwiners κ (fun X : CM => π (1 ⊗ₜ X))
    (complexStandardRep n (List.ofFn d)) (fun X => complexStandardLie n (List.ofFn d) (1 ⊗ₜ X))
    (complexStandardAdmissible n (List.ofFn d)) hgk.1 hgk.2.1 q
    (fun k w a => complexCompactJacquetMap_K d hgk (hJ a) w k)
    (fun X w a => complexCompactJacquetMap_lie d hgk (hJ a) w X) ?_
  intro w hw
  apply hsep
  intro a k
  rw [← complexCompactJacquetMap_compact d hgk (hJ a)]
  exact congrArg (fun v : V₀ => (v : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits k)) (hw a)

end Complex

end Langlands.Archimedean

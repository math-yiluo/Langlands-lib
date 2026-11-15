import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof
import Langlands.Geometry.Building.Kottwitz.TorusNormValuation

/-! # Uniformizers of composita with the maximal unramified extension -/

noncomputable section

universe u

open Polynomial IsLocalRing
open scoped NNReal IntermediateField WithZero

namespace Langlands.Geometry.Building.Kottwitz

namespace CompositumUniformizer

open Langlands.LocalGalois Langlands.LocalGalois.Separable

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

local instance (priority := 10) compositumNormedField : NontriviallyNormedField F := localNormedField F
local instance compositumUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance compositumComplete : CompleteSpace F := localNormedField_complete F
local instance compositumResidueFinite : Finite (ResidueField (baseIntegers F)) :=
  localResidue_finite F

local notation "Ω" => SeparableClosure F
local notation "𝔸" => extensionIntegers F (SeparableClosure F)
local notation "κ" => ResidueField (baseIntegers F)

/-- The spectral valuation of `F^sep` is invariant under `Gal(F^sep/F)`. -/
theorem sepClosureValuation_map (σ : Ω ≃ₐ[F] Ω) (x : Ω) :
    sepClosureValuation F (σ x) = sepClosureValuation F x := by
  apply NNReal.eq
  rw [sepClosureValuation_apply, sepClosureValuation_apply]
  exact (spectralNorm_eq_of_equiv σ x).symm

theorem mem_integers_iff (x : Ω) : x ∈ 𝔸 ↔ sepClosureValuation F x ≤ 1 :=
  Valuation.mem_valuationSubring_iff _ _

variable (E : IntermediateField F (SeparableClosure F))

/-- A polynomial expression over an intermediate field `E` in a Teichmüller root `ζ`, of degree
below the degree of `ζ` over `E`, has the value of one of its coefficients. -/
theorem exists_value_aeval_teich {M : ℕ} (hM : 0 < M) {ζ : 𝔸}
    (hζ : IsPrimitiveRoot ζ (Nat.card κ ^ M - 1)) (g : Polynomial E)
    (hg : g.natDegree < (minpoly E (ζ : Ω)).natDegree) :
    ∃ a : E, sepClosureValuation F (aeval (ζ : Ω) g) = sepClosureValuation F (a : Ω) := by
  classical
  have : IsGalois E Ω := IsGalois.tower_top_of_isGalois F E Ω
  by_cases hg0 : g = 0
  · exact ⟨0, by simp [hg0]⟩
  obtain ⟨j, hj, hmax⟩ := g.support.exists_max_image
    (fun i => sepClosureValuation F ((g.coeff i : E) : Ω)) (nonempty_support_iff.mpr hg0)
  have hc : g.coeff j ≠ 0 := mem_support_iff.mp hj
  have hcΩ : ((g.coeff j : E) : Ω) ≠ 0 := by
    intro h
    exact hc (Subtype.ext h)
  have hvc : sepClosureValuation F ((g.coeff j : E) : Ω) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hcΩ
  refine ⟨g.coeff j, ?_⟩
  set h : Polynomial E := C (g.coeff j)⁻¹ * g with hh
  -- every coefficient of `h` is integral
  have hlift : ∀ i, (h.map (algebraMap E Ω)).coeff i ∈ Set.range (algebraMap 𝔸 Ω) := by
    intro i
    refine ⟨⟨(h.map (algebraMap E Ω)).coeff i, ?_⟩, rfl⟩
    rw [mem_integers_iff, coeff_map, hh, coeff_C_mul, map_mul, map_inv₀, map_mul, map_inv₀]
    by_cases hi : i ∈ g.support
    · exact inv_mul_le_one_of_le₀ (hmax i hi) zero_le
    · rw [notMem_support_iff.mp hi, map_zero, map_zero, mul_zero]
      exact zero_le_one
  obtain ⟨g₀, hg₀⟩ := (mem_lifts _).mp ((lifts_iff_coeff_lifts _).mpr hlift)
  have hinj : Function.Injective (algebraMap 𝔸 Ω) := Subtype.val_injective
  have hcoeff : g₀.coeff j = 1 := by
    apply hinj
    rw [← coeff_map, hg₀, coeff_map, hh, coeff_C_mul, inv_mul_cancel₀ hc, map_one, map_one]
  have hdeg : g₀.natDegree < (minpoly E (ζ : Ω)).natDegree := by
    rw [← natDegree_map_eq_of_injective hinj, hg₀,
      natDegree_map_eq_of_injective (algebraMap E Ω).injective]
    exact lt_of_le_of_lt (natDegree_C_mul_le _ _) hg
  have heval : ∀ β : 𝔸, aeval (β : Ω) h = ((aeval β g₀ : 𝔸) : Ω) := by
    intro β
    rw [aeval_def, ← eval_map, ← hg₀, eval_map, aeval_def]
    exact eval₂_at_apply (algebraMap 𝔸 Ω) β
  -- the residue polynomial
  set H : (ResidueField 𝔸)[X] := g₀.map (residue 𝔸) with hH
  have hH0 : H ≠ 0 := by
    intro h0
    have := congrArg (fun p => p.coeff j) h0
    simp only [hH, coeff_map, hcoeff, map_one, coeff_zero] at this
    exact one_ne_zero this
  have hres : ∀ β : 𝔸, residue 𝔸 (aeval β g₀) = eval (residue 𝔸 β) H := by
    intro β
    rw [hH, eval_map, aeval_def]
    exact (eval₂_at_apply (residue 𝔸) β).symm
  have hval_le : sepClosureValuation F (aeval (ζ : Ω) h) ≤ 1 := by
    rw [heval]
    exact (aeval ζ g₀).2
  have hval : sepClosureValuation F (aeval (ζ : Ω) h) = 1 := by
    refine le_antisymm hval_le (not_lt.mp fun hlt => ?_)
    -- every conjugate of `ζ` over `E` gives a residue root of `H`
    have hroot : ∀ β ∈ (minpoly E (ζ : Ω)).rootSet Ω,
        ∃ σ : Ω ≃ₐ[E] Ω, σ (ζ : Ω) = β := fun β hβ =>
      minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic _) (mem_rootSet'.mp hβ).2
    have hint : ∀ σ : Ω ≃ₐ[E] Ω, σ (ζ : Ω) ∈ 𝔸 := by
      intro σ
      rw [mem_integers_iff]
      exact (sepClosureValuation_map F (σ.restrictScalars F) (ζ : Ω)).le.trans
        ((mem_integers_iff F _).mp ζ.2)
    let gfun : Ω → ResidueField 𝔸 := fun β => if hβ : β ∈ 𝔸 then residue 𝔸 ⟨β, hβ⟩ else 0
    have hg' : ∀ σ : Ω ≃ₐ[E] Ω, gfun (σ (ζ : Ω)) = residue 𝔸 ⟨σ (ζ : Ω), hint σ⟩ := fun σ =>
      dite_eq_left_of_eq_true (eq_true (hint σ))
    have hpow : ∀ σ : Ω ≃ₐ[E] Ω,
        (⟨σ (ζ : Ω), hint σ⟩ : 𝔸) ^ (Nat.card κ ^ M - 1) = 1 := by
      intro σ
      apply Subtype.ext
      change σ (ζ : Ω) ^ (Nat.card κ ^ M - 1) = 1
      rw [← map_pow, coe_pow_eq_one F hζ.pow_eq_one, map_one]
    have hcard : ((minpoly E (ζ : Ω)).rootSet Ω).ncard = (minpoly E (ζ : Ω)).natDegree := by
      rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
      exact card_rootSet_eq_natDegree (Algebra.IsSeparable.isSeparable E _)
        (Normal.splits inferInstance _)
    have hle : ((minpoly E (ζ : Ω)).rootSet Ω).ncard ≤ (H.rootSet (ResidueField 𝔸)).ncard := by
      refine Set.ncard_le_ncard_of_injOn gfun ?_ ?_ (rootSet_finite _ _)
      · intro β hβ
        obtain ⟨σ, rfl⟩ := hroot β hβ
        rw [hg', mem_rootSet']
        refine ⟨by rwa [Algebra.algebraMap_self, Polynomial.map_id], ?_⟩
        rw [coe_aeval_eq_eval, ← hres]
        rw [residue_eq_zero_iff, mem_maximalIdeal_iff_lt]
        have h1 := heval ⟨σ (ζ : Ω), hint σ⟩
        change aeval (σ (ζ : Ω)) h = _ at h1
        have h2 : aeval (σ (ζ : Ω)) h = σ (aeval (ζ : Ω) h) :=
          aeval_algHom_apply σ.toAlgHom (ζ : Ω) h
        change sepClosureValuation F _ < 1
        rw [← h1, h2]
        exact (sepClosureValuation_map F (σ.restrictScalars F) _).trans_lt hlt
      · intro β₁ h₁ β₂ h₂ heq
        obtain ⟨σ₁, rfl⟩ := hroot β₁ h₁
        obtain ⟨σ₂, rfl⟩ := hroot β₂ h₂
        rw [hg', hg'] at heq
        have := eq_of_pow_eq_one_of_sub_mem (teichOrder_isUnit F hM) (hpow σ₁) (hpow σ₂)
          (by rw [← residue_eq_zero_iff, map_sub, heq, sub_self])
        exact congrArg Subtype.val this
    have h3 := ncard_rootSet_le H (ResidueField 𝔸)
    have h4 : H.natDegree ≤ g₀.natDegree := natDegree_map_le
    omega
  have hsplit : aeval (ζ : Ω) g = ((g.coeff j : E) : Ω) * aeval (ζ : Ω) h := by
    have hg' : g = C (g.coeff j) * h := by
      rw [hh, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]
    conv_lhs => rw [hg']
    rw [map_mul, aeval_C]
    rfl
  rw [hsplit, map_mul, hval, mul_one]

/-- Every element of `K ⊔ E` lies in `E(ζ)` for a Teichmüller root of unity `ζ`. -/
theorem exists_teich_of_mem_sup {x : Ω} (hx : x ∈ inertiaFixedField F ⊔ E) :
    ∃ M, 0 < M ∧ ∃ ζ : 𝔸, IsPrimitiveRoot ζ (Nat.card κ ^ M - 1) ∧
      x ∈ IntermediateField.adjoin E {(ζ : Ω)} := by
  have hle : inertiaFixedField F ⊔ E ≤
      (IntermediateField.adjoin E (teichSet F)).restrictScalars F := by
    rw [IntermediateField.restrictScalars_adjoin_eq_sup, sup_comm]
    exact sup_le_sup_left (inertiaFixedField_le_adjoin F) E
  obtain ⟨S, hS, hxS⟩ := IntermediateField.exists_finset_of_mem_adjoin
    ((IntermediateField.mem_restrictScalars F).mp (hle hx))
  obtain ⟨M, hM, hSM⟩ := exists_common_teich F S hS
  obtain ⟨ζ, hζ⟩ := exists_teich F hM
  refine ⟨M, hM, ζ, hζ, ?_⟩
  refine (IntermediateField.adjoin_le_iff.mpr ?_) hxS
  intro y hy
  have hy' := mem_adjoin_of_pow_eq_one F hM hζ (hSM y hy)
  have hle' : IntermediateField.adjoin F {(ζ : Ω)} ≤
      (IntermediateField.adjoin E {(ζ : Ω)}).restrictScalars F :=
    IntermediateField.adjoin_le_iff.mpr
      (Set.singleton_subset_iff.mpr (IntermediateField.mem_adjoin_simple_self E _))
  exact (IntermediateField.mem_restrictScalars F).mp (hle' hy')

/-- Every value of the spectral valuation on `K ⊔ E` is attained on `E`. -/
theorem exists_value_of_mem_sup {x : Ω} (hx : x ∈ inertiaFixedField F ⊔ E) :
    ∃ a : E, sepClosureValuation F x = sepClosureValuation F (a : Ω) := by
  obtain ⟨M, hM, ζ, hζ, hxζ⟩ := exists_teich_of_mem_sup F E hx
  have hint : IsIntegral E (ζ : Ω) :=
    (Algebra.IsIntegral.isIntegral (R := F) (ζ : Ω)).tower_top
  obtain ⟨f, hfdeg, hf⟩ :=
    (IntermediateField.adjoin.powerBasis hint).exists_eq_aeval ⟨x, hxζ⟩
  have hx' : x = aeval (ζ : Ω) f := by
    have := congrArg Subtype.val hf
    rwa [IntermediateField.adjoin.powerBasis_gen,
      IntermediateField.AdjoinSimple.coe_aeval_gen_apply] at this
  obtain ⟨a, ha⟩ := exists_value_aeval_teich F E hM hζ f hfdeg
  exact ⟨a, by rw [hx', ha]⟩

/-- If a finite extension `M` of `K = UnramifiedClosure F` inside `F^sep` contains `E` and is
contained in `K ⊔ E`, some element of `E` has normalized `M`-valuation one. -/
theorem exists_uniformizer_of_le_sup
    (M : IntermediateField (UnramifiedClosure F) Ω) [FiniteDimensional (UnramifiedClosure F) M]
    (hM : ∀ x ∈ M, x ∈ inertiaFixedField F ⊔ E) (hEM : ∀ x ∈ E, x ∈ M) :
    ∃ a : E, normalizedIntermediateValuation F M ⟨a, hEM a a.2⟩ =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : ℤᵐ⁰) := by
  obtain ⟨z, hz⟩ := (normalizedIntermediateValuation_spec' F M).2
    ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : ℤᵐ⁰)
  obtain ⟨a, ha⟩ := exists_value_of_mem_sup F E (hM z z.2)
  refine ⟨a, ?_⟩
  rw [← hz]
  exact ((normalizedIntermediateValuation_spec' F M).1.eq_iff).mpr ha.symm

end CompositumUniformizer

end Langlands.Geometry.Building.Kottwitz

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-! # Algebraic base change of a discrete valuation ring -/

noncomputable section

open TensorProduct IsLocalRing

namespace Langlands.CommutativeAlgebra.DVRAlgebraicBaseChange

section UnitMulPow

variable {A : Type*} [CommRing A]

/-- A nontrivial ring in which every element is zero or a unit times a power of `t`, with all
powers of `t` nonzero, is a domain. -/
theorem isDomain_of_forall_eq_zero_or [Nontrivial A] (t : A) (ht : ∀ j : ℕ, t ^ j ≠ 0)
    (h : ∀ y : A, y = 0 ∨ ∃ (j : ℕ) (u : A), IsUnit u ∧ y = t ^ j * u) : IsDomain A := by
  have : NoZeroDivisors A := by
    refine ⟨fun {a b} hab => ?_⟩
    rcases h a with ha | ⟨i, u, hu, rfl⟩
    · exact Or.inl ha
    rcases h b with hb | ⟨j, v, hv, rfl⟩
    · exact Or.inr hb
    exfalso
    apply ht (i + j)
    have : t ^ (i + j) * (u * v) = 0 := by rw [← hab]; ring
    exact (hu.mul hv).mul_left_eq_zero.mp this
  exact NoZeroDivisors.to_isDomain A

/-- A domain in which every element is zero or a unit times a power of a nonzero nonunit `t`
is a discrete valuation ring. -/
theorem isDiscreteValuationRing_of_forall_eq_zero_or [IsDomain A] (t : A) (ht : ¬IsUnit t)
    (ht0 : t ≠ 0) (h : ∀ y : A, y = 0 ∨ ∃ (j : ℕ) (u : A), IsUnit u ∧ y = t ^ j * u) :
    IsDiscreteValuationRing A := by
  have hirr : Irreducible t := by
    refine ⟨ht, fun a b hab => ?_⟩
    rcases h a with ha | ⟨i, u, hu, rfl⟩
    · exact absurd (by rw [hab, ha, zero_mul]) ht0
    rcases h b with hb | ⟨j, v, hv, rfl⟩
    · exact absurd (by rw [hab, hb, mul_zero]) ht0
    rcases i with _ | i
    · left; simpa using hu
    rcases j with _ | j
    · right; simpa using hv
    exfalso
    apply ht
    have h1 : t * 1 = t * (t * (t ^ (i + j) * (u * v))) := by rw [mul_one]; nth_rw 1 [hab]; ring
    exact IsUnit.of_mul_eq_one _ (mul_left_cancel₀ ht0 h1).symm
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨t, hirr, fun {x} hx => ?_⟩
  rcases h x with hx' | ⟨j, u, hu, rfl⟩
  · exact absurd hx' hx
  exact ⟨j, hu.unit, rfl⟩

/-- Krull's intersection theorem: if every element of the prime `n` becomes a multiple of
`t ∈ n` after multiplication by an element outside `n`, then every element of the Noetherian
localization at `n` is zero or a unit times a power of `t`. -/
theorem localization_eq_zero_or_of_isNoetherianRing [IsNoetherianRing A] (n : Ideal A)
    [n.IsPrime] (t : A) (htn : t ∈ n) (h : ∀ x ∈ n, ∃ s ∉ n, s * x ∈ Ideal.span {t})
    (y : Localization.AtPrime n) :
    y = 0 ∨ ∃ (j : ℕ) (u : Localization.AtPrime n), IsUnit u ∧
      y = algebraMap A (Localization.AtPrime n) t ^ j * u := by
  have hmax : maximalIdeal (Localization.AtPrime n) =
      Ideal.span {algebraMap A (Localization.AtPrime n) t} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      obtain ⟨s, hs, hsx⟩ := h x hx
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hsx
      have hu : IsUnit (algebraMap A (Localization.AtPrime n) s) :=
        IsLocalization.map_units (Localization.AtPrime n) (⟨s, hs⟩ : n.primeCompl)
      rw [Ideal.mem_comap, ← Ideal.unit_mul_mem_iff_mem _ hu, ← map_mul, ← ha, map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ htn
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (Localization.AtPrime n))
    (Ideal.IsMaximal.ne_top inferInstance)
  by_cases hy : y = 0
  · exact Or.inl hy
  right
  have hex : ∃ N, y ∉ maximalIdeal (Localization.AtPrime n) ^ N := by
    by_contra hcon
    push Not at hcon
    apply hy
    have : y ∈ ⨅ N, maximalIdeal (Localization.AtPrime n) ^ N := Submodule.mem_iInf _ |>.mpr hcon
    rwa [hK, Ideal.mem_bot] at this
  classical
  have hN0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0, pow_zero, Ideal.one_eq_top] at this
    exact this Submodule.mem_top
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  have hyj : y ∈ maximalIdeal (Localization.AtPrime n) ^ j := by
    have := Nat.find_min hex (show j < Nat.find hex by omega)
    simpa using this
  have hyj1 : y ∉ maximalIdeal (Localization.AtPrime n) ^ (j + 1) := by
    have := Nat.find_spec hex
    rwa [hj] at this
  rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hyj
  obtain ⟨u, hu⟩ := hyj
  refine ⟨j, u, ?_, by rw [← hu, mul_comm]⟩
  by_contra hnu
  have hum : u ∈ maximalIdeal (Localization.AtPrime n) := hnu
  rw [hmax, Ideal.mem_span_singleton'] at hum
  obtain ⟨c, hc⟩ := hum
  apply hyj1
  rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  exact ⟨c, by rw [← hu, ← hc]; ring⟩

/-- In a reduced zero-dimensional ring, every element of a prime `p` is killed by an element
outside `p`. -/
theorem exists_notMem_mul_eq_zero [Ring.KrullDimLE 0 A] [IsReduced A] (p : Ideal A) [p.IsPrime]
    {x : A} (hx : x ∈ p) : ∃ s ∉ p, s * x = 0 := by
  have hp : p ∈ minimalPrimes A := Ideal.mem_minimalPrimes_of_krullDimLE_zero p
  have : Ring.KrullDimLE 0 (Localization.AtPrime p) := .of_isLocalization _ hp _
  have hF : IsField (Localization.AtPrime p) := Ring.KrullDimLE.isField_of_isReduced
  have h0 : algebraMap A (Localization.AtPrime p) x = 0 := by
    have : algebraMap A (Localization.AtPrime p) x ∈ maximalIdeal (Localization.AtPrime p) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hx
    rwa [IsLocalRing.isField_iff_maximalIdeal_eq.mp hF, Ideal.mem_bot] at this
  obtain ⟨⟨s, hs⟩, hs'⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl _ x).mp h0
  exact ⟨s, hs, hs'⟩

end UnitMulPow

variable (k : Type*) [Field k]

section ZeroDim

variable (E F : Type*) [CommRing E] [Algebra k E] [Algebra.IsIntegral k E] [Field F] [Algebra k F]

/-- The tensor product of an integral algebra with a field is zero-dimensional. -/
theorem krullDimLE_zero_tensor : Ring.KrullDimLE 0 (E ⊗[k] F) := by
  have h : Ring.KrullDimLE 0 (F ⊗[k] E) := by
    refine Ring.KrullDimLE.mk₀ fun I hI => ?_
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := F) I inferInstance
  rw [Ring.krullDimLE_iff] at h ⊢
  rwa [ringKrullDim_eq_of_ringEquiv (Algebra.TensorProduct.comm k E F).toRingEquiv]

end ZeroDim

section Stage

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra k R]
variable (E : Type*) [CommRing E] [Algebra k E]

/-- The reduction map `E ⊗[k] R → E ⊗[k] κ(R)`. -/
local notation "π" => Algebra.TensorProduct.map (AlgHom.id k E)
  (IsScalarTower.toAlgHom k R (ResidueField R))

theorem map_residue_surjective : Function.Surjective π :=
  Algebra.TensorProduct.map_surjective _ _ Function.surjective_id residue_surjective

/-- The kernel of the reduction map is generated by a uniformizer. -/
theorem ker_map_residue {ϖ : R} (hϖ : Irreducible ϖ) :
    RingHom.ker π = Ideal.span {(1 : E) ⊗ₜ[k] ϖ} := by
  rw [Algebra.TensorProduct.lTensor_ker _ residue_surjective]
  have : RingHom.ker (IsScalarTower.toAlgHom k R (ResidueField R)) = maximalIdeal R :=
    ker_residue
  rw [this, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  rfl

/-- Over a prime containing the uniformizer, every element becomes a multiple of the
uniformizer after multiplication by an element outside the prime. -/
theorem exists_notMem_mul_mem_span [Ring.KrullDimLE 0 (E ⊗[k] ResidueField R)]
    [IsReduced (E ⊗[k] ResidueField R)] {ϖ : R} (hϖ : Irreducible ϖ)
    (n : Ideal (E ⊗[k] R)) [n.IsPrime] (htn : (1 : E) ⊗ₜ[k] ϖ ∈ n) {x : E ⊗[k] R}
    (hx : x ∈ n) : ∃ s ∉ n, s * x ∈ Ideal.span {(1 : E) ⊗ₜ[k] ϖ} := by
  have hker : RingHom.ker π ≤ n := by
    rw [ker_map_residue k R E hϖ, Ideal.span_le, Set.singleton_subset_iff]
    exact htn
  have hsurj := map_residue_surjective k R E
  have : (n.map π).IsPrime := Ideal.map_isPrime_of_surjective hsurj hker
  obtain ⟨s', hs', hs'x⟩ := exists_notMem_mul_eq_zero (n.map π) (Ideal.mem_map_of_mem _ hx)
  obtain ⟨s, rfl⟩ := hsurj s'
  refine ⟨s, fun hs => hs' (Ideal.mem_map_of_mem _ hs), ?_⟩
  rw [← ker_map_residue k R E hϖ, RingHom.mem_ker, map_mul]
  exact hs'x

theorem isNoetherianRing_tensor [Module.Finite k E] : IsNoetherianRing (E ⊗[k] R) := by
  have : IsNoetherian R (R ⊗[k] E) := isNoetherian_of_isNoetherianRing_of_finite R _
  have : IsNoetherianRing (R ⊗[k] E) := isNoetherian_of_tower R this
  exact isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm k R E).toRingEquiv

/-- At a finite stage, every element of the localization at a prime containing the uniformizer
is zero or a unit times a power of the uniformizer. -/
theorem stage_localization_eq_zero_or [Module.Finite k E]
    [Ring.KrullDimLE 0 (E ⊗[k] ResidueField R)] [IsReduced (E ⊗[k] ResidueField R)]
    {ϖ : R} (hϖ : Irreducible ϖ) (n : Ideal (E ⊗[k] R)) [n.IsPrime]
    (htn : (1 : E) ⊗ₜ[k] ϖ ∈ n) (y : Localization.AtPrime n) :
    y = 0 ∨ ∃ (j : ℕ) (u : Localization.AtPrime n), IsUnit u ∧
      y = algebraMap _ (Localization.AtPrime n) ((1 : E) ⊗ₜ[k] ϖ) ^ j * u := by
  have := isNoetherianRing_tensor k R E
  exact localization_eq_zero_or_of_isNoetherianRing n _ htn
    (fun x hx => exists_notMem_mul_mem_span k R E hϖ n htn hx) y

end Stage

section Finite

variable (L : Type*) [Field L] [Algebra k L]
variable (R : Type*) [CommRing R] [Algebra k R]

/-- The base change to `R` of the inclusion of an intermediate field of `L`. -/
abbrev stageMap (E : IntermediateField k L) : E ⊗[k] R →ₐ[k] L ⊗[k] R :=
  Algebra.TensorProduct.map E.val (AlgHom.id k R)

theorem mem_range_stageMap_of_le {E₁ E₂ : IntermediateField k L} (h : E₁ ≤ E₂)
    {x : L ⊗[k] R} (hx : x ∈ (stageMap k L R E₁).range) : x ∈ (stageMap k L R E₂).range := by
  obtain ⟨y, rfl⟩ := (AlgHom.mem_range _).mp hx
  clear hx
  refine (AlgHom.mem_range _).mpr
    ⟨Algebra.TensorProduct.map (IntermediateField.inclusion h) (AlgHom.id k R) y, ?_⟩
  induction y with
  | tmul a r => simp
  | add y z hy hz => simp only [map_add, hy, hz]

/-- Every element of `L ⊗[k] R` comes from a finite-dimensional intermediate field. -/
theorem exists_finiteDimensional_mem_range [Algebra.IsAlgebraic k L] (x : L ⊗[k] R) :
    ∃ E : IntermediateField k L, FiniteDimensional k E ∧ x ∈ (stageMap k L R E).range := by
  induction x with
  | tmul a r =>
    refine ⟨IntermediateField.adjoin k {a},
      IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic a).isIntegral,
      (AlgHom.mem_range _).mpr ⟨⟨a, IntermediateField.mem_adjoin_simple_self k a⟩ ⊗ₜ r, rfl⟩⟩
  | add x y hx hy =>
    obtain ⟨E₁, h₁, hx⟩ := hx
    obtain ⟨E₂, h₂, hy⟩ := hy
    exact ⟨E₁ ⊔ E₂, inferInstance, Subalgebra.add_mem _
      (mem_range_stageMap_of_le k L R le_sup_left hx)
      (mem_range_stageMap_of_le k L R le_sup_right hy)⟩

/-- Any two elements of `L ⊗[k] R` come from a common finite-dimensional intermediate field. -/
theorem exists_finiteDimensional_mem_range₂ [Algebra.IsAlgebraic k L] (x y : L ⊗[k] R) :
    ∃ E : IntermediateField k L, FiniteDimensional k E ∧ x ∈ (stageMap k L R E).range ∧
      y ∈ (stageMap k L R E).range := by
  obtain ⟨E₁, h₁, hx⟩ := exists_finiteDimensional_mem_range k L R x
  obtain ⟨E₂, h₂, hy⟩ := exists_finiteDimensional_mem_range k L R y
  exact ⟨E₁ ⊔ E₂, inferInstance, mem_range_stageMap_of_le k L R le_sup_left hx,
    mem_range_stageMap_of_le k L R le_sup_right hy⟩

end Finite

section Main

variable (L : Type*) [Field L] [Algebra k L]
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra k R]
variable (m : Ideal (L ⊗[k] R)) [m.IsPrime]

/-- The image of a fraction coming from a finite stage `E → L` is zero or a unit times a power
of the uniformizer. -/
theorem mk'_stage_eq_zero_or (E : Type*) [Field E] [Algebra k E] [FiniteDimensional k E]
    [Algebra.IsGeometricallyReduced k (ResidueField R)] (g : E →ₐ[k] L) {ϖ : R}
    (hϖ : Irreducible ϖ) (htm : (1 : L) ⊗ₜ[k] ϖ ∈ m) (b s : E ⊗[k] R)
    (hs : Algebra.TensorProduct.map g (AlgHom.id k R) s ∈ m.primeCompl) :
    IsLocalization.mk' (Localization.AtPrime m) (Algebra.TensorProduct.map g (AlgHom.id k R) b)
        ⟨_, hs⟩ = 0 ∨ ∃ (j : ℕ) (u : Localization.AtPrime m), IsUnit u ∧
      IsLocalization.mk' (Localization.AtPrime m) (Algebra.TensorProduct.map g (AlgHom.id k R) b)
        ⟨_, hs⟩ = algebraMap _ (Localization.AtPrime m) ((1 : L) ⊗ₜ[k] ϖ) ^ j * u := by
  have : Ring.KrullDimLE 0 (E ⊗[k] ResidueField R) := krullDimLE_zero_tensor k E _
  let G : E ⊗[k] R →+* L ⊗[k] R := (Algebra.TensorProduct.map g (AlgHom.id k R)).toRingHom
  obtain ⟨n, hn⟩ : ∃ n : Ideal (E ⊗[k] R), n = m.comap G := ⟨_, rfl⟩
  have : n.IsPrime := by rw [hn]; infer_instance
  have hsn : s ∈ n.primeCompl := by
    change s ∉ n
    rw [hn, Ideal.mem_comap]
    exact hs
  have htn : (1 : E) ⊗ₜ[k] ϖ ∈ n := by
    rw [hn, Ideal.mem_comap]
    simpa [G] using htm
  let φ : Localization.AtPrime n →+* Localization.AtPrime m := Localization.localRingHom n m G hn
  have hφ : IsLocalization.mk' (Localization.AtPrime m)
      (Algebra.TensorProduct.map g (AlgHom.id k R) b) ⟨_, hs⟩ =
      φ (IsLocalization.mk' _ b ⟨s, hsn⟩) := by
    simp only [φ, Localization.localRingHom_mk']
    rfl
  rcases stage_localization_eq_zero_or k R E hϖ n htn
    (IsLocalization.mk' _ b ⟨s, hsn⟩) with h0 | ⟨j, u, hu, hy⟩
  · left
    rw [hφ, h0, map_zero]
  · right
    refine ⟨j, φ u, hu.map φ, ?_⟩
    rw [hφ, hy, map_mul, map_pow]
    simp [φ, G]

/-- Every element of the localization at a prime containing the uniformizer is zero or a unit
times a power of the uniformizer. -/
theorem localization_eq_zero_or [Algebra.IsAlgebraic k L]
    [Algebra.IsGeometricallyReduced k (ResidueField R)] {ϖ : R} (hϖ : Irreducible ϖ)
    (htm : (1 : L) ⊗ₜ[k] ϖ ∈ m) (y : Localization.AtPrime m) :
    y = 0 ∨ ∃ (j : ℕ) (u : Localization.AtPrime m), IsUnit u ∧
      y = algebraMap _ (Localization.AtPrime m) ((1 : L) ⊗ₜ[k] ϖ) ^ j * u := by
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective m.primeCompl y
  obtain ⟨E, hE, hb, hs⟩ := exists_finiteDimensional_mem_range₂ k L R b (s : L ⊗[k] R)
  obtain ⟨b', rfl⟩ := (AlgHom.mem_range _).mp hb
  obtain ⟨s', hs'⟩ := (AlgHom.mem_range _).mp hs
  have hs'm : stageMap k L R E s' ∈ m.primeCompl := hs' ▸ s.2
  have heq : IsLocalization.mk' (Localization.AtPrime m) (stageMap k L R E b') s =
      IsLocalization.mk' (Localization.AtPrime m) (stageMap k L R E b') ⟨_, hs'm⟩ := by
    congr 1
    exact Subtype.ext hs'.symm
  dsimp only
  rw [heq]
  exact mk'_stage_eq_zero_or k L R m E E.val hϖ htm b' s' hs'm

omit [IsDiscreteValuationRing R] in
/-- Multiplication by the uniformizer is injective on `L ⊗[k] R`. -/
theorem mul_tmul_injective {ϖ : R} (hϖ : ϖ ≠ 0) :
    Function.Injective (fun b : L ⊗[k] R => b * ((1 : L) ⊗ₜ[k] ϖ)) := by
  have : (fun b : L ⊗[k] R => b * ((1 : L) ⊗ₜ[k] ϖ)) =
      LinearMap.lTensor L (LinearMap.mulRight k ϖ) := by
    funext b
    induction b with
    | tmul a r => simp
    | add x y hx hy => simp only [add_mul, map_add, hx, hy]
  rw [this]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ (mul_left_injective₀ hϖ)

omit [IsDiscreteValuationRing R] in
theorem algebraMap_pow_ne_zero {ϖ : R} (hϖ : ϖ ≠ 0) (j : ℕ) :
    algebraMap _ (Localization.AtPrime m) ((1 : L) ⊗ₜ[k] ϖ) ^ j ≠ 0 := by
  have key : ∀ (j : ℕ) (s : L ⊗[k] R), s * ((1 : L) ⊗ₜ[k] ϖ) ^ j = 0 → s = 0 := by
    intro j
    induction j with
    | zero => intro s h; simpa using h
    | succ j ih =>
      intro s h
      apply ih
      apply mul_tmul_injective k L R hϖ
      simp only [zero_mul]
      rw [← h, pow_succ, mul_assoc]
  rw [← map_pow, Ne, IsLocalization.map_eq_zero_iff m.primeCompl]
  rintro ⟨⟨s, hs⟩, hs0⟩
  exact hs (key j s hs0 ▸ m.zero_mem)

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem algebraMap_mem_maximalIdeal {ϖ : R} (htm : (1 : L) ⊗ₜ[k] ϖ ∈ m) :
    algebraMap _ (Localization.AtPrime m) ((1 : L) ⊗ₜ[k] ϖ) ∈
      maximalIdeal (Localization.AtPrime m) :=
  (IsLocalization.AtPrime.to_map_mem_maximal_iff _ m _).mpr htm

/-- The localization at a prime containing the uniformizer is a domain. -/
theorem isDomain_localization [Algebra.IsAlgebraic k L]
    [Algebra.IsGeometricallyReduced k (ResidueField R)] {ϖ : R} (hϖ : Irreducible ϖ)
    (htm : (1 : L) ⊗ₜ[k] ϖ ∈ m) : IsDomain (Localization.AtPrime m) :=
  isDomain_of_forall_eq_zero_or _ (algebraMap_pow_ne_zero k L R m hϖ.ne_zero)
    (localization_eq_zero_or k L R m hϖ htm)

/-- The localization at a prime containing the uniformizer is a discrete valuation ring. -/
theorem isDiscreteValuationRing_localization [Algebra.IsAlgebraic k L]
    [Algebra.IsGeometricallyReduced k (ResidueField R)] [IsDomain (Localization.AtPrime m)]
    {ϖ : R} (hϖ : Irreducible ϖ) (htm : (1 : L) ⊗ₜ[k] ϖ ∈ m) :
    IsDiscreteValuationRing (Localization.AtPrime m) :=
  isDiscreteValuationRing_of_forall_eq_zero_or _
    ((mem_maximalIdeal _).mp (algebraMap_mem_maximalIdeal k L R m htm))
    (by simpa using algebraMap_pow_ne_zero k L R m hϖ.ne_zero 1)
    (localization_eq_zero_or k L R m hϖ htm)

/-- The map `R → (L ⊗[k] R)_m`. -/
def toLocalization : R →ₐ[k] Localization.AtPrime m :=
  (IsScalarTower.toAlgHom k (L ⊗[k] R) (Localization.AtPrime m)).comp
    Algebra.TensorProduct.includeRight

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem toLocalization_apply (r : R) :
    toLocalization k L R m r = algebraMap _ (Localization.AtPrime m) ((1 : L) ⊗ₜ[k] r) := rfl

/-- The map `R → (L ⊗[k] R)_m` is injective. -/
theorem toLocalization_injective {ϖ : R} (hϖ : Irreducible ϖ) :
    Function.Injective (toLocalization k L R m) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra h0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
  rw [map_mul, map_pow, (u.isUnit.map (toLocalization k L R m)).mul_right_eq_zero,
    toLocalization_apply] at hr
  exact algebraMap_pow_ne_zero k L R m hϖ.ne_zero n hr

/-- The map `R → (L ⊗[k] R)_m` is local when `m` contains the uniformizer. -/
theorem isLocalHom_toLocalization {ϖ : R} (hϖ : Irreducible ϖ) (htm : (1 : L) ⊗ₜ[k] ϖ ∈ m) :
    IsLocalHom (toLocalization k L R m) := by
  refine ⟨fun r hr => ?_⟩
  by_contra hnu
  have hrm : r ∈ maximalIdeal R := hnu
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hrm
  obtain ⟨c, rfl⟩ := hrm
  rw [map_mul, toLocalization_apply k L R m ϖ] at hr
  exact (mem_maximalIdeal _).mp
    (Ideal.mul_mem_left _ _ (algebraMap_mem_maximalIdeal k L R m htm)) hr

end Main

section Existence

variable (L : Type*) [Field L] [Algebra k L]
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra k R]

/-- There is a prime of `L ⊗[k] R` containing the uniformizer. -/
theorem exists_isPrime_tmul_mem {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ m : Ideal (L ⊗[k] R), m.IsPrime ∧ (1 : L) ⊗ₜ[k] ϖ ∈ m := by
  have : Nontrivial (L ⊗[k] ResidueField R) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k L _
      (algebraMap k L).injective (algebraMap k (ResidueField R)).injective
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (L ⊗[k] ResidueField R)
  refine ⟨M.comap (Algebra.TensorProduct.map (AlgHom.id k L)
    (IsScalarTower.toAlgHom k R (ResidueField R))), Ideal.comap_isPrime _ _, ?_⟩
  rw [Ideal.mem_comap]
  have : residue R ϖ = 0 := (residue_eq_zero_iff ϖ).mpr ((mem_maximalIdeal ϖ).mpr hϖ.not_isUnit)
  simp [this]

end Existence

section Residue

/-- A field which is a localization of a reduced zero-dimensional `L`-algebra `A` at a prime is
geometrically reduced over `L` as soon as `L̄ ⊗[L] A` is reduced. -/
theorem isGeometricallyReduced_of_forall_mul_eq {L A κ : Type*} [Field L] [CommRing A]
    [Algebra L A] [Field κ] [Algebra L κ] [Ring.KrullDimLE 0 A] [IsReduced A]
    [IsReduced (AlgebraicClosure L ⊗[L] A)] (θ : A →ₐ[L] κ)
    (hθ : ∀ z : κ, ∃ a s : A, θ s ≠ 0 ∧ z * θ s = θ a) : Algebra.IsGeometricallyReduced L κ := by
  have : (RingHom.ker θ).IsPrime := RingHom.ker_isPrime θ
  let : Algebra A κ := θ.toRingHom.toAlgebra
  have : IsScalarTower L A κ := IsScalarTower.of_algebraMap_eq fun l => (θ.commutes l).symm
  have hθa : ∀ a : A, algebraMap A κ a = θ a := fun _ => rfl
  have : IsLocalization (RingHom.ker θ).primeCompl κ := by
    refine ⟨⟨fun s => ?_, fun z => ?_, fun {a b} h => ?_⟩⟩
    · rw [hθa]
      exact isUnit_iff_ne_zero.mpr fun h => s.2 (RingHom.mem_ker.mpr h)
    · obtain ⟨a, s, hs, h⟩ := hθ z
      exact ⟨⟨a, ⟨s, fun h' => hs (RingHom.mem_ker.mp h')⟩⟩, h⟩
    · have hab : a - b ∈ RingHom.ker θ := by
        rw [RingHom.mem_ker, map_sub, sub_eq_zero]
        exact h
      obtain ⟨c, hc, hc'⟩ := exists_notMem_mul_eq_zero _ hab
      exact ⟨⟨c, hc⟩, by rw [mul_sub, sub_eq_zero] at hc'; exact hc'⟩
  rw [Algebra.isGeometricallyReduced_field_iff]
  let e := IsLocalization.tensorProductEquivOfMapIncludeRight L (AlgebraicClosure L)
    (RingHom.ker θ).primeCompl κ (Localization (((RingHom.ker θ).primeCompl).map
      (Algebra.TensorProduct.includeRight (R := L) (A := AlgebraicClosure L))))
  exact isReduced_of_injective e.toRingHom e.injective

variable (L : Type*) [Field L] [Algebra k L]
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra k R]
variable (m : Ideal (L ⊗[k] R)) [m.IsPrime]

/-- The residue field of the localization at a prime containing the uniformizer is geometrically
reduced over `L`. -/
theorem isGeometricallyReduced_residueField [Algebra.IsAlgebraic k L]
    [Algebra.IsGeometricallyReduced k (ResidueField R)] {ϖ : R} (hϖ : Irreducible ϖ)
    (htm : (1 : L) ⊗ₜ[k] ϖ ∈ m) :
    Algebra.IsGeometricallyReduced L (ResidueField (Localization.AtPrime m)) := by
  have := isLocalHom_toLocalization k L R m hϖ htm
  let g : ResidueField R →ₐ[k] ResidueField (Localization.AtPrime m) :=
    ResidueField.mapAlgHom (toLocalization k L R m)
  let θ : L ⊗[k] ResidueField R →ₐ[L] ResidueField (Localization.AtPrime m) :=
    Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId L _) g
  let π := Algebra.TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k R (ResidueField R))
  have key : ∀ x : L ⊗[k] R, θ (π x) = residue _ (algebraMap _ (Localization.AtPrime m) x) := by
    intro x
    induction x with
    | tmul l r =>
      have hl : algebraMap L (ResidueField (Localization.AtPrime m)) l =
          residue _ (algebraMap _ (Localization.AtPrime m) (l ⊗ₜ[k] (1 : R))) := rfl
      have h1 : θ (π (l ⊗ₜ[k] r)) =
          algebraMap L _ l * residue _ (toLocalization k L R m r) := by
        simp [θ, g, π]
      rw [h1, hl, toLocalization_apply, ← map_mul, ← map_mul,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have : Ring.KrullDimLE 0 (L ⊗[k] ResidueField R) := krullDimLE_zero_tensor k L _
  have : Algebra.IsAlgebraic k (AlgebraicClosure L) := Algebra.IsAlgebraic.trans k L _
  have : IsReduced (AlgebraicClosure L ⊗[L] (L ⊗[k] ResidueField R)) :=
    isReduced_of_injective (Algebra.TensorProduct.cancelBaseChange k L (AlgebraicClosure L)
      (AlgebraicClosure L) (ResidueField R)).toRingHom (AlgEquiv.injective _)
  refine isGeometricallyReduced_of_forall_mul_eq θ fun z => ?_
  obtain ⟨y, rfl⟩ := residue_surjective z
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective m.primeCompl y
  refine ⟨π b, π s, ?_, ?_⟩
  · rw [key, Ne, residue_eq_zero_iff, mem_maximalIdeal]
    exact not_not.mpr (IsLocalization.map_units _ s)
  · rw [key, key, ← map_mul, IsLocalization.mk'_spec]

end Residue

section FractionRing

variable (L : Type*) [Field L] [Algebra k L]
variable (R : Type*) [CommRing R] [Algebra k R]

/-- The map `L ⊗[k] R → L ⊗[k] Frac(R)`. -/
abbrev toTensorFractionRing : L ⊗[k] R →ₐ[k] L ⊗[k] FractionRing R :=
  Algebra.TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k R (FractionRing R))

/-- The map `L ⊗[k] R → L ⊗[k] Frac(R)` is injective, since `L` is flat over `k`. -/
theorem toTensorFractionRing_injective : Function.Injective (toTensorFractionRing k L R) := by
  have : ⇑(toTensorFractionRing k L R) =
      LinearMap.lTensor L (IsScalarTower.toAlgHom k R (FractionRing R)).toLinearMap := by
    funext b
    induction b with
    | tmul a r => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [this]
  exact Module.Flat.lTensor_preserves_injective_linearMap _
    (IsFractionRing.injective R (FractionRing R))

end FractionRing

section PurelyInseparable

/-- For a purely inseparable extension `L/k` and a geometrically reduced field `F` over `k`, the
ring `L ⊗[k] F` is a field. -/
theorem isField_tensor_of_isPurelyInseparable (L F : Type*) [Field L] [Algebra k L]
    [IsPurelyInseparable k L] [Field F] [Algebra k F] [Algebra.IsGeometricallyReduced k F] :
    IsField (L ⊗[k] F) := by
  have : Nontrivial (L ⊗[k] F) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k L F
      (algebraMap k L).injective (algebraMap k F).injective
  refine ⟨exists_pair_ne _, mul_comm, fun {x} hx => ?_⟩
  let e := Algebra.TensorProduct.comm k L F
  obtain ⟨n, hn, c, hc⟩ :=
    IsPurelyInseparable.exists_pow_mem_range_tensorProduct (k := k) (K := L) (R := F) (e x)
  have hc' : x ^ n = (1 : L) ⊗ₜ[k] c := by
    apply e.injective
    rw [map_pow, ← hc]
    simp [e]
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hx (IsNilpotent.eq_zero ⟨n, by rw [hc', TensorProduct.tmul_zero]⟩)
  have hu : IsUnit (x ^ n) := by
    rw [hc']
    exact (isUnit_iff_ne_zero.mpr hc0).map
      (Algebra.TensorProduct.includeRight : F →ₐ[k] L ⊗[k] F)
  obtain ⟨y, hy⟩ := ((isUnit_pow_iff hn.ne').mp hu).exists_right_inv
  exact ⟨y, hy⟩

variable (L : Type*) [Field L] [Algebra k L]
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra k R]

/-- The reduction map `L ⊗[k] R → L ⊗[k] κ(R)`. -/
local notation "ρ" => Algebra.TensorProduct.map (AlgHom.id k L)
  (IsScalarTower.toAlgHom k R (ResidueField R))

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The map `R → L ⊗[k] R` is integral when `L` is integral over `k`. -/
theorem includeRight_isIntegral [Algebra.IsIntegral k L] :
    (Algebra.TensorProduct.includeRight : R →ₐ[k] L ⊗[k] R).toRingHom.IsIntegral := by
  have h : (Algebra.TensorProduct.includeRight : R →ₐ[k] L ⊗[k] R).toRingHom =
      (Algebra.TensorProduct.comm k R L).toRingHom.comp (algebraMap R (R ⊗[k] L)) := by
    ext r
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [h]
  exact RingHom.IsIntegral.trans _ _ (algebraMap_isIntegral_iff.mpr inferInstance)
    (RingHom.isIntegral_of_surjective _ (Algebra.TensorProduct.comm k R L).surjective)

/-- Every maximal ideal of `L ⊗[k] R` contains the kernel of the reduction map. -/
theorem ker_map_residue_le [Algebra.IsIntegral k L] (M : Ideal (L ⊗[k] R)) [M.IsMaximal] :
    RingHom.ker ρ ≤ M := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [ker_map_residue k R L hϖ, Ideal.span_le, Set.singleton_subset_iff]
  have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _ (includeRight_isIntegral k L R) M
  have hM : M.comap (Algebra.TensorProduct.includeRight : R →ₐ[k] L ⊗[k] R).toRingHom =
      maximalIdeal R := IsLocalRing.eq_maximalIdeal hmax
  have hϖM : ϖ ∈ M.comap (Algebra.TensorProduct.includeRight : R →ₐ[k] L ⊗[k] R).toRingHom := by
    rw [hM]
    exact (mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
  exact hϖM

variable [IsPurelyInseparable k L] [Algebra.IsGeometricallyReduced k (ResidueField R)]

/-- An element of `L ⊗[k] R` is a unit if and only if its reduction is nonzero. -/
theorem isUnit_iff_map_residue_ne_zero (x : L ⊗[k] R) : IsUnit x ↔ ρ x ≠ 0 := by
  have hF := isField_tensor_of_isPurelyInseparable k L (ResidueField R)
  have : Nontrivial (L ⊗[k] ResidueField R) := ⟨hF.exists_pair_ne⟩
  constructor
  · intro hx h0
    have := hx.map ρ
    rw [h0] at this
    exact not_isUnit_zero this
  · intro hx
    by_contra hnu
    obtain ⟨M, hM, hxM⟩ := exists_max_ideal_of_mem_nonunits hnu
    have hsurj := map_residue_surjective k R L
    have : (M.map ρ).IsPrime := Ideal.map_isPrime_of_surjective hsurj (ker_map_residue_le k L R M)
    obtain ⟨y, hy⟩ := hF.mul_inv_cancel hx
    apply this.ne_top
    rw [Ideal.eq_top_iff_one, ← hy]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hxM)

/-- `L ⊗[k] R` is a local ring. -/
theorem isLocalRing_tensor : IsLocalRing (L ⊗[k] R) := by
  have : Nontrivial (L ⊗[k] R) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k L R
      (algebraMap k L).injective (algebraMap k R).injective
  refine IsLocalRing.of_nonunits_add fun a b ha hb => ?_
  rw [mem_nonunits_iff, isUnit_iff_map_residue_ne_zero, not_not] at ha hb ⊢
  rw [map_add, ha, hb, add_zero]

/-- The image of a uniformizer of `R` is not a unit in `L ⊗[k] R`. -/
theorem tmul_not_isUnit {ϖ : R} (hϖ : Irreducible ϖ) : ¬IsUnit ((1 : L) ⊗ₜ[k] ϖ) := by
  rw [isUnit_iff_map_residue_ne_zero, not_not]
  have : residue R ϖ = 0 := (residue_eq_zero_iff ϖ).mpr ((mem_maximalIdeal ϖ).mpr hϖ.not_isUnit)
  simp [this]

/-- The map `R → L ⊗[k] R` is local. -/
theorem isLocalHom_includeRight :
    IsLocalHom ((Algebra.TensorProduct.includeRight : R →ₐ[k] L ⊗[k] R) : R →+* L ⊗[k] R) := by
  refine ⟨fun r hr => ?_⟩
  by_contra hnu
  rw [AlgHom.coe_toRingHom, isUnit_iff_map_residue_ne_zero] at hr
  apply hr
  have : residue R r = 0 := (residue_eq_zero_iff r).mpr ((mem_maximalIdeal r).mpr hnu)
  simp [this]

/-- Every element of `L ⊗[k] R` is zero or a unit times a power of the uniformizer. -/
theorem tensor_eq_zero_or {ϖ : R} (hϖ : Irreducible ϖ) (y : L ⊗[k] R) :
    y = 0 ∨ ∃ (j : ℕ) (u : L ⊗[k] R), IsUnit u ∧ y = ((1 : L) ⊗ₜ[k] ϖ) ^ j * u := by
  have := isLocalRing_tensor k L R
  have htm : (1 : L) ⊗ₜ[k] ϖ ∈ maximalIdeal (L ⊗[k] R) := tmul_not_isUnit k L R hϖ
  let e := IsLocalization.atUnits (L ⊗[k] R) (maximalIdeal (L ⊗[k] R)).primeCompl
    (S := Localization.AtPrime (maximalIdeal (L ⊗[k] R)))
    fun x hx => (IsUnit.mem_submonoid_iff x).mpr (IsLocalRing.notMem_maximalIdeal.mp hx)
  have he : ∀ z, e z = algebraMap _ (Localization.AtPrime (maximalIdeal (L ⊗[k] R))) z :=
    fun _ => rfl
  rcases localization_eq_zero_or k L R (maximalIdeal (L ⊗[k] R)) hϖ htm
    (algebraMap _ _ y) with h0 | ⟨j, u, hu, h⟩
  · left
    apply e.injective
    rw [he, h0, map_zero]
  · right
    refine ⟨j, e.symm u, hu.map e.symm, e.injective ?_⟩
    rw [map_mul, map_pow, e.apply_symm_apply, he, he, h]

theorem tmul_pow_ne_zero {ϖ : R} (hϖ : Irreducible ϖ) (j : ℕ) : ((1 : L) ⊗ₜ[k] ϖ) ^ j ≠ 0 := by
  have := isLocalRing_tensor k L R
  intro h
  exact algebraMap_pow_ne_zero k L R (maximalIdeal (L ⊗[k] R)) hϖ.ne_zero j
    (by rw [← map_pow, h, map_zero])

/-- `L ⊗[k] R` is a domain. -/
theorem isDomain_tensor : IsDomain (L ⊗[k] R) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have := isLocalRing_tensor k L R
  exact isDomain_of_forall_eq_zero_or _ (tmul_pow_ne_zero k L R hϖ) (tensor_eq_zero_or k L R hϖ)

/-- `L ⊗[k] R` is a discrete valuation ring. -/
theorem isDiscreteValuationRing_tensor [IsDomain (L ⊗[k] R)] :
    IsDiscreteValuationRing (L ⊗[k] R) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  exact isDiscreteValuationRing_of_forall_eq_zero_or _ (tmul_not_isUnit k L R hϖ)
    (by simpa using tmul_pow_ne_zero k L R hϖ 1) (tensor_eq_zero_or k L R hϖ)

/-- The image of a uniformizer of `R` is irreducible in `L ⊗[k] R`. -/
theorem irreducible_tmul [IsDomain (L ⊗[k] R)] {ϖ : R} (hϖ : Irreducible ϖ) :
    Irreducible ((1 : L) ⊗ₜ[k] ϖ) := by
  have := isDiscreteValuationRing_tensor k L R
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  ext x
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_map_residue_ne_zero, not_not,
    ← RingHom.mem_ker, ker_map_residue k R L hϖ]

/-- `L ⊗[k] Frac(R)` is the fraction ring of `L ⊗[k] R`, through `toTensorFractionRing`. -/
theorem isFractionRing_tensor :
    letI := (toTensorFractionRing k L R).toRingHom.toAlgebra
    IsFractionRing (L ⊗[k] R) (L ⊗[k] FractionRing R) := by
  let := (toTensorFractionRing k L R).toRingHom.toAlgebra
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have := isDomain_tensor k L R
  have hmap : ∀ x, algebraMap (L ⊗[k] R) (L ⊗[k] FractionRing R) x =
      toTensorFractionRing k L R x := fun _ => rfl
  have hR0 : ∀ b : R, b ≠ 0 → (1 : L) ⊗ₜ[k] b ≠ 0 := fun b hb h =>
    hb (Algebra.TensorProduct.includeRight_injective (algebraMap k L).injective
      (h.trans (map_zero Algebra.TensorProduct.includeRight).symm))
  refine ⟨⟨fun s => ?_, fun z => ?_, fun {a b} h => ?_⟩⟩
  · rcases tensor_eq_zero_or k L R hϖ s with h0 | ⟨j, u, hu, hsu⟩
    · exact absurd h0 (nonZeroDivisors.ne_zero s.2)
    rw [hsu, map_mul, map_pow]
    refine (IsUnit.pow j ?_).mul (hu.map _)
    rw [hmap]
    have hϖK : algebraMap R (FractionRing R) ϖ ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
    simpa using (isUnit_iff_ne_zero.mpr hϖK).map
      (Algebra.TensorProduct.includeRight : FractionRing R →ₐ[k] L ⊗[k] FractionRing R)
  · induction z with
    | tmul l x =>
      obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) x
      refine ⟨⟨l ⊗ₜ a, ⟨(1 : L) ⊗ₜ (b : R),
        mem_nonZeroDivisors_of_ne_zero (hR0 _ (nonZeroDivisors.ne_zero b.2))⟩⟩, ?_⟩
      simp only [hmap, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        IsScalarTower.coe_toAlgHom', Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      rw [hab]
    | add z w hz hw =>
      obtain ⟨⟨a, s⟩, has⟩ := hz
      obtain ⟨⟨b, t⟩, hbt⟩ := hw
      refine ⟨⟨a * t + b * s, s * t⟩, ?_⟩
      simp only [Submonoid.coe_mul, map_mul, map_add] at has hbt ⊢
      rw [← has, ← hbt]
      ring
  · exact ⟨1, by rw [toTensorFractionRing_injective k L R h]⟩

/-- The residue field of the local ring `L ⊗[k] R` is geometrically reduced over `L`. -/
theorem isGeometricallyReduced_residueField_tensor [IsLocalRing (L ⊗[k] R)] :
    Algebra.IsGeometricallyReduced L (ResidueField (L ⊗[k] R)) := by
  have : IsLocalHom (Algebra.TensorProduct.includeRight : R →ₐ[k] L ⊗[k] R) :=
    ⟨fun r hr => (isLocalHom_includeRight k L R).map_nonunit r hr⟩
  let g : ResidueField R →ₐ[k] ResidueField (L ⊗[k] R) :=
    ResidueField.mapAlgHom (Algebra.TensorProduct.includeRight : R →ₐ[k] L ⊗[k] R)
  let θ : L ⊗[k] ResidueField R →ₐ[L] ResidueField (L ⊗[k] R) :=
    Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId L _) g
  have key : ∀ x : L ⊗[k] R, θ (ρ x) = residue _ x := by
    intro x
    induction x with
    | tmul l r =>
      have hl : algebraMap L (ResidueField (L ⊗[k] R)) l = residue _ (l ⊗ₜ[k] (1 : R)) := rfl
      have h1 : θ (ρ (l ⊗ₜ[k] r)) = algebraMap L _ l * residue _ ((1 : L) ⊗ₜ[k] r) := by
        simp [θ, g]
      rw [h1, hl, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have : Ring.KrullDimLE 0 (L ⊗[k] ResidueField R) := krullDimLE_zero_tensor k L _
  have : Algebra.IsAlgebraic k (AlgebraicClosure L) := Algebra.IsAlgebraic.trans k L _
  have : IsReduced (AlgebraicClosure L ⊗[L] (L ⊗[k] ResidueField R)) :=
    isReduced_of_injective (Algebra.TensorProduct.cancelBaseChange k L (AlgebraicClosure L)
      (AlgebraicClosure L) (ResidueField R)).toRingHom (AlgEquiv.injective _)
  refine isGeometricallyReduced_of_forall_mul_eq θ fun z => ?_
  obtain ⟨y, rfl⟩ := residue_surjective z
  exact ⟨ρ y, 1, by simp, by rw [map_one, mul_one, key]⟩

end PurelyInseparable

end Langlands.CommutativeAlgebra.DVRAlgebraicBaseChange

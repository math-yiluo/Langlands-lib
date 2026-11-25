import Langlands.ClassFieldTheory.Local.QuadraticNormIndex
import Langlands.Group.Unitary.Basic
import Langlands.HarmonicAnalysis.Bicharacter.SelfDual
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.FieldSimp

/-!
# Balls of the norm form of a quadratic extension of a nonarchimedean local field

Let `F` be a nonarchimedean local field and `E = F(δ)` a quadratic extension with conjugation `c`
(`IsQuadraticInvolution c δ`).

* `normSign E t ∈ {1, -1} ⊆ ℂ` is the quadratic character `η_{E/F}`: `1` on the norms from `E`;
  it is multiplicative (`normSign_mul`) and equal to `normResidueSign F E` (`normSign_eq_normResidueSign`).
* `valuationBall s = {x | v x ≤ v s}` is a compact open subset of `F`.
* For a non-square `d` the norm form satisfies `v(2a)² ≤ v(a² - d b²)`
  (`valuation_two_mul_sq_le`; Hensel's lemma for `X² + X + t`), so the sets
  `{z ∈ E | v(N_{E/F} z) ≤ v(s)}` are compact open subgroups of `E`
  (`exists_addSubgroup_norm_mem_valuationBall`).
-/

noncomputable section

open ValuativeRel

namespace Langlands.LocalClassField

/-- The quadratic character `η_{E/F}` as a complex number: `1` on the norms from `E`, `-1` on the
other elements of `Fˣ`. For a quadratic extension of nonarchimedean local fields it is
`normResidueSign F E` (`normSign_eq_normResidueSign`). -/
def normSign {F : Type} [Field F] (E : Type) [Field E] [Algebra F E] (t : Fˣ) : ℂ :=
  open Classical in if t ∈ (Units.map (Algebra.norm F : E →* F)).range then 1 else -1

/-- `normSign` is the complex value of `normResidueSign`. -/
theorem normSign_eq_normResidueSign {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    [IsGalois F E] (t : Fˣ) : normSign E t = ((normResidueSign F E t : ℤ) : ℂ) := by
  classical
  unfold normSign
  by_cases h : t ∈ (Units.map (Algebra.norm F : E →* F)).range
  · simp [h, normResidueSign_of_mem h]
  · simp [h, normResidueSign_of_notMem h]

/-- `normSign` is multiplicative for a quadratic extension `E = F(δ)` (index two of the norms,
`mul_mem_range_norm_of_finrank_eq_two`), in characteristic `≠ 2`. -/
theorem normSign_mul' {F : Type} [Field F] [NeZero (2 : F)] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {E : Type} [Field E] [Algebra F E] {c : E →ₐ[F] E} {δ : E}
    (hE : IsQuadraticInvolution c δ) (s t : Fˣ) :
    normSign E (s * t) = normSign E s * normSign E t := by
  classical
  have : IsGalois F E := hE.isGalois
  set H := (Units.map (Algebra.norm F : E →* F)).range with hH
  unfold normSign
  rw [← hH]
  by_cases hs : s ∈ H <;> by_cases ht : t ∈ H
  · simp [hs, ht, H.mul_mem hs ht]
  · have : s * t ∉ H := fun h => ht ((H.mul_mem_cancel_left hs).mp h)
    simp [hs, ht, this]
  · have : s * t ∉ H := fun h => hs ((H.mul_mem_cancel_right ht).mp h)
    simp [hs, ht, this]
  · have : s * t ∈ H := mul_mem_range_norm_of_finrank_eq_two hE.finrank_eq_two hs ht
    simp [hs, ht, this]

/-- `normSign` is multiplicative for a quadratic extension `E = F(δ)` (index two of the norms,
`mul_mem_range_norm_of_finrank_eq_two`); `normSign_mul'` in characteristic `≠ 2`. -/
theorem normSign_mul {F : Type} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {E : Type} [Field E] [Algebra F E] {c : E →ₐ[F] E} {δ : E}
    (hE : IsQuadraticInvolution c δ) (s t : Fˣ) :
    normSign E (s * t) = normSign E s * normSign E t :=
  normSign_mul' hE s t

/-- The closed ball `{x | v x ≤ v s}` of a valued field. -/
abbrev valuationBall {F : Type*} [Field F] [ValuativeRel F] (s : Fˣ) : Set F :=
  {x | valuation F x ≤ valuation F (s : F)}

/-- Over a nonarchimedean local field the closed ball `{x | v x ≤ v s}` is compact. -/
theorem isCompact_valuationBall {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (s : Fˣ) : IsCompact (valuationBall s) :=
  IsNonarchimedeanLocalField.isCompact_closedBall F _

/-- Over a nonarchimedean local field the closed ball `{x | v x ≤ v s}` is open. -/
theorem isOpen_valuationBall {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (s : Fˣ) : IsOpen (valuationBall s) :=
  HarmonicAnalysis.isOpen_setOf_valuation_le s

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private lemma eval_zero_quadratic_mem_maximalIdeal (t : F) (ht : valuation F t < 1)
    (htmem : t ∈ 𝒪[F]) :
    Polynomial.eval 0 (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (⟨t, htmem⟩ : 𝒪[F]) :
      Polynomial 𝒪[F]) ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    zero_pow two_ne_zero, zero_add]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers _).isUnit_iff_valuation_eq_one]
  exact ht.ne

private lemma exists_sq_eq_one_sub_four_mul {t : F} (ht : valuation F t < 1) :
    ∃ w : F, (1 + 2 * w) ^ 2 = 1 - 4 * t := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  have hH : HenselianRing 𝒪[F] (IsLocalRing.maximalIdeal 𝒪[F]) :=
    IsAdicComplete.henselianRing _ _
  have htmem : t ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).2 ht.le
  have hf : (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (⟨t, htmem⟩ : 𝒪[F]) :
      Polynomial 𝒪[F]).Monic := by
    monicity!
  have h1 : IsUnit ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[F]))
      (Polynomial.eval 0 (Polynomial.derivative (Polynomial.X ^ 2 + Polynomial.X +
        Polynomial.C (⟨t, htmem⟩ : 𝒪[F]) : Polynomial 𝒪[F])))) := by
    simp
  obtain ⟨w, hw, -⟩ := hH.is_henselian _ hf 0 (eval_zero_quadratic_mem_maximalIdeal t ht htmem) h1
  refine ⟨(w : F), ?_⟩
  have h := congrArg (fun x : 𝒪[F] => (x : F)) hw.eq_zero
  simp at h
  linear_combination 4 * h

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private lemma valuation_two_le_one : valuation F (2 : F) ≤ 1 := by
  rw [← one_add_one_eq_two]
  exact (valuation F).map_add_le (by simp) (by simp)


/-- For a non-square `d`, the norm form `a² - d b²` satisfies `v(2a)² ≤ v(a² - d b²)`. -/
theorem valuation_two_mul_sq_le {d : F} (hd : ∀ r : F, r ^ 2 ≠ d) (a b : F) :
    valuation F (2 * a) ^ 2 ≤ valuation F (a ^ 2 - d * b ^ 2) := by
  rcases eq_or_ne (2 * a) 0 with h2a | h2a
  · simp [h2a]
  by_contra hlt
  push Not at hlt
  set e := a ^ 2 - d * b ^ 2 with he
  have ha : a ≠ 0 := right_ne_zero_of_mul h2a
  have h2 : (2 : F) ≠ 0 := left_ne_zero_of_mul h2a
  have het : e = e / (2 * a) ^ 2 * (2 * a) ^ 2 := by field_simp
  have ht : valuation F (e / (2 * a) ^ 2) < 1 := by
    by_contra hge
    push Not at hge
    have hv : valuation F e = valuation F (e / (2 * a) ^ 2) * valuation F (2 * a) ^ 2 := by
      rw [← map_pow, ← map_mul, ← het]
    have : valuation F (2 * a) ^ 2 ≤ valuation F e := by
      rw [hv]
      exact le_mul_of_one_le_left' hge
    exact (not_le.2 hlt) this
  obtain ⟨w, hw⟩ := exists_sq_eq_one_sub_four_mul ht
  rcases eq_or_ne b 0 with hb | hb
  · have hea : e = a ^ 2 := by simp [he, hb]
    have : valuation F (2 * a) ^ 2 ≤ valuation F (a ^ 2) := by
      rw [map_mul, map_pow, mul_pow]
      exact mul_le_of_le_one_left' (pow_le_one₀ zero_le valuation_two_le_one)
    rw [hea] at hlt
    exact (not_le.2 hlt) this
  apply hd (a / b * (1 + 2 * w))
  rw [mul_pow, hw]
  field_simp
  rw [he]
  ring

/-- The pairs `(a, b)` with `a² - d b²` in the ball `{x | v x ≤ v s}`, a subgroup by
`valuation_two_mul_sq_le`. -/
private def normFormBall {d : F} (hd : ∀ r : F, r ^ 2 ≠ d) (s : Fˣ) : AddSubgroup (F × F) where
  carrier := {p | p.1 ^ 2 - d * p.2 ^ 2 ∈ valuationBall s}
  zero_mem' := by simp [valuationBall]
  neg_mem' := by
    intro p hp
    simpa using hp
  add_mem' := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h h'
    simp only [valuationBall, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add] at h h' ⊢
    have e : (a + a') ^ 2 - d * (b + b') ^ 2 =
        (a ^ 2 - d * b ^ 2) + (a' ^ 2 - d * b' ^ 2) + 2 * (a * a' - d * b * b') := by ring
    have k := valuation_two_mul_sq_le hd (a * a' - d * b * b') (a * b' - b * a')
    have e2 : (a * a' - d * b * b') ^ 2 - d * (a * b' - b * a') ^ 2 =
        (a ^ 2 - d * b ^ 2) * (a' ^ 2 - d * b' ^ 2) := by ring
    rw [e2, map_mul (valuation F) (a ^ 2 - d * b ^ 2)] at k
    have k2 : valuation F (2 * (a * a' - d * b * b')) ≤ valuation F (s : F) := by
      refine le_of_pow_le_pow_left₀ two_ne_zero zero_le (k.trans ?_)
      rw [sq (valuation F (s : F))]
      exact mul_le_mul' h h'
    rw [e]
    exact (valuation F).map_add_le ((valuation F).map_add_le h h') k2

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private lemma mem_union_of_valuation_sq_le (u : Fˣ) {y : F} (h : valuation F y ^ 2 ≤ valuation F
    (u : F)) :
    y ∈ valuationBall (1 : Fˣ) ∪ valuationBall u := by
  simp only [valuationBall, Set.mem_union, Set.mem_ofPred_eq, Units.val_one, map_one]
  by_cases hy : valuation F y ≤ 1
  · exact Or.inl hy
  · right
    push Not at hy
    calc valuation F y = valuation F y * 1 := (mul_one _).symm
      _ ≤ valuation F y * valuation F y := by gcongr
      _ = valuation F y ^ 2 := (sq _).symm
      _ ≤ _ := h

private lemma isCompact_isOpen_normFormBall {d : F} (hd : ∀ r : F, r ^ 2 ≠ d) (hd0 : d ≠ 0)
    (h2 : (2 : F) ≠ 0) (s : Fˣ) :
    IsCompact ((normFormBall hd s : AddSubgroup (F × F)) : Set (F × F)) ∧
      IsOpen ((normFormBall hd s : AddSubgroup (F × F)) : Set (F × F)) := by
  have hq : Continuous fun p : F × F => p.1 ^ 2 - d * p.2 ^ 2 := by fun_prop
  have hset : ((normFormBall hd s : AddSubgroup (F × F)) : Set (F × F)) =
      (fun p : F × F => p.1 ^ 2 - d * p.2 ^ 2) ⁻¹' valuationBall s := rfl
  refine ⟨?_, ?_⟩
  · set D : Fˣ := Units.mk0 d hd0
    set K₁ := (fun y : F => (2 : F)⁻¹ * y) ''
      (valuationBall (1 : Fˣ) ∪ valuationBall s)
    set K₂ := (fun y : F => (2 * d)⁻¹ * y) ''
      (valuationBall (1 : Fˣ) ∪ valuationBall (D * s))
    have hK₁ : IsCompact K₁ :=
      ((isCompact_valuationBall _).union (isCompact_valuationBall _)).image
        (continuous_const.mul continuous_id)
    have hK₂ : IsCompact K₂ :=
      ((isCompact_valuationBall _).union (isCompact_valuationBall _)).image
        (continuous_const.mul continuous_id)
    have hclosed : IsClosed ((normFormBall hd s : AddSubgroup (F × F)) : Set (F × F)) := by
      rw [hset]
      exact (isCompact_valuationBall s).isClosed.preimage hq
    refine (hK₁.prod hK₂).of_isClosed_subset hclosed ?_
    rintro ⟨a, b⟩ hp
    have hp' : valuation F (a ^ 2 - d * b ^ 2) ≤ valuation F (s : F) := hp
    refine ⟨⟨2 * a, mem_union_of_valuation_sq_le s ?_, by field_simp⟩,
      ⟨2 * (d * b), mem_union_of_valuation_sq_le (D * s) ?_, by field_simp⟩⟩
    · rw [← map_pow]
      exact (by simpa [map_pow] using valuation_two_mul_sq_le hd a b : valuation F
          ((2 * a) ^ 2) ≤ _).trans hp'
    · have k := valuation_two_mul_sq_le hd (d * b) a
      have e : (d * b) ^ 2 - d * a ^ 2 = -d * (a ^ 2 - d * b ^ 2) := by ring
      rw [e, map_mul (valuation F) (-d), Valuation.map_neg] at k
      refine k.trans ?_
      simp only [D, Units.val_mul, Units.val_mk0, map_mul]
      gcongr
  · rw [hset]
    exact (isOpen_valuationBall s).preimage hq


/-- For a quadratic extension `E = F(δ)` of a nonarchimedean local field of characteristic `≠ 2`
(`c` the conjugation, `c δ = -δ`), the set `{z | v(N_{E/F} z) ≤ v(s)}` is a compact open subgroup
of `E`. -/
theorem exists_addSubgroup_norm_mem_valuationBall' [NeZero (2 : F)] {E : Type} [Field E]
    [Algebra F E]
    [TopologicalSpace E] [IsModuleTopology F E] {c : E →ₐ[F] E} {δ : E}
    (hE : IsQuadraticInvolution c δ) (s : Fˣ) :
    ∃ L : AddSubgroup E, (L : Set E) = {z | Algebra.norm F z ∈ valuationBall s} ∧
      IsCompact (L : Set E) ∧ IsOpen (L : Set E) := by
  have : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have hneg : c δ = -δ := hE.map_eq_neg
  have hfix : c (δ ^ 2) = δ ^ 2 := by rw [map_pow, hneg, neg_sq]
  obtain ⟨d, hdδ⟩ := hE.exists_of_fixed hfix
  have hinj := hE.algebraMap_injective
  have h2E : (2 : E) ≠ 0 := by
    intro h
    apply two_ne_zero (α := F)
    apply hinj
    rw [map_ofNat, map_zero]
    exact h
  have hd : ∀ r : F, r ^ 2 ≠ d := by
    intro r hr
    have hc : c (algebraMap F E r) = algebraMap F E r := c.commutes r
    have hsq : (δ - algebraMap F E r) * (δ + algebraMap F E r) = 0 := by
      rw [← hr, map_pow] at hdδ
      linear_combination hdδ
    have hδ0 : δ = 0 := by
      rcases mul_eq_zero.1 hsq with h | h
      · have h' : δ = algebraMap F E r := sub_eq_zero.1 h
        have hr' := hneg
        rw [h', hc] at hr'
        have : (2 : E) * algebraMap F E r = 0 := by linear_combination hr'
        rw [h']
        exact (mul_eq_zero.1 this).resolve_left h2E
      · have h' : δ = -algebraMap F E r := eq_neg_of_add_eq_zero_left h
        have hr' := hneg
        rw [h', map_neg, hc] at hr'
        have : (2 : E) * algebraMap F E r = 0 := by linear_combination -hr'
        rw [h', (mul_eq_zero.1 this).resolve_left h2E, neg_zero]
    exact hE.isUnit.ne_zero hδ0
  have hd0 : d ≠ 0 := fun h => hd 0 (by simp [h])
  have hnorm : ∀ a b : F, Algebra.norm F (a • (1 : E) + b • δ) = a ^ 2 - d * b ^ 2 := by
    intro a b
    apply hinj
    rw [hE.algebraMap_norm]
    simp only [Algebra.smul_def, mul_one, map_add, map_mul, AlgHom.commutes, hneg, map_sub,
      map_pow]
    linear_combination (-(algebraMap F E b) ^ 2) * hdδ
  obtain ⟨bs, hb0, hb1⟩ := hE.exists_basis
  let ψ : E →ₗ[F] F × F :=
    (LinearMap.proj 0 ∘ₗ bs.equivFun.toLinearMap).prod (LinearMap.proj 1 ∘ₗ bs.equivFun.toLinearMap)
  have hψ : Continuous ψ := IsModuleTopology.continuous_of_linearMap ψ
  have hφψ : ∀ z : E, (ψ z).1 • (1 : E) + (ψ z).2 • δ = z := by
    intro z
    have h := bs.sum_equivFun z
    rw [Fin.sum_univ_two, hb0, hb1] at h
    exact h
  have : ContinuousSMul F E := IsModuleTopology.toContinuousSMul F E
  have : ContinuousAdd E := IsModuleTopology.toContinuousAdd F E
  have hφ : Continuous fun p : F × F => p.1 • (1 : E) + p.2 • δ :=
    (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)
  obtain ⟨hK, hU⟩ := isCompact_isOpen_normFormBall hd hd0 two_ne_zero s
  refine ⟨(normFormBall hd s).comap ψ, ?_, ?_, ?_⟩
  · ext z
    change (ψ z).1 ^ 2 - d * (ψ z).2 ^ 2 ∈ valuationBall s ↔ _
    rw [← hnorm, hφψ]
    rfl
  · have himg : (((normFormBall hd s).comap ψ : AddSubgroup E) : Set E) =
        (fun p : F × F => p.1 • (1 : E) + p.2 • δ) ''
          ((normFormBall hd s : AddSubgroup (F × F)) : Set (F × F)) := by
      ext z
      constructor
      · intro hz
        exact ⟨ψ z, hz, hφψ z⟩
      · rintro ⟨p, hp, rfl⟩
        change (ψ _).1 ^ 2 - d * (ψ _).2 ^ 2 ∈ valuationBall s
        rw [← hnorm, hφψ, hnorm]
        exact hp
    rw [himg]
    exact hK.image hφ
  · exact hU.preimage hψ

/-- For a quadratic extension `E = F(δ)` of a nonarchimedean local field (`c` the conjugation,
`c δ = -δ`), the set `{z | v(N_{E/F} z) ≤ v(s)}` is a compact open subgroup of `E`
(`exists_addSubgroup_norm_mem_valuationBall'` in characteristic `≠ 2`). -/
theorem exists_addSubgroup_norm_mem_valuationBall [CharZero F] {E : Type} [Field E] [Algebra F E]
    [TopologicalSpace E] [IsModuleTopology F E] {c : E →ₐ[F] E} {δ : E}
    (hE : IsQuadraticInvolution c δ) (s : Fˣ) :
    ∃ L : AddSubgroup E, (L : Set E) = {z | Algebra.norm F z ∈ valuationBall s} ∧
      IsCompact (L : Set E) ∧ IsOpen (L : Set E) :=
  exists_addSubgroup_norm_mem_valuationBall' hE s

end Langlands.LocalClassField

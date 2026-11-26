import Langlands.Global.LeftCosetSemidirectFiniteVolume
import Mathlib.MeasureTheory.Integral.Prod

/-! # Fundamental domains and Haar measures of topological semidirect products -/

noncomputable section

universe u v w x

open MeasureTheory Set Topology
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Global.LeftCosetSpace.Semidirect

variable {N : Type u} {M : Type v} {H : Type w} [Group N] [Group M] [Group H]
  (i : N →* H) (j : M →* H) (p : H →* M)
  (hpj : ∀ m, p (j m) = m) (hker : ∀ h, p h = 1 → ∃ n, i n = h) (hpi : ∀ n, p (i n) = 1)

/-- The product set of a transversal of `N` and a transversal of `M`. -/
def prodTransversal (tN : Set N) (tM : Set M) : Set H :=
  {h | normalPart i j p hpj hker h ∈ tN ∧ p h ∈ tM}

include hpi in
theorem mul_mem_prodTransversal_iff (hi : Function.Injective i) (tN : Set N) (tM : Set M)
    (n : N) (m : M) :
    i n * j m ∈ prodTransversal i j p hpj hker tN tM ↔ n ∈ tN ∧ m ∈ tM := by
  change normalPart i j p hpj hker (i n * j m) ∈ tN ∧ p (i n * j m) ∈ tM ↔ _
  rw [normalPart_mul j p hpj hker hpi hi, p_i_mul_j i j p hpj hpi]

include hpi in
/-- **Product transversals.** Let `Λ ≤ H` be a subgroup with `j (p λ) ∈ Λ` for `λ ∈ Λ`, so that
`Λ` is the semidirect product of `Λ ∩ i(N)` and `Λ ∩ j(M)`. If `tN` and `tM` are transversals
for the left actions of `i⁻¹(Λ)` on `N` and `j⁻¹(Λ)` on `M`, then the set of `i n * j m` with
`n ∈ tN` and `m ∈ tM` is a transversal for the left action of `Λ` on `H`. -/
theorem prodTransversal_unique (hi : Function.Injective i) (Λ : Subgroup H)
    (hΛp : ∀ x ∈ Λ, j (p x) ∈ Λ)
    {tN : Set N} (htN : ∀ n, ∃! γ : Λ.comap i, (γ : N) * n ∈ tN)
    {tM : Set M} (htM : ∀ m, ∃! γ : Λ.comap j, (γ : M) * m ∈ tM) (h : H) :
    ∃! γ : Λ, (γ : H) * h ∈ prodTransversal i j p hpj hker tN tM := by
  set n := normalPart i j p hpj hker h
  set m := p h
  have hh : i n * j m = h := i_normalPart_mul_j_p i j p hpj hker h
  -- decomposition of an element of `Λ`
  have hdec : ∀ γ : Λ, ∃ κ : Λ.comap i, ∃ α : Λ.comap j, (γ : H) = i κ * j α := by
    intro γ
    refine ⟨⟨normalPart i j p hpj hker γ, ?_⟩, ⟨p γ, hΛp _ γ.property⟩, ?_⟩
    · change i (normalPart i j p hpj hker γ) ∈ Λ
      rw [i_normalPart]
      exact Λ.mul_mem γ.property (Λ.inv_mem (hΛp _ γ.property))
    · exact (i_normalPart_mul_j_p i j p hpj hker γ).symm
  have hact : ∀ (κ : N) (α : M), i κ * j α * h =
      i (κ * conjFun i j p hpj hker α n) * j (α * m) := by
    intro κ α
    rw [← hh, map_mul, map_mul, i_conjFun i j p hpj hker hpi]
    group
  obtain ⟨α, hα, hαu⟩ := htM m
  obtain ⟨κ, hκ, hκu⟩ := htN (conjFun i j p hpj hker α n)
  refine ⟨⟨i κ * j α, Λ.mul_mem κ.property α.property⟩, ?_, ?_⟩
  · change i κ * j α * h ∈ _
    rw [hact, mul_mem_prodTransversal_iff i j p hpj hker hpi hi]
    exact ⟨hκ, hα⟩
  · intro γ hγ
    obtain ⟨κ', α', hγe⟩ := hdec γ
    rw [hγe, hact, mul_mem_prodTransversal_iff i j p hpj hker hpi hi] at hγ
    have hα' : α' = α := hαu α' hγ.2
    subst hα'
    have hκ' : κ' = κ := hκu κ' hγ.1
    subst hκ'
    exact Subtype.ext hγe

variable [TopologicalSpace N] [TopologicalSpace M] [TopologicalSpace H] [IsTopologicalGroup H]

include hpi in
theorem prodTransversal_eq_preimage (hi : IsEmbedding i) (hj : Continuous j) (hp : Continuous p)
    (tN : Set N) (tM : Set M) :
    prodTransversal i j p hpj hker tN tM =
      (prodHomeomorph i j p hpj hker hpi hi hj hp).symm ⁻¹' (tN ×ˢ tM) := rfl

variable [IsTopologicalGroup N] [IsTopologicalGroup M]
  [LocallyCompactSpace N] [LocallyCompactSpace M] [LocallyCompactSpace H]
  [SecondCountableTopology N] [SecondCountableTopology M] [SecondCountableTopology H]
  [MeasurableSpace N] [MeasurableSpace M] [MeasurableSpace H]
  [BorelSpace N] [BorelSpace M] [BorelSpace H]

omit [IsTopologicalGroup N] [IsTopologicalGroup M] [LocallyCompactSpace N]
  [LocallyCompactSpace M] [LocallyCompactSpace H] [SecondCountableTopology N]
  [SecondCountableTopology H] in
include hpi in
theorem measurableSet_prodTransversal (hi : IsEmbedding i) (hj : Continuous j)
    (hp : Continuous p) {tN : Set N} {tM : Set M} (htN : MeasurableSet tN)
    (htM : MeasurableSet tM) : MeasurableSet (prodTransversal i j p hpj hker tN tM) := by
  rw [prodTransversal_eq_preimage i j p hpj hker hpi hi hj hp]
  exact (prodHomeomorph i j p hpj hker hpi hi hj hp).symm.continuous.measurable (htN.prod htM)

omit [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] in
include hpi in
/-- **Triviality of the conjugation modulus.** If a discrete subgroup `ΓM ≤ M` of finite
covolume is carried into a discrete `Γ ≤ H`, and one compact set of `N` meets every orbit of
`i⁻¹(Γ)`, then conjugation by every element of `M` preserves Haar measure on `N`. -/
theorem mulEquivHaarChar_conj_eq_one (hi : IsEmbedding i) (hj : Continuous j)
    (Γ : Subgroup H) (hΓ : IsDiscrete (Γ : Set H))
    {K : Set N} (hK : IsCompact K) (hKcover : ∀ n, ∃ γ, i γ ∈ Γ ∧ γ * n ∈ K)
    (ΓM : Subgroup M) (hΓM : IsDiscrete (ΓM : Set M)) (hjΓM : ∀ γ ∈ ΓM, j γ ∈ Γ)
    [IsFiniteMeasure (haarQuotientMeasure ΓM hΓM)] (m : M) :
    mulEquivHaarChar (conj i j p hpj hker hpi hi hj m) = 1 :=
  eq_one_of_measurable_of_isFiniteMeasure ΓM hΓM _
    (measurable_mulEquivHaarChar_conj hpj hker hpi hi hj)
    (mulEquivHaarChar_conj_mul hpj hker hpi hi hj)
    (fun _ => (mulEquivHaarChar_pos _).ne')
    (fun γ hγ => mulEquivHaarChar_conj_eq_one_of_mem hpj hker hpi hi hj Γ hΓ hK hKcover
      (hjΓM γ hγ)) m

include hpi in
/-- **Haar measure of a semidirect product.** Suppose conjugation by `M` preserves Haar measure
on `N`, and let `Λ ≤ H` be countable with `j (p λ) ∈ Λ` for `λ ∈ Λ`. If the scalings `a • haar`,
`b • haar`, `d • haar` give mass one to measurable transversals of `Λ`, `i⁻¹(Λ)` and `j⁻¹(Λ)`
respectively, then `a • haar` on `H` is the image of the product of `b • haar` and `d • haar`
under `(n, m) ↦ i n * j m`. -/
theorem smul_haar_eq_map_prod (hi : IsEmbedding i) (hj : Continuous j) (hp : Continuous p)
    (hδ : ∀ m, mulEquivHaarChar (conj i j p hpj hker hpi hi hj m) = 1)
    (Λ : Subgroup H) [Countable Λ] (hΛp : ∀ x ∈ Λ, j (p x) ∈ Λ)
    {D : Set H} (hD : MeasurableSet D) (hDu : ∀ h : H, ∃! γ : Λ, (γ : H) * h ∈ D)
    {tN : Set N} (htNm : MeasurableSet tN) (htN : ∀ n, ∃! γ : Λ.comap i, (γ : N) * n ∈ tN)
    {tM : Set M} (htMm : MeasurableSet tM) (htM : ∀ m, ∃! γ : Λ.comap j, (γ : M) * m ∈ tM)
    (a b d : ℝ≥0∞) (ha : a * (Measure.haar : Measure H) D = 1)
    (hb : b * (Measure.haar : Measure N) tN = 1) (hd : d * (Measure.haar : Measure M) tM = 1) :
    a • (Measure.haar : Measure H) =
      Measure.map (prodHomeomorph i j p hpj hker hpi hi hj hp)
        ((b • (Measure.haar : Measure N)).prod (d • (Measure.haar : Measure M))) := by
  obtain ⟨c, hc⟩ := exists_haar_eq_smul_map_prod hpj hker hpi hi hj hp hδ
  set Φ := prodHomeomorph i j p hpj hker hpi hi hj hp
  set T := prodTransversal i j p hpj hker tN tM
  have hTm : MeasurableSet T := measurableSet_prodTransversal i j p hpj hker hpi hi hj hp htNm htMm
  have hTu := prodTransversal_unique i j p hpj hker hpi hi.injective Λ hΛp htN htM
  have hfdD : IsFundamentalDomain Λ D (Measure.haar : Measure H) :=
    IsFundamentalDomain.mk' hD.nullMeasurableSet hDu
  have hfdT : IsFundamentalDomain Λ T (Measure.haar : Measure H) :=
    IsFundamentalDomain.mk' hTm.nullMeasurableSet hTu
  have hTD : (Measure.haar : Measure H) T = (Measure.haar : Measure H) D := hfdT.measure_eq hfdD
  have hTval : (Measure.haar : Measure H) T =
      (c : ℝ≥0∞) * ((Measure.haar : Measure N) tN * (Measure.haar : Measure M) tM) := by
    have hpre : Φ.toMeasurableEquiv ⁻¹' T = tN ×ˢ tM := by
      ext ⟨n, m⟩
      exact mul_mem_prodTransversal_iff i j p hpj hker hpi hi.injective tN tM n m
    rw [hc, Measure.smul_apply,
      show Measure.map Φ ((Measure.haar : Measure N).prod (Measure.haar : Measure M)) =
        Measure.map Φ.toMeasurableEquiv _ from rfl, MeasurableEquiv.map_apply, hpre,
      Measure.prod_prod, ENNReal.smul_def, smul_eq_mul]
  have hb0 : b ≠ 0 := left_ne_zero_of_mul_eq_one hb
  have hd0 : d ≠ 0 := left_ne_zero_of_mul_eq_one hd
  have hbt : b ≠ ∞ := fun h => by simp [h, right_ne_zero_of_mul_eq_one hb] at hb
  have hdt : d ≠ ∞ := fun h => by simp [h, right_ne_zero_of_mul_eq_one hd] at hd
  have hN0 : (Measure.haar : Measure N) tN ≠ 0 := right_ne_zero_of_mul_eq_one hb
  have hM0 : (Measure.haar : Measure M) tM ≠ 0 := right_ne_zero_of_mul_eq_one hd
  have hNt : (Measure.haar : Measure N) tN ≠ ∞ := fun h => by simp [h, hb0] at hb
  have hMt : (Measure.haar : Measure M) tM ≠ ∞ := fun h => by simp [h, hd0] at hd
  -- `a * c = b * d`
  have hkey : a * c = b * d := by
    have h1 : a * (c * ((Measure.haar : Measure N) tN * (Measure.haar : Measure M) tM)) =
        (b * (Measure.haar : Measure N) tN) * (d * (Measure.haar : Measure M) tM) := by
      rw [← hTval, hTD, ha, hb, hd, one_mul]
    have hprod0 : (Measure.haar : Measure N) tN * (Measure.haar : Measure M) tM ≠ 0 :=
      mul_ne_zero hN0 hM0
    have hprodt : (Measure.haar : Measure N) tN * (Measure.haar : Measure M) tM ≠ ∞ :=
      ENNReal.mul_ne_top hNt hMt
    have h2 : (a * c) * ((Measure.haar : Measure N) tN * (Measure.haar : Measure M) tM) =
        (b * d) * ((Measure.haar : Measure N) tN * (Measure.haar : Measure M) tM) := by
      calc (a * c) * ((Measure.haar : Measure N) tN * (Measure.haar : Measure M) tM)
          = a * (c * ((Measure.haar : Measure N) tN * (Measure.haar : Measure M) tM)) := by
            ring
        _ = (b * (Measure.haar : Measure N) tN) * (d * (Measure.haar : Measure M) tM) := h1
        _ = (b * d) * ((Measure.haar : Measure N) tN * (Measure.haar : Measure M) tM) := by
            ring
    exact (ENNReal.mul_left_inj hprod0 hprodt).mp h2
  rw [hc, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul,
    ENNReal.smul_def, smul_smul, hkey]
  exact Φ.continuous.measurable.aemeasurable

omit [IsTopologicalGroup N] [IsTopologicalGroup M] [LocallyCompactSpace N]
  [LocallyCompactSpace M] [LocallyCompactSpace H] [SecondCountableTopology N]
  [SecondCountableTopology H] in
include hpi in
/-- **Integrals over a product transversal.** If the left invariant measure `μH` is the image of
`μN.prod μM` (with `μN`, `μM` s-finite) under `(n, m) ↦ i n * j m`, then for a countable `Λ'` with
`j (p λ) ∈ Λ'` for `λ ∈ Λ'`, the integral of a left `Λ'`-invariant function over any measurable
transversal of `Λ'` is its integral over the product of measurable transversals of `i⁻¹(Λ')` and
`j⁻¹(Λ')`. -/
theorem setIntegral_transversal_eq_prod (hi : IsEmbedding i) (hj : Continuous j)
    (hp : Continuous p) (μN : Measure N) (μM : Measure M) (μH : Measure H)
    [SFinite μN] [SFinite μM] [μH.IsMulLeftInvariant]
    (hμ : μH = Measure.map (prodHomeomorph i j p hpj hker hpi hi hj hp) (μN.prod μM))
    (Λ : Subgroup H) [Countable Λ] (hΛp : ∀ x ∈ Λ, j (p x) ∈ Λ)
    {D : Set H} (hD : MeasurableSet D) (hDu : ∀ h : H, ∃! γ : Λ, (γ : H) * h ∈ D)
    {tN : Set N} (htNm : MeasurableSet tN) (htN : ∀ n, ∃! γ : Λ.comap i, (γ : N) * n ∈ tN)
    {tM : Set M} (htMm : MeasurableSet tM) (htM : ∀ m, ∃! γ : Λ.comap j, (γ : M) * m ∈ tM)
    {E : Type x} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : H → E) (hf : ∀ γ ∈ Λ, ∀ h, f (γ * h) = f h) :
    ∫ h in D, f h ∂μH = ∫ z in tN ×ˢ tM, f (i z.1 * j z.2) ∂(μN.prod μM) := by
  set Φ := prodHomeomorph i j p hpj hker hpi hi hj hp
  have hTm : MeasurableSet (prodTransversal i j p hpj hker tN tM) :=
    measurableSet_prodTransversal i j p hpj hker hpi hi hj hp htNm htMm
  have hfdD : IsFundamentalDomain Λ D μH := IsFundamentalDomain.mk' hD.nullMeasurableSet hDu
  have hfdT : IsFundamentalDomain Λ (prodTransversal i j p hpj hker tN tM) μH :=
    IsFundamentalDomain.mk' hTm.nullMeasurableSet
      (prodTransversal_unique i j p hpj hker hpi hi.injective Λ hΛp htN htM)
  rw [hfdD.setIntegral_eq hfdT (fun γ h => hf _ γ.property h),
    prodTransversal_eq_preimage i j p hpj hker hpi hi hj hp, hμ,
    show Measure.map Φ (μN.prod μM) = Measure.map Φ.toMeasurableEquiv (μN.prod μM) from rfl]
  rw [show Φ.symm ⁻¹' (tN ×ˢ tM) = Φ.toMeasurableEquiv.symm ⁻¹' (tN ×ˢ tM) from rfl,
    ← MeasurableEquiv.image_eq_preimage_symm, setIntegral_map_equiv,
    MeasurableEquiv.preimage_image]
  rfl

omit [IsTopologicalGroup N] [IsTopologicalGroup M] [LocallyCompactSpace N]
  [LocallyCompactSpace M] [LocallyCompactSpace H] [SecondCountableTopology N]
  [SecondCountableTopology H] in
include hpi in
/-- The nonnegative form of `setIntegral_transversal_eq_prod`. -/
theorem setLIntegral_transversal_eq_prod (hi : IsEmbedding i) (hj : Continuous j)
    (hp : Continuous p) (μN : Measure N) (μM : Measure M) (μH : Measure H)
    [SFinite μN] [SFinite μM] [μH.IsMulLeftInvariant]
    (hμ : μH = Measure.map (prodHomeomorph i j p hpj hker hpi hi hj hp) (μN.prod μM))
    (Λ : Subgroup H) [Countable Λ] (hΛp : ∀ x ∈ Λ, j (p x) ∈ Λ)
    {D : Set H} (hD : MeasurableSet D) (hDu : ∀ h : H, ∃! γ : Λ, (γ : H) * h ∈ D)
    {tN : Set N} (htNm : MeasurableSet tN) (htN : ∀ n, ∃! γ : Λ.comap i, (γ : N) * n ∈ tN)
    {tM : Set M} (htMm : MeasurableSet tM) (htM : ∀ m, ∃! γ : Λ.comap j, (γ : M) * m ∈ tM)
    (f : H → ℝ≥0∞) (hf : ∀ γ ∈ Λ, ∀ h, f (γ * h) = f h) :
    ∫⁻ h in D, f h ∂μH = ∫⁻ z in tN ×ˢ tM, f (i z.1 * j z.2) ∂(μN.prod μM) := by
  set Φ := prodHomeomorph i j p hpj hker hpi hi hj hp
  have hTm : MeasurableSet (prodTransversal i j p hpj hker tN tM) :=
    measurableSet_prodTransversal i j p hpj hker hpi hi hj hp htNm htMm
  have hfdD : IsFundamentalDomain Λ D μH := IsFundamentalDomain.mk' hD.nullMeasurableSet hDu
  have hfdT : IsFundamentalDomain Λ (prodTransversal i j p hpj hker tN tM) μH :=
    IsFundamentalDomain.mk' hTm.nullMeasurableSet
      (prodTransversal_unique i j p hpj hker hpi hi.injective Λ hΛp htN htM)
  rw [hfdD.setLIntegral_eq hfdT _ (fun γ h => hf _ γ.property h),
    prodTransversal_eq_preimage i j p hpj hker hpi hi hj hp, hμ,
    show Measure.map Φ (μN.prod μM) = Measure.map Φ.toMeasurableEquiv (μN.prod μM) from rfl]
  rw [show Φ.symm ⁻¹' (tN ×ˢ tM) = Φ.toMeasurableEquiv.symm ⁻¹' (tN ×ˢ tM) from rfl,
    ← MeasurableEquiv.image_eq_preimage_symm, MeasurableEquiv.restrict_map,
    MeasurableEquiv.preimage_image, lintegral_map_equiv]
  rfl

omit [IsTopologicalGroup N] [IsTopologicalGroup M] [LocallyCompactSpace N]
  [LocallyCompactSpace M] [LocallyCompactSpace H] [SecondCountableTopology N]
  [SecondCountableTopology H] in
include hpi in
/-- For a function also invariant under left translation by `i(N)`, the integral over a
transversal of `Λ` is the mass of `tN` times the integral of its restriction to `j(M)` over `tM`. -/
theorem setIntegral_transversal_eq_of_invariant (hi : IsEmbedding i) (hj : Continuous j)
    (hp : Continuous p) (μN : Measure N) (μM : Measure M) (μH : Measure H)
    [SFinite μN] [SFinite μM] [μH.IsMulLeftInvariant]
    (hμ : μH = Measure.map (prodHomeomorph i j p hpj hker hpi hi hj hp) (μN.prod μM))
    (Λ : Subgroup H) [Countable Λ] (hΛp : ∀ x ∈ Λ, j (p x) ∈ Λ)
    {D : Set H} (hD : MeasurableSet D) (hDu : ∀ h : H, ∃! γ : Λ, (γ : H) * h ∈ D)
    {tN : Set N} (htNm : MeasurableSet tN) (htN : ∀ n, ∃! γ : Λ.comap i, (γ : N) * n ∈ tN)
    {tM : Set M} (htMm : MeasurableSet tM) (htM : ∀ m, ∃! γ : Λ.comap j, (γ : M) * m ∈ tM)
    {E : Type x} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : H → E) (hf : ∀ γ ∈ Λ, ∀ h, f (γ * h) = f h) (hfN : ∀ n h, f (i n * h) = f h) :
    ∫ h in D, f h ∂μH = (μN tN).toReal • ∫ m in tM, f (j m) ∂μM := by
  rw [setIntegral_transversal_eq_prod i j p hpj hker hpi hi hj hp μN μM μH hμ Λ hΛp hD hDu
    htNm htN htMm htM f hf, ← Measure.prod_restrict]
  simp_rw [hfN]
  rw [integral_fun_snd (fun m => f (j m)), Measure.real, Measure.restrict_apply_univ]

end Langlands.Global.LeftCosetSpace.Semidirect

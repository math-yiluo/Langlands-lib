import Langlands.Global.AdelicBoundedWavePacketStatement
import Langlands.Global.AdelicLocalWavePacketStatement
import Langlands.Global.BoundedWavePacketApproximation

/-! # Lapid's Lemma 10 from its smooth case

Lapid 2011, Lemma 10 (p.329), `BoundedWavePacketStatement`, from Proposition 2 and the bound
(19) for smooth wave packets (`LocalWavePacketInnerProductStatement`,
`LocalWavePacketNormBoundStatement`), the sesquilinearity of `(·,·)_P` on `A^2_P`, and the
existence of Levi projections and Iwasawa-compatible measures, following Lapid's proof:
approximation by smooth packets, an `L²`-Cauchy argument and passage to the limit. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct Filter Topology Set
open scoped CategoryTheory.MonObj TensorProduct ENNReal ContDiff

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic BoundedWavePacket

namespace BoundedWavePacket

/-! ### Domains of holomorphy in coordinates -/

/-- If `f` is meromorphic in coordinates with domain `D`, then for a real-linear map
`L : ℝⁿ → V` the set `{x | L x ∈ D}` is open and `f ∘ L` is continuous on it. -/
theorem isOpen_and_continuousOn_of_isMeromorphicInCoordinatesOn {V : Type*} [AddCommGroup V]
    [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V] {n : ℕ} (L : (Fin n → ℝ) →ₗ[ℝ] V)
    {f : V → ℂ} {D : Set V} (hf : IsMeromorphicInCoordinatesOn f D) :
    IsOpen {x | L x ∈ D} ∧ ContinuousOn (fun x => f (L x)) {x | L x ∈ D} := by
  obtain ⟨hfin, hmer⟩ := hf
  let ec : (Fin (Module.finrank ℂ V) → ℂ) ≃ₗ[ℂ] V := (Module.finBasis ℂ V).equivFun.symm
  obtain ⟨hopen, -, hhol, -⟩ := hmer _ ec
  let φ : (Fin n → ℝ) →ₗ[ℝ] (Fin (Module.finrank ℂ V) → ℂ) :=
    (ec.symm.toLinearMap.restrictScalars ℝ).comp L
  have hφ : Continuous φ := LinearMap.continuous_of_finiteDimensional φ
  have hpre : {x | L x ∈ D} = φ ⁻¹' (ec ⁻¹' D) := by
    ext x
    simp [φ]
  have hcont : ContinuousOn (f ∘ ec) (ec ⁻¹' D) := by
    have := (hhol (ContinuousLinearMap.id ℂ ℂ)).continuousOn
    simp only [ContinuousLinearMap.coe_id', id] at this
    exact this
  refine ⟨hpre ▸ hopen.preimage hφ, ?_⟩
  have e : (fun x => f (L x)) = (f ∘ ec) ∘ φ := by
    funext x
    simp [φ]
  rw [e, hpre]
  exact hcont.comp hφ.continuousOn fun x hx => hx

/-- A common domain for a family of meromorphic functions whose preimage under `L` is open:
the given domain if the family is nonempty, and everything otherwise. -/
theorem exists_open_domain {V : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
    [IsScalarTower ℝ ℂ V] {n : ℕ} (L : (Fin n → ℝ) →ₗ[ℝ] V) {κ : Type*} {f : κ → V → ℂ}
    {D : Set V} (hf : ∀ i, IsMeromorphicInCoordinatesOn (f i) D) :
    ∃ D' : Set V, D ⊆ D' ∧ IsOpen {x | L x ∈ D'} ∧
      (∀ i, IsMeromorphicInCoordinatesOn (f i) D') ∧
      ∀ i, ContinuousOn (fun x => f i (L x)) {x | L x ∈ D'} := by
  by_cases h : Nonempty κ
  · obtain ⟨i₀⟩ := h
    exact ⟨D, subset_rfl, (isOpen_and_continuousOn_of_isMeromorphicInCoordinatesOn L (hf i₀)).1,
      hf, fun i => (isOpen_and_continuousOn_of_isMeromorphicInCoordinatesOn L (hf i)).2⟩
  · rw [not_nonempty_iff] at h
    exact ⟨univ, subset_univ _, by simp, fun i => isEmptyElim i, fun i => isEmptyElim i⟩

theorem spectralMeasure_lt_top {n : ℕ} {N : Set (Fin n → ℝ)} (hN : IsCompact N) :
    spectralMeasure n N < ⊤ := by
  unfold spectralMeasure
  rw [Measure.smul_apply, smul_eq_mul]
  refine ENNReal.mul_lt_top ?_ hN.measure_lt_top
  refine ENNReal.pow_lt_top ?_
  rw [ENNReal.inv_lt_top]
  exact ENNReal.ofReal_pos.2 Real.two_pi_pos

/-- Approximation data for the coefficients of a bounded wave packet: smooth coefficients
vanishing outside the compact set `N`, uniformly bounded, converging `ν`-almost everywhere. -/
theorem exists_coefficient_approximation {n k : ℕ} (ν : Measure (Fin n → ℝ)) [IsFiniteMeasure ν]
    {S N : Set (Fin n → ℝ)} (hS : IsCompact S) (hSN : S ⊆ interior N)
    {c : Fin k → (Fin n → ℝ) → ℂ}
    (hc : ∀ j, Measurable (c j) ∧ (∃ C : ℝ, ∀ x, ‖c j x‖ ≤ C) ∧ ∀ x ∉ S, c j x = 0) :
    ∃ (A : ℝ) (cs : ℕ → Fin k → (Fin n → ℝ) → ℂ), 0 ≤ A ∧ (∀ j x, ‖c j x‖ ≤ A) ∧
      (∀ m j, ContDiff ℝ ∞ (cs m j)) ∧ (∀ m j x, x ∉ N → cs m j x = 0) ∧
      (∀ m j x, ‖cs m j x‖ ≤ A) ∧
      ∀ᵐ x ∂ν, ∀ j, Tendsto (fun m => cs m j x) atTop (𝓝 (c j x)) := by
  have hcb : ∀ j, ∃ C : ℝ, ∀ x, ‖c j x‖ ≤ C := fun j => (hc j).2.1
  choose Cj hCj using hcb
  set C : ℝ := ∑ j, max (Cj j) 0 with hCdef
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => le_max_right _ _
  have hCc : ∀ j x, ‖c j x‖ ≤ C := fun j x =>
    (hCj j x).trans ((le_max_left _ _).trans
      (Finset.single_le_sum (f := fun j => max (Cj j) 0) (fun j _ => le_max_right _ _)
        (Finset.mem_univ j)))
  have happrox := fun j => exists_seq_smooth_tendsto_ae ν hS hSN (hc j).1 (hCc j) (hc j).2.2
  choose cs hcs hcsN hcsA hcsl using happrox
  refine ⟨2 * C + 1, fun m j => cs j m, by linarith, fun j x => by linarith [hCc j x],
    fun m j => hcs j m, fun m j => hcsN j m, fun m j => hcsA j m, ?_⟩
  exact ae_all_iff.2 hcsl

/-- Almost-everywhere convergence on `N` extends to all of `ℝⁿ` when the functions vanish
outside `N`. -/
theorem ae_tendsto_of_restrict {n k : ℕ} {σ : Measure (Fin n → ℝ)} {S N : Set (Fin n → ℝ)}
    (hN : MeasurableSet N) (hSN : S ⊆ N) {c : Fin k → (Fin n → ℝ) → ℂ}
    (hcS : ∀ j x, x ∉ S → c j x = 0) {cs : ℕ → Fin k → (Fin n → ℝ) → ℂ}
    (hcsN : ∀ m j x, x ∉ N → cs m j x = 0)
    (h : ∀ᵐ x ∂σ.restrict N, ∀ j, Tendsto (fun m => cs m j x) atTop (𝓝 (c j x))) :
    ∀ᵐ x ∂σ, ∀ j, Tendsto (fun m => cs m j x) atTop (𝓝 (c j x)) := by
  rw [ae_restrict_iff' hN] at h
  filter_upwards [h] with x hx
  by_cases hxN : x ∈ N
  · exact hx hxN
  · intro j
    have hxS : x ∉ S := fun h => hxN (hSN h)
    simp only [hcsN _ j x hxN, hcS j x hxS]
    exact tendsto_const_nhds

end BoundedWavePacket

/-! ### The norm bound -/

/-- Lapid 2011, Lemma 10, bound (19), from the bound for smooth wave packets and the
sesquilinearity of `(·,·)_P`. -/
theorem boundedWavePacketNormBound_of_local (hB : LocalWavePacketNormBoundStatement)
    (hD : InducedInnerProductSesquilinearStatement) : BoundedWavePacketNormBoundStatement := by
  intro F _ _ G P M U A _ _ _ _ _ _ _ p _ iU l _ a r _ _ _ hA hT π hG hU hlπ K hK Nr dr rho
    hsmooth hcalc hKmax hrho μM _ hμM n e β hβc hβs hβ1 k v c S E D hv hS hc hSD hE hEis Θ φ μG
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  set σ := spectralMeasure n with hσ
  set L : (Fin n → ℝ) →ₗ[ℝ] ComplexCharacterParameter F P :=
    (imaginaryParameter F P).comp e.toLinearMap with hL
  obtain ⟨D', hDD', hD'open, hE', hEc⟩ := exists_open_domain L
    (κ := Fin k × AdelicGroupPoints F G) (f := fun i lam => E i.1 lam i.2)
    (fun i => hE i.1 i.2)
  have hSO : S ⊆ {x | L x ∈ D'} := fun x hx => hDD' (hSD ⟨x, hx, rfl⟩)
  obtain ⟨Nc, hNc, hSN, hNO⟩ := exists_compact_between hS hD'open hSO
  have hNm : MeasurableSet Nc := hNc.isClosed.measurableSet
  have hσN : σ Nc < ⊤ := spectralMeasure_lt_top hNc
  have : IsFiniteMeasure (σ.restrict Nc) := isFiniteMeasure_restrict.2 hσN.ne
  obtain ⟨Ab, cs, hA0, -, hcs, hcsN, hcsA, hcsl⟩ :=
    exists_coefficient_approximation (σ.restrict Nc) hS hSN hc
  have hlim := ae_tendsto_of_restrict hNm (hSN.trans interior_subset) (fun j x hx => (hc j).2.2 x hx)
    hcsN hcsl
  set Gm : Fin k → Fin k → ℂ := fun j j' =>
    inducedInnerProduct K hK.isCompact p l μM e β (v j) (v j') with hGm
  have hgramEq : ∀ z : Fin k → ℂ,
      inducedInnerProduct K hK.isCompact p l μM e β (fun g => ∑ j, z j * v j g)
        (fun g => ∑ j, z j * v j g) = gramForm Gm z := fun z =>
    hD F G P M U A p iU l a r hA hT π hG hU hlπ K hK rho hsmooth hcalc hKmax hrho μM hμM e β hβc
      hβs hβ1 k v hv z z
  have hND' : (fun x => imaginaryParameter F P (e x)) '' Nc ⊆ D' := by
    rintro _ ⟨x, hx, rfl⟩
    exact hNO hx
  have hE'' : ∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E j lam g) D' := fun j g =>
    hE' (j, g)
  set Φ : Fin k → (Fin n → ℝ) → AdelicGroupPoints F G → ℂ := fun j x g =>
    E j (imaginaryParameter F P (e x)) g with hΦ
  have hΦN : ∀ j g, ContinuousOn (fun x => Φ j x g) Nc := fun j g => (hEc (j, g)).mono hNO
  have hBapp : ∀ d' : Fin k → (Fin n → ℝ) → ℂ, (∀ j, ContDiff ℝ ∞ (d' j)) →
      (∀ j x, x ∉ Nc → d' j x = 0) →
      (weylParameterSet p l p l π).Finite ∧
      MemLp (fun y : RationalQuotient F G => packet σ d' Φ y.out) 2 μG ∧
      ∫ y, ‖packet σ d' Φ y.out‖ ^ 2 ∂μG ≤
        (Nat.card (weylParameterSet p l p l π) : ℝ) *
          ∫ x, (gramForm Gm fun j => d' j x).re ∂σ := by
    intro d' hd' hd'N
    have h := hB F G P M U A p iU l a r hA hT π hG hU hlπ K hK rho hsmooth hcalc hKmax hrho μM
      hμM e β hβc hβs hβ1 k v d' Nc E D' hv hNc (fun j => ⟨hd' j, fun x hx => hd'N j x hx⟩)
      hND' hE'' hEis
    dsimp only at h
    simp only [hgramEq] at h
    exact h
  have HB := fun d' hd' hd'N => (hBapp d' hd' hd'N).2
  obtain ⟨hmem, -, hbound⟩ := packet_core (μY := μG) (fun y : RationalQuotient F G => y.out)
    hNc hσN hΦN hA0 hcs hcsA hcsN hlim Gm _ HB
  have hfin := (hBapp (fun _ _ => 0) (fun _ => contDiff_const) (fun _ _ _ => rfl)).1
  refine ⟨hfin, hmem, ?_⟩
  have key : ∫ x, (inducedInnerProduct K hK.isCompact p l μM e β (φ x) (φ x)).re ∂σ =
      ∫ x, (gramForm Gm fun j => c j x).re ∂σ :=
    integral_congr_ae (ae_of_all _ fun x => by
      show (inducedInnerProduct K hK.isCompact p l μM e β (fun g => ∑ j, c j x * v j g)
        (fun g => ∑ j, c j x * v j g)).re = (gramForm Gm fun j => c j x).re
      rw [hgramEq])
  rw [key]
  exact hbound

/-! ### The inner product formula -/

namespace BoundedWavePacket

/-- A normalized smooth bump on `ℝⁿ`: a continuous compactly supported weight of integral `1`. -/
theorem exists_weight (n : ℕ) :
    ∃ β : (Fin n → ℝ) → ℝ, Continuous β ∧ HasCompactSupport β ∧ ∫ y, β y = 1 := by
  let b : ContDiffBump (0 : Fin n → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  exact ⟨b.normed volume, b.continuous_normed, b.hasCompactSupport_normed, b.integral_normed⟩

end BoundedWavePacket

/-- Lapid 2011, Lemma 10, inner product formula, from Proposition 2 and the bound (19) for
smooth wave packets, the sesquilinearity of `(·,·)_P`, and the existence of a Levi projection
and an Iwasawa-compatible measure for `P`. -/
theorem boundedWavePacketInnerProduct_of_local (hA1 : LocalWavePacketInnerProductStatement)
    (hB : LocalWavePacketNormBoundStatement) (hD : InducedInnerProductSesquilinearStatement)
    (hC1 : LeviProjectionExistenceStatement) (hC2 : WavePacketIwasawaCompatibleMeasureExistenceStatement) :
    BoundedWavePacketInnerProductStatement := by
  intro F _ _ G P M U P' M' U' A A' _ _ _ _ _ _ _ _ _ _ _ p _ iU l _ a r _ _ _ hA hT p' _ iU' l' _
    a' r' _ _ _ hA' hT' π' hG hU hU' hlπ' K hK hK' Nr dr rho hsmooth hcalc hKmax hrho μM' _ hμM'
    n n' e e' β' hβc' hβs' hβ1' k v c S E D hv hS hc hSD hE hEis k' v' c' S' E' D' hv' hS' hc'
    hSD' hE' hEis' T _ w cw hw hinj hsurj mi ψ coeff DM hψ hSDM hcoeff hexp Θ Θ' μG
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  have : LocallyOfFiniteType P'.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p') ‹IsClosedImmersion p'.hom.hom.left›
  -- Levi data for `P`
  obtain ⟨π, hlπ⟩ := hC1 F G P M U A p iU l a r hA hT hG hU
  obtain ⟨μM, hμMh, hμM⟩ := hC2 F G P M U A p iU l a r hA hT hG hU K hK hKmax
  obtain ⟨β, hβc, hβs, hβ1⟩ := exists_weight n
  set σ := spectralMeasure n with hσ
  set σ' := spectralMeasure n' with hσ'
  -- domains
  set L : (Fin n → ℝ) →ₗ[ℝ] ComplexCharacterParameter F P :=
    (imaginaryParameter F P).comp e.toLinearMap with hL
  set L' : (Fin n' → ℝ) →ₗ[ℝ] ComplexCharacterParameter F P' :=
    (imaginaryParameter F P').comp e'.toLinearMap with hL'
  obtain ⟨D₁, hDD₁, hD₁open, hE₁, hEc⟩ := exists_open_domain L
    (κ := Fin k × AdelicGroupPoints F G) (f := fun i lam => E i.1 lam i.2)
    (fun i => hE i.1 i.2)
  obtain ⟨DM₁, hDMDM₁, hDM₁open, hcoeff₁, hcoeffc⟩ := exists_open_domain L
    (κ := T × Fin k × Fin mi) (f := fun i => coeff i.1 i.2.1 i.2.2)
    (fun i => hcoeff i.1 i.2.1 i.2.2)
  obtain ⟨D₁', hDD₁', hD₁'open, hE₁', hEc'⟩ := exists_open_domain L'
    (κ := Fin k' × AdelicGroupPoints F G) (f := fun i lam => E' i.1 lam i.2)
    (fun i => hE' i.1 i.2)
  have hSO : S ⊆ {x | L x ∈ D₁} ∩ {x | L x ∈ DM₁} := fun x hx =>
    ⟨hDD₁ (hSD ⟨x, hx, rfl⟩), hDMDM₁ (hSDM ⟨x, hx, rfl⟩)⟩
  obtain ⟨Nc, hNc, hSN, hNO⟩ := exists_compact_between hS (hD₁open.inter hDM₁open) hSO
  have hSO' : S' ⊆ {x | L' x ∈ D₁'} := fun x hx => hDD₁' (hSD' ⟨x, hx, rfl⟩)
  obtain ⟨Nc', hNc', hSN', hNO'⟩ := exists_compact_between hS' hD₁'open hSO'
  have hNm : MeasurableSet Nc := hNc.isClosed.measurableSet
  have hNm' : MeasurableSet Nc' := hNc'.isClosed.measurableSet
  have hσN : σ Nc < ⊤ := spectralMeasure_lt_top hNc
  have hσN' : σ' Nc' < ⊤ := spectralMeasure_lt_top hNc'
  have : IsFiniteMeasure (σ.restrict Nc) := isFiniteMeasure_restrict.2 hσN.ne
  have : IsFiniteMeasure (σ'.restrict Nc') := isFiniteMeasure_restrict.2 hσN'.ne
  -- the Weyl maps in coordinates
  set Lt : T → (Fin n → ℝ) →ₗ[ℝ] (Fin n' → ℝ) := fun t =>
    e'.symm.toLinearMap.comp ((realWeylParameter l (cw t) π').comp e.toLinearMap) with hLt
  have hLtc : ∀ t, Continuous (Lt t) := fun t => LinearMap.continuous_of_finiteDimensional _
  set ν' : Measure (Fin n' → ℝ) :=
    σ'.restrict Nc' + ∑ t, (σ.restrict Nc).map (Lt t) with hν'
  have : IsFiniteMeasure ν' := by
    refine ⟨?_⟩
    rw [hν', Measure.add_apply, Measure.finsetSum_apply]
    refine ENNReal.add_lt_top.2 ⟨measure_lt_top _ _, ENNReal.sum_lt_top.2 fun t _ => ?_⟩
    exact measure_lt_top _ _
  have hν'1 : σ'.restrict Nc' ≤ ν' := Measure.le_add_right le_rfl
  have hν'2 : ∀ t, (σ.restrict Nc).map (Lt t) ≤ ν' := by
    intro t
    refine Measure.le_iff'.2 fun s => ?_
    rw [hν', Measure.add_apply, Measure.finsetSum_apply]
    exact le_add_left (Finset.single_le_sum (f := fun t => (σ.restrict Nc).map (Lt t) s)
      (fun _ _ => zero_le) (Finset.mem_univ t))
  -- approximations
  obtain ⟨Ab, cs, hA0, -, hcs, hcsN, hcsA, hcsl⟩ :=
    exists_coefficient_approximation (σ.restrict Nc) hS hSN hc
  obtain ⟨Ab', cs', hA0', -, hcs', hcsN', hcsA', hcsl'⟩ :=
    exists_coefficient_approximation ν' hS' hSN' hc'
  have hlim := ae_tendsto_of_restrict hNm (hSN.trans interior_subset)
    (fun j x hx => (hc j).2.2 x hx) hcsN hcsl
  have hlim' := ae_tendsto_of_restrict hNm' (hSN'.trans interior_subset)
    (fun j x hx => (hc' j).2.2 x hx) hcsN' (ae_mono hν'1 hcsl')
  have hlimL : ∀ᵐ x ∂σ, x ∈ Nc → ∀ t j', Tendsto (fun m => cs' m j' (Lt t x)) atTop
      (𝓝 (c' j' (Lt t x))) := by
    have h : ∀ t, ∀ᵐ x ∂σ.restrict Nc, ∀ j', Tendsto (fun m => cs' m j' (Lt t x)) atTop
        (𝓝 (c' j' (Lt t x))) := fun t =>
      ae_of_ae_map (hLtc t).aemeasurable (ae_mono (hν'2 t) hcsl')
    have h2 := ae_all_iff.2 h
    rw [ae_restrict_iff' hNm] at h2
    filter_upwards [h2] with x hx hxN t j'
    exact hx hxN t j'
  -- the `P`-side packets
  set Gm : Fin k → Fin k → ℂ := fun j j' =>
    inducedInnerProduct K hK.isCompact p l μM e β (v j) (v j') with hGm
  have hgramEq : ∀ z : Fin k → ℂ,
      inducedInnerProduct K hK.isCompact p l μM e β (fun g => ∑ j, z j * v j g)
        (fun g => ∑ j, z j * v j g) = gramForm Gm z := fun z =>
    hD F G P M U A p iU l a r hA hT π hG hU hlπ K hK rho hsmooth hcalc hKmax hrho μM hμM e β hβc
      hβs hβ1 k v hv z z
  have hND₁ : (fun x => imaginaryParameter F P (e x)) '' Nc ⊆ D₁ := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hNO hx).1
  have hNDM₁ : (fun x => imaginaryParameter F P (e x)) '' Nc ⊆ DM₁ := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hNO hx).2
  have hEP : ∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E j lam g) D₁ := fun j g =>
    hE₁ (j, g)
  set Φ : Fin k → (Fin n → ℝ) → AdelicGroupPoints F G → ℂ := fun j x g =>
    E j (imaginaryParameter F P (e x)) g with hΦ
  have hΦN : ∀ j g, ContinuousOn (fun x => Φ j x g) Nc := fun j g =>
    (hEc (j, g)).mono fun x hx => (hNO hx).1
  have HB : ∀ d' : Fin k → (Fin n → ℝ) → ℂ, (∀ j, ContDiff ℝ ∞ (d' j)) →
      (∀ j x, x ∉ Nc → d' j x = 0) →
      MemLp (fun y : RationalQuotient F G => packet σ d' Φ y.out) 2 μG ∧
      ∫ y, ‖packet σ d' Φ y.out‖ ^ 2 ∂μG ≤
        (Nat.card (weylParameterSet p l p l π) : ℝ) *
          ∫ x, (gramForm Gm fun j => d' j x).re ∂σ := by
    intro d' hd' hd'N
    have h := hB F G P M U A p iU l a r hA hT π hG hU hlπ K hK rho hsmooth hcalc hKmax hrho μM
      hμM e β hβc hβs hβ1 k v d' Nc E D₁ hv hNc (fun j => ⟨hd' j, fun x hx => hd'N j x hx⟩)
      hND₁ hEP hEis
    dsimp only at h
    simp only [hgramEq] at h
    exact h.2
  obtain ⟨hmem, hT1, -⟩ := packet_core (μY := μG) (fun y : RationalQuotient F G => y.out)
    hNc hσN hΦN hA0 hcs hcsA hcsN hlim Gm _ HB
  -- the `P'`-side packets
  set Gm' : Fin k' → Fin k' → ℂ := fun j j' =>
    inducedInnerProduct K hK'.isCompact p' l' μM' e' β' (v' j) (v' j') with hGm'
  have hgramEq' : ∀ z : Fin k' → ℂ,
      inducedInnerProduct K hK'.isCompact p' l' μM' e' β' (fun g => ∑ j, z j * v' j g)
        (fun g => ∑ j, z j * v' j g) = gramForm Gm' z := fun z =>
    hD F G P' M' U' A' p' iU' l' a' r' hA' hT' π' hG hU' hlπ' K hK' rho hsmooth hcalc hKmax hrho
      μM' hμM' e' β' hβc' hβs' hβ1' k' v' hv' z z
  have hND₁' : (fun x => imaginaryParameter F P' (e' x)) '' Nc' ⊆ D₁' := by
    rintro _ ⟨x, hx, rfl⟩
    exact hNO' hx
  have hE₁'' : ∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E' j lam g) D₁' := fun j g =>
    hE₁' (j, g)
  set Φ' : Fin k' → (Fin n' → ℝ) → AdelicGroupPoints F G → ℂ := fun j x g =>
    E' j (imaginaryParameter F P' (e' x)) g with hΦ'
  have hΦN' : ∀ j g, ContinuousOn (fun x => Φ' j x g) Nc' := fun j g => (hEc' (j, g)).mono hNO'
  have HB' : ∀ d' : Fin k' → (Fin n' → ℝ) → ℂ, (∀ j, ContDiff ℝ ∞ (d' j)) →
      (∀ j x, x ∉ Nc' → d' j x = 0) →
      MemLp (fun y : RationalQuotient F G => packet σ' d' Φ' y.out) 2 μG ∧
      ∫ y, ‖packet σ' d' Φ' y.out‖ ^ 2 ∂μG ≤
        (Nat.card (weylParameterSet p' l' p' l' π') : ℝ) *
          ∫ x, (gramForm Gm' fun j => d' j x).re ∂σ' := by
    intro d' hd' hd'N
    have h := hB F G P' M' U' A' p' iU' l' a' r' hA' hT' π' hG hU' hlπ' K hK' rho hsmooth hcalc
      hKmax hrho μM' hμM' e' β' hβc' hβs' hβ1' k' v' d' Nc' E' D₁' hv' hNc'
      (fun j => ⟨hd' j, fun x hx => hd'N j x hx⟩) hND₁' hE₁'' hEis'
    dsimp only at h
    simp only [hgramEq'] at h
    exact h.2
  obtain ⟨hmem', hT1', -⟩ := packet_core (μY := μG) (fun y : RationalQuotient F G => y.out)
    hNc' hσN' hΦN' hA0' hcs' hcsA' hcsN' hlim' Gm' _ HB'
  refine ⟨hmem, hmem', ?_⟩
  -- Proposition 2 for the smooth packets
  set Gc : T → Fin k → Fin mi → Fin k' → ℂ := fun t j i j' =>
    inducedInnerProduct K hK'.isCompact p' l' μM' e' β' (ψ t j i) (v' j') with hGc
  have hcross : ∀ m, ∫ y, packet σ (cs m) Φ y.out * (starRingEnd ℂ) (packet σ' (cs' m) Φ' y.out)
      ∂μG = ∫ x, ∑ t, ∑ j, ∑ i, ∑ j', cs m j x * coeff t j i (imaginaryParameter F P (e x)) *
        (starRingEnd ℂ) (cs' m j' (e'.symm (realWeylParameter l (cw t) π' (e x)))) *
          Gc t j i j' ∂σ := by
    intro m
    have h := hA1 F G P M U P' M' U' A A' p iU l a r hA hT p' iU' l' a' r' hA' hT' π' hG hU hU'
      hlπ' K hK hK' rho hsmooth hcalc hKmax hrho μM' hμM' e e' β' hβc' hβs' hβ1' k v (cs m) Nc E
      D₁ hv hNc (fun j => ⟨hcs m j, fun x hx => hcsN m j x hx⟩) hND₁ hEP hEis k' v' (cs' m) Nc'
      E' D₁' hv' hNc' (fun j => ⟨hcs' m j, fun x hx => hcsN' m j x hx⟩) hND₁' hE₁'' hEis' T w cw
      hw hinj hsurj mi ψ coeff DM₁ hψ hNDM₁ (fun t j i => hcoeff₁ (t, j, i)) hexp
    dsimp only at h
    exact h.2.2
  have hLHS := tendsto_integral_mul_conj
    (f := fun m (y : RationalQuotient F G) => packet σ (cs m) Φ y.out)
    (f' := fun m (y : RationalQuotient F G) => packet σ' (cs' m) Φ' y.out)
    (fun m => (HB (cs m) (hcs m) (hcsN m)).1) (fun m => (HB' (cs' m) (hcs' m) (hcsN' m)).1)
    hmem hmem' hT1 hT1'
  -- the right side in the limit
  have hcoeffN : ∀ t j i, ContinuousOn (fun x => coeff t j i (imaginaryParameter F P (e x))) Nc :=
    fun t j i => (hcoeffc (t, j, i)).mono fun x hx => (hNO hx).2
  have hcb : ∀ t j i, ∃ C, ∀ x ∈ Nc, ‖coeff t j i (imaginaryParameter F P (e x))‖ ≤ C :=
    fun t j i => hNc.exists_bound_of_continuousOn (hcoeffN t j i)
  choose Cb hCb using hcb
  have hRHS : Tendsto (fun m => ∫ x, ∑ t, ∑ j, ∑ i, ∑ j', cs m j x *
      coeff t j i (imaginaryParameter F P (e x)) *
        (starRingEnd ℂ) (cs' m j' (e'.symm (realWeylParameter l (cw t) π' (e x)))) *
          Gc t j i j' ∂σ) atTop
      (𝓝 (∫ x, ∑ t, ∑ j, ∑ i, ∑ j', c j x * coeff t j i (imaginaryParameter F P (e x)) *
        (starRingEnd ℂ) (c' j' (e'.symm (realWeylParameter l (cw t) π' (e x)))) *
          Gc t j i j' ∂σ)) := by
    refine tendsto_integral_of_bdd_of_zero_off hNm hσN
      (B := ∑ t, ∑ j, ∑ i, ∑ j', Ab * max (Cb t j i) 0 * Ab' * ‖Gc t j i j'‖) ?_ ?_ ?_ ?_
    · intro m
      refine aestronglyMeasurable_of_restrict_of_zero_off hNm ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ hNm
        refine continuousOn_finsetSum _ fun t _ => continuousOn_finsetSum _ fun j _ =>
          continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j' _ => ?_
        refine ContinuousOn.mul (ContinuousOn.mul (ContinuousOn.mul
          (hcs m j).continuous.continuousOn (hcoeffN t j i)) ?_) continuousOn_const
        exact (Complex.continuous_conj.comp ((hcs' m j').continuous.comp
          (hLtc t))).continuousOn
      · intro x hx
        simp [hcsN m _ x hx]
    · intro m x
      by_cases hx : x ∈ Nc
      · refine norm_sum_le_of_le _ fun t _ => norm_sum_le_of_le _ fun j _ =>
          norm_sum_le_of_le _ fun i _ => norm_sum_le_of_le _ fun j' _ => ?_
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj]
        have h1 := hcsA m j x
        have h2 : ‖coeff t j i (imaginaryParameter F P (e x))‖ ≤ max (Cb t j i) 0 :=
          (hCb t j i x hx).trans (le_max_left _ _)
        have h3 := hcsA' m j' (e'.symm (realWeylParameter l (cw t) π' (e x)))
        gcongr
      · simp only [hcsN m _ x hx, zero_mul, Finset.sum_const_zero, norm_zero]
        refine Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun j _ =>
          Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j' _ => ?_
        have := le_max_right (Cb t j i) 0
        positivity
    · intro m x hx
      simp [hcsN m _ x hx]
    · filter_upwards [hlim, hlimL] with x hx hxL
      by_cases hxN : x ∈ Nc
      · refine tendsto_finsetSum _ fun t _ => tendsto_finsetSum _ fun j _ =>
          tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j' _ => ?_
        refine Tendsto.mul_const _ (Tendsto.mul ((hx j).mul_const _) ?_)
        exact (Complex.continuous_conj.tendsto _).comp (hxL hxN t j')
      · have hxS : x ∉ S := fun h => hxN (interior_subset (hSN h))
        simp only [hcsN _ _ x hxN, (hc _).2.2 x hxS, zero_mul, Finset.sum_const_zero]
        exact tendsto_const_nhds
  exact tendsto_nhds_unique hLHS (hRHS.congr fun m => (hcross m).symm)

/-- Lapid 2011, Lemma 10 (`BoundedWavePacketStatement`), from Proposition 2 and the bound (19)
for smooth wave packets, the sesquilinearity of `(·,·)_P`, and the existence of Levi
projections and Iwasawa-compatible measures. -/
theorem boundedWavePacket_of_local (hA1 : LocalWavePacketInnerProductStatement)
    (hB : LocalWavePacketNormBoundStatement) (hD : InducedInnerProductSesquilinearStatement)
    (hC1 : LeviProjectionExistenceStatement) (hC2 : WavePacketIwasawaCompatibleMeasureExistenceStatement) :
    BoundedWavePacketStatement :=
  ⟨boundedWavePacketInnerProduct_of_local hA1 hB hD hC1 hC2,
    boundedWavePacketNormBound_of_local hB hD⟩

/-- The premises `LocalWavePacketInnerProductStatement` (Lapid's Proposition 2 on `W_P`),
`LocalWavePacketNormBoundStatement` ((19) on `W_P`), `InducedInnerProductSesquilinearStatement`,
`LeviProjectionExistenceStatement` and `WavePacketIwasawaCompatibleMeasureExistenceStatement` imply Lapid
2011, Lemma 10 (`BoundedWavePacketStatement`). -/
def BoundedWavePacketLocalSufficiencyStatement : Prop :=
  LocalWavePacketInnerProductStatement → LocalWavePacketNormBoundStatement →
    InducedInnerProductSesquilinearStatement → LeviProjectionExistenceStatement →
    WavePacketIwasawaCompatibleMeasureExistenceStatement → BoundedWavePacketStatement

theorem boundedWavePacketLocalSufficiency : BoundedWavePacketLocalSufficiencyStatement :=
  boundedWavePacket_of_local

/-! ### The smooth premises are special cases of the target -/

namespace BoundedWavePacket

theorem measurable_bounded_of_contDiff {q : ℕ} {S : Set (Fin q → ℝ)} (hS : IsCompact S)
    {b : (Fin q → ℝ) → ℂ} (hb : ContDiff ℝ (⊤ : ℕ∞) b ∧ ∀ x ∉ S, b x = 0) :
    Measurable b ∧ (∃ C : ℝ, ∀ x, ‖b x‖ ≤ C) ∧ ∀ x ∉ S, b x = 0 := by
  refine ⟨hb.1.continuous.measurable, ?_, hb.2⟩
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hb.1.continuous.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : x ∈ S
  · exact (hC x hx).trans (le_max_left _ _)
  · rw [hb.2 x hx, norm_zero]
    exact le_max_right _ _

end BoundedWavePacket

/-- The inner product formula for bounded packets contains its smooth case
`LocalWavePacketInnerProductStatement`. -/
theorem localWavePacketInnerProduct_of_bounded (h : BoundedWavePacketInnerProductStatement) :
    LocalWavePacketInnerProductStatement := by
  intro F _ _ G P M U P' M' U' A A' _ _ _ _ _ _ _ _ _ _ _ p _ iU l _ a r _ _ _ hA hT p' _ iU' l' _
    a' r' _ _ _ hA' hT' π' hG hU hU' hlπ' K hK hK' Nr dr rho hsmooth hcalc hKmax hrho μM' _ hμM'
    n n' e e' β' hβc' hβs' hβ1' k v c S E D hv hS hc hSD hE hEis k' v' c' S' E' D' hv' hS' hc'
    hSD' hE' hEis' T _ w cw hw hinj hsurj mi ψ coeff DM hψ hSDM hcoeff hexp
  exact h F G P M U P' M' U' A A' p iU l a r hA hT p' iU' l' a' r' hA' hT' π' hG hU hU' hlπ' K hK
    hK' rho hsmooth hcalc hKmax hrho μM' hμM' e e' β' hβc' hβs' hβ1' k v c S E D hv hS
    (fun j => measurable_bounded_of_contDiff hS (hc j)) hSD hE hEis k' v' c' S' E' D' hv' hS'
    (fun j => measurable_bounded_of_contDiff hS' (hc' j)) hSD' hE' hEis' T w cw hw hinj hsurj mi
    ψ coeff DM hψ hSDM hcoeff hexp

/-- The norm bound for bounded packets contains its smooth case
`LocalWavePacketNormBoundStatement`. -/
theorem localWavePacketNormBound_of_bounded (h : BoundedWavePacketNormBoundStatement) :
    LocalWavePacketNormBoundStatement := by
  intro F _ _ G P M U A _ _ _ _ _ _ _ p _ iU l _ a r _ _ _ hA hT π hG hU hlπ K hK Nr dr rho
    hsmooth hcalc hKmax hrho μM _ hμM n e β hβc hβs hβ1 k v c S E D hv hS hc hSD hE hEis
  exact h F G P M U A p iU l a r hA hT π hG hU hlπ K hK rho hsmooth hcalc hKmax hrho μM hμM e β
    hβc hβs hβ1 k v c S E D hv hS (fun j => measurable_bounded_of_contDiff hS (hc j)) hSD hE hEis

end Langlands.Global

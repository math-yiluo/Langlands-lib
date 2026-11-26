import Langlands.Global.LeftCosetWeilMeasure
import Langlands.Global.AdelicInducedInnerProductIntegrable
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Integral.Prod

/-! # Discrete quotient integration through a product of group coordinates -/

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal

namespace Langlands.Global.LeftCosetSpace

variable {G H K : Type*} [Group G] [Group H] [MeasurableSpace G] [MeasurableSpace H]
  [MeasurableSpace K] [MeasurableMul G] [MeasurableMul H]
  [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [BorelSpace G]
  (i : H →* G) (hi : Function.Injective i) (him : Measurable i) (j : K → G) (hjm : Measurable j)
  (Γ : Subgroup H) (Δ : Subgroup G) (hΓ : IsDiscrete (Δ : Set G))
  (μG : Measure G) (μH : Measure H) (μK : Measure K) [SFinite μH] [SFinite μK]
  [SMulInvariantMeasure Γ H μH]

include him hjm in
omit [MeasurableMul G] [MeasurableMul H] in
private theorem measurable_mul_coordinates : Measurable (fun x : H × K => i x.1 * j x.2) :=
  (him.comp measurable_fst).mul (hjm.comp measurable_snd)

include hi him hjm in
/-- A strict fundamental domain of `Γ` in `H` cuts out the quotient measure when the ambient
measure is the pushforward of product measure by `(h, k) ↦ i(h) j(k)`. -/
theorem discreteQuotientMeasure_map_mul_prod
    (hΔ : Γ.map i = Δ)
    (hμ : Measure.map (fun x : H × K => i x.1 * j x.2) (μH.prod μK) = μG)
    {D : Set H} (hD : MeasurableSet D) (huniq : ∀ h : H, ∃! δ : Γ, (δ : H) * h ∈ D) :
    discreteQuotientMeasure Δ hΓ μG =
      Measure.map (fun x : H × K => mk Δ (i x.1 * j x.2)) ((μH.restrict D).prod μK) := by
  subst Δ
  let Δ := Γ.map i
  let E := fundamentalDomain Δ hΓ
  let e := Subgroup.equivMapOfInjective Γ i hi
  have hm := measurable_mul_coordinates i him j hjm
  let : Countable Δ := countable_of_isDiscrete Δ hΓ
  let : Countable Γ := e.injective.countable
  have hDfd : IsFundamentalDomain Γ D μH := IsFundamentalDomain.mk' hD.nullMeasurableSet huniq
  have hm' : Measurable (fun x : H × K => mk Δ (i x.1 * j x.2)) :=
    (measurable_mk Δ).comp hm
  ext S hS
  rw [discreteQuotientMeasure, quotientMeasure_apply _ _ _ hS, ← hμ,
    Measure.map_apply hm (((measurable_mk Δ) hS).inter (measurableSet_fundamentalDomain Δ hΓ)),
    Measure.map_apply hm' hS,
    Measure.prod_apply_symm (hm (((measurable_mk Δ) hS).inter
      (measurableSet_fundamentalDomain Δ hΓ))),
    Measure.prod_apply_symm (hm' hS)]
  refine lintegral_congr fun k => ?_
  let f : H → G := fun x => i x * j k
  have hf : Measurable f := him.mul_const _
  let T := f ⁻¹' (mk Δ ⁻¹' S)
  let E' := f ⁻¹' E
  change μH (T ∩ E') = (μH.restrict D) T
  rw [Measure.restrict_apply (hf ((measurable_mk Δ) hS))]
  have hE' : IsFundamentalDomain Γ E' μH := by
    refine IsFundamentalDomain.mk' (hf (measurableSet_fundamentalDomain Δ hΓ)).nullMeasurableSet ?_
    intro x
    have he (δ : Γ) : (δ : H) * x ∈ E' ↔ (e δ : G) * f x ∈ E := by
      change i (δ.val * x) * j k ∈ E ↔ i δ.val * (i x * j k) ∈ E
      rw [map_mul, mul_assoc]
    obtain ⟨δ, hδ, hu⟩ := fundamentalDomain_unique Δ hΓ (f x)
    exact ⟨e.symm δ, (he _).2 (by simpa only [MulEquiv.apply_symm_apply] using hδ),
      fun γ hγ => e.injective (by rw [e.apply_symm_apply]; exact hu _ ((he γ).1 hγ))⟩
  apply hE'.measure_set_eq hDfd (hf ((measurable_mk Δ) hS))
  intro γ
  ext x
  change mk Δ (i (γ.val * x) * j k) ∈ S ↔ mk Δ (i x * j k) ∈ S
  rw [map_mul, mul_assoc, show i γ.val = (e γ : G) from rfl, mk_subgroup_mul]

/-- A discrete quotient of a Polish group has a Borel section. -/
theorem exists_measurable_section {H : Type} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [PolishSpace H] [MeasurableSpace H] [BorelSpace H]
    (Γ : Subgroup H) (hΓ : IsDiscrete (Γ : Set H)) :
    ∃ s : LeftCosetSpace Γ → H, Measurable s ∧ ∀ q, mk Γ (s q) = q := by
  let : T2Space (LeftCosetSpace Γ) :=
    Langlands.QuotientIntegration.leftQuotient_t2Space Γ (Γ.isClosed_of_isDiscrete hΓ)
  let : BorelSpace (LeftCosetSpace Γ) := discreteQuotientBorelSpace Γ hΓ
  let D := fundamentalDomain Γ hΓ
  have hD := measurableSet_fundamentalDomain Γ hΓ
  have hi : Set.InjOn (mk Γ) D := by
    intro x hx y hy hxy
    let d : Γ := ⟨y * x⁻¹, (mk_eq_mk_iff Γ x y).1 hxy⟩
    have hd : d.val * x ∈ D := by simpa [d] using hy
    obtain ⟨δ, _, hδ⟩ := fundamentalDomain_unique Γ hΓ x
    have h1 : d = 1 := (hδ d hd).trans (hδ 1 (by simpa using hx)).symm
    have h := congrArg (fun z : Γ => z.val * x) h1
    simpa [d] using h.symm
  let t : D → LeftCosetSpace Γ := fun x => mk Γ x.val
  have ht : MeasurableEmbedding t :=
    (continuous_mk Γ).continuousOn.measurableEmbedding hD hi
  have hsurj : Function.Surjective t := by
    intro q
    obtain ⟨x, rfl⟩ := mk_surjective Γ q
    obtain ⟨d, hd, _⟩ := fundamentalDomain_unique Γ hΓ x
    exact ⟨⟨d.val * x, hd⟩, mk_subgroup_mul Γ d x⟩
  let e : D ≃ LeftCosetSpace Γ := Equiv.ofBijective t ⟨ht.injective, hsurj⟩
  have he : Measurable e.symm := by
    intro T hT
    have h : e.symm ⁻¹' T = e '' T := (e.image_eq_preimage_symm T).symm
    rw [h]
    exact ht.measurableSet_image' hT
  exact ⟨Subtype.val ∘ e.symm, measurable_subtype_coe.comp he, e.apply_symm_apply⟩

/-- Jointly measurable functions which are invariant in the group variable descend to the
product with the discrete quotient. -/
theorem measurable_out_of_invariant_prod {H X E : Type} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [PolishSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace X] [MeasurableSpace E] {Γ : Subgroup H} (hΓ : IsDiscrete (Γ : Set H))
    (f : X → H → E) (hf : Measurable (fun z : X × H => f z.1 z.2))
    (hinv : ∀ x, ∀ d ∈ Γ, ∀ h, f x (d * h) = f x h) :
    Measurable (fun z : X × LeftCosetSpace Γ => f z.1 z.2.out) := by
  obtain ⟨s, hs, hsq⟩ := exists_measurable_section Γ hΓ
  have hEq (x : X × LeftCosetSpace Γ) : f x.1 x.2.out = f x.1 (s x.2) := by
    calc
      _ = f x.1 (mk Γ (s x.2)).out := congrArg (fun q => f x.1 (Quotient.out q)) (hsq x.2).symm
      _ = _ := out_mk_of_invariant Γ (f x.1) (hinv x.1) _
  have h : Measurable (fun z : X × LeftCosetSpace Γ => f z.1 (s z.2)) :=
    hf.comp (measurable_fst.prodMk (hs.comp measurable_snd))
  exact (funext hEq).symm ▸ h

/-- Measurability of a function obtained from radical, Levi and compact coordinates after
passing to radical cosets. -/
theorem measurable_radicalQuotient_product {N M K G : Type} [Group N] [Group G]
    [MeasurableSpace N] [TopologicalSpace N] [IsTopologicalGroup N] [PolishSpace N]
    [LocallyCompactSpace N] [BorelSpace N] [MeasurableSpace M] [MeasurableSpace K]
    [MeasurableSpace G] [MeasurableMul₂ G] {Δ : Subgroup N} (hΔ : IsDiscrete (Δ : Set N))
    (u : N →* G) (m : M → G) (k : K → G) (hu : Measurable u) (hm : Measurable m)
    (hk : Measurable k) (f : G → ℂ) (hf : Measurable f)
    (hInv : ∀ d ∈ Δ, ∀ g, f (u d * g) = f g) :
    Measurable (fun z : (LeftCosetSpace Δ × M) × K => f (u z.1.1.out * m z.1.2 * k z.2)) := by
  have h : Measurable (fun z : (M × K) × LeftCosetSpace Δ => f (u z.2.out * m z.1.1 * k z.1.2)) := by
    apply measurable_out_of_invariant_prod hΔ (f := fun (x : M × K) n => f (u n * m x.1 * k x.2))
    · exact hf.comp (((hu.comp measurable_snd).mul
        (hm.comp (measurable_fst.comp measurable_fst))).mul
          (hk.comp (measurable_snd.comp measurable_fst)))
    · intro x d hd n
      simpa only [map_mul, mul_assoc] using hInv d hd (u n * m x.1 * k x.2)
  let r : (LeftCosetSpace Δ × M) × K → (M × K) × LeftCosetSpace Δ :=
    fun z => ((z.1.2, z.2), z.1.1)
  have hr : Measurable r := by dsimp only [r]; fun_prop
  exact h.comp hr

/-- Fubini in the order compact, Levi, radical. A period invariant under the principal Levi
subgroup descends to its count-normalized quotient. -/
theorem refold_discrete_fibre {M K X : Type} [Group M] [TopologicalSpace M]
    [IsTopologicalGroup M] [LocallyCompactSpace M] [PolishSpace M] [MeasurableSpace M]
    [BorelSpace M] [MeasurableSpace K] [MeasurableSpace X]
    (Γ : Subgroup M) (hΓ : IsDiscrete (Γ : Set M))
    (μX : Measure X) (μM : Measure M) (μK : Measure K)
    [SFinite μX] [SFinite μM] [SFinite μK]
    (f : (X × M) × K → ℂ) (hf : Measurable f)
    (hInt : Integrable f ((μX.prod (μM.restrict (fundamentalDomain Γ hΓ))).prod μK))
    (hInv : ∀ k, ∀ d ∈ Γ, ∀ m, (∫ x, f ((x, d * m), k) ∂μX) = ∫ x, f ((x, m), k) ∂μX) :
    let A := fun z : K × LeftCosetSpace Γ => ∫ x, f ((x, z.2.out), z.1) ∂μX
    let μ := μK.prod (discreteQuotientMeasure Γ hΓ μM)
    Integrable A μ ∧ (∫ z, A z ∂μ) =
      ∫ z, f z ∂((μX.prod (μM.restrict (fundamentalDomain Γ hΓ))).prod μK) := by
  intro A μ
  let ν := μM.restrict (fundamentalDomain Γ hΓ)
  let e : ((K × M) × X) ≃ᵐ ((X × M) × K) :=
    MeasurableEquiv.prodComm.trans
      ((MeasurableEquiv.refl X).prodCongr MeasurableEquiv.prodComm) |>.trans MeasurableEquiv.prodAssoc.symm
  have he : MeasurePreserving e ((μK.prod ν).prod μX) ((μX.prod ν).prod μK) :=
    ((measurePreserving_prodAssoc μX ν μK).symm MeasurableEquiv.prodAssoc).comp
      (((MeasurePreserving.id μX).prod Measure.measurePreserving_swap).comp Measure.measurePreserving_swap)
  let B (k : K) (m : M) := ∫ x, f ((x, m), k) ∂μX
  have hB : Integrable (fun z : K × M => B z.1 z.2) (μK.prod ν) :=
    (he.integrable_comp_of_integrable hInt).integral_prod_left
  have hbm : Measurable (fun z : K × M => B z.1 z.2) :=
    (hf.comp he.measurable).stronglyMeasurable.integral_prod_right'.measurable
  have hm : Measurable A := measurable_out_of_invariant_prod hΓ B hbm hInv
  let a : K × M → K × LeftCosetSpace Γ := Prod.map id (mk Γ)
  have ha : MeasurePreserving a (μK.prod ν) μ :=
    (MeasurePreserving.id μK).prod ⟨measurable_mk Γ, rfl⟩
  have heval : A ∘ a = fun z => B z.1 z.2 :=
    funext fun z => out_mk_of_invariant Γ (B z.1) (hInv z.1) z.2
  refine ⟨?_, ?_⟩
  · rw [← ha.map_eq, integrable_map_measure hm.aestronglyMeasurable ha.measurable.aemeasurable,
      heval]
    exact hB
  · rw [← ha.map_eq, integral_map ha.measurable.aemeasurable hm.aestronglyMeasurable]
    change (∫ x, (A ∘ a) x ∂μK.prod ν) = _
    rw [heval, ← he.integral_comp e.measurableEmbedding f]
    exact (integral_prod _ (he.integrable_comp_of_integrable hInt)).symm

end Langlands.Global.LeftCosetSpace

namespace Langlands.Global

open scoped CompactlySupported Pointwise

/-- A compact-factor integration formula on compactly supported continuous functions
identifies the corresponding product pushforward measure. -/
theorem map_compactFactor_eq_of_integral {G H X K : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [TopologicalSpace.PseudoMetrizableSpace G]
    [TopologicalSpace H] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
    (i : H → G) (hi : IsClosedEmbedding i) (e : X ≃ₜ H) (j : K → G) (hj : Continuous j)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    [SFinite ν] (κ : Measure K) [IsFiniteMeasure κ]
    (h : ∀ f : C_c(G, ℝ), ∫ g, f g ∂μ = ∫ k, ∫ x, f (i (e x) * j k) ∂ν ∂κ) :
    Measure.map (fun z : X × K => i (e z.1) * j z.2) (ν.prod κ) = μ := by
  let f : X × K → G := fun z => i (e z.1) * j z.2
  have hf : Continuous f := ((hi.continuous.comp e.continuous).comp continuous_fst).mul
    (hj.comp continuous_snd)
  have hpre {C : Set G} (hC : IsCompact C) : IsCompact (f ⁻¹' C) := by
    let D := (i ∘ e) ⁻¹' (C * (j '' (Set.univ : Set K))⁻¹)
    have hD : IsCompact D := (hi.comp e.isClosedEmbedding).isCompact_preimage
      (hC.mul ((isCompact_univ.image hj).inv))
    apply (hD.prod (isCompact_univ : IsCompact (Set.univ : Set K))).of_isClosed_subset
      (hC.isClosed.preimage hf)
    rintro ⟨x, k⟩ hx
    refine ⟨?_, Set.mem_univ _⟩
    change i (e x) ∈ C * (j '' (Set.univ : Set K))⁻¹
    exact ⟨f (x, k), hx, (j k)⁻¹, ⟨k, Set.mem_univ _, (inv_inv _).symm⟩, mul_inv_cancel_right _ _⟩
  let : IsFiniteMeasureOnCompacts (Measure.map f (ν.prod κ)) := ⟨fun C hC => by
    rw [Measure.map_apply hf.measurable hC.measurableSet]
    exact (hpre hC).measure_lt_top⟩
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  have hs : HasCompactSupport (g ∘ f) :=
    (hpre g.hasCompactSupport).of_isClosed_subset isClosed_closure
      (closure_minimal (fun _ hx => subset_closure hx) (isClosed_closure.preimage hf))
  have hg : Integrable (g ∘ f) (ν.prod κ) := (g.continuous.comp hf).integrable_of_hasCompactSupport hs
  change (∫ x, g x ∂Measure.map f (ν.prod κ)) = _
  rw [integral_map (f := fun x => g x) hf.measurable.aemeasurable
    g.continuous.aestronglyMeasurable]
  change (∫ x, (g ∘ f) x ∂ν.prod κ) = _
  rw [integral_prod_symm _ hg]
  exact (h g).symm

/-- Two pushforward formulas with a common parameter space give matching integrals if the
pulled back functions agree after applying the density. -/
theorem integrable_integral_of_weighted_pushforwards {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure X) (μ : Measure Y) (κ : Measure Z)
    (a : X → Y) (b : X → Z) (w : X → ℝ) (hw : Measurable w) (hn : ∀ x, 0 ≤ w x)
    (ha : MeasurePreserving a (ν.withDensity fun x => ENNReal.ofReal (w x)) μ)
    (hb : MeasurePreserving b ν κ)
    (f : Y → ℂ) (g : Z → ℂ) (hf : Measurable f) (hg : Measurable g)
    (h : ∀ x, (w x : ℂ) * f (a x) = g (b x)) :
    (Integrable f μ ↔ Integrable g κ) ∧ (∫ y, f y ∂μ) = ∫ z, g z ∂κ := by
  have hd : Measurable (fun x => ENNReal.ofReal (w x)) := ENNReal.measurable_ofReal.comp hw
  have ht : ∀ᵐ x ∂ν, ENNReal.ofReal (w x) < ∞ := Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have he : (fun x => (ENNReal.ofReal (w x)).toReal • (f ∘ a) x) = g ∘ b := by
    funext x
    rw [ENNReal.toReal_ofReal (hn x), Complex.real_smul]
    exact h x
  constructor
  · rw [← ha.map_eq, ← hb.map_eq, integrable_map_measure hf.aestronglyMeasurable ha.measurable.aemeasurable,
      integrable_map_measure hg.aestronglyMeasurable hb.measurable.aemeasurable,
      integrable_withDensity_iff_integrable_smul' hd ht, he]
  · rw [← ha.map_eq, ← hb.map_eq, integral_map ha.measurable.aemeasurable hf.aestronglyMeasurable,
      integral_map hb.measurable.aemeasurable hg.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul hd ht]
    exact congrArg (fun k : X → ℂ => ∫ x, k x ∂ν) he

/-- Fibrewise equality of absolute and complex integrals transports integrability and the
integral over two more factors. -/
theorem integrable_integral_prod₃_of_fibres {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) (κ : Measure Z) [SFinite μ] [SFinite ν] [SFinite κ]
    (f g : (X × Y) × Z → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hn : ∀ (y : Y) (z : Z), (∫⁻ x, ‖f ((x, y), z)‖ₑ ∂μ) = ∫⁻ x, ‖g ((x, y), z)‖ₑ ∂μ)
    (he : ∀ (y : Y) (z : Z), (∫ x, f ((x, y), z) ∂μ) = ∫ x, g ((x, y), z) ∂μ)
    (h : Integrable g ((μ.prod ν).prod κ)) :
    Integrable f ((μ.prod ν).prod κ) ∧
      (∫ x, f x ∂((μ.prod ν).prod κ)) = ∫ x, g x ∂((μ.prod ν).prod κ) := by
  have hn' : (∫⁻ x, ‖f x‖ₑ ∂((μ.prod ν).prod κ)) = ∫⁻ x, ‖g x‖ₑ ∂((μ.prod ν).prod κ) := by
    rw [lintegral_prod_symm _ hf.enorm.aemeasurable, lintegral_prod_symm _ hg.enorm.aemeasurable]
    refine lintegral_congr fun z => ?_
    have hfz : Measurable (fun x : X × Y => ‖f (x, z)‖ₑ) := hf.enorm.comp measurable_prodMk_right
    have hgz : Measurable (fun x : X × Y => ‖g (x, z)‖ₑ) := hg.enorm.comp measurable_prodMk_right
    rw [lintegral_prod_symm _ hfz.aemeasurable, lintegral_prod_symm _ hgz.aemeasurable]
    exact lintegral_congr fun y => hn y z
  have hfi : Integrable f ((μ.prod ν).prod κ) :=
    ⟨hf.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr
      (hn'.symm ▸ (hasFiniteIntegral_iff_enorm.mp h.hasFiniteIntegral))⟩
  refine ⟨hfi, ?_⟩
  rw [integral_prod_symm _ hfi, integral_prod_symm _ h]
  refine integral_congr_ae ?_
  filter_upwards [hfi.prod_left_ae, h.prod_left_ae] with z hfz hgz
  rw [integral_prod_symm _ hfz, integral_prod_symm _ hgz]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => he y z)

end Langlands.Global

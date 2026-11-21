import Langlands.Global.AdelicImaginaryIntertwiningProperties
import Langlands.Analysis.HolomorphicContDiff

/-! # Density of smooth compactly supported families in Arthur's space `L̂`

Bridge for the input `SymmetricFamilyDensityStatement` of the spectral transform reduction. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct InnerProductSpace ENNReal Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

section Parameters

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in
/-- `μ ↦ iμ` is injective: `Im(iμ) = μ` factorwise. -/
theorem imaginaryParameter_injective (P : GroupScheme (Spec (CommRingCat.of F))) :
    Function.Injective (imaginaryParameter F P) := by
  have hleft : (AlgebraTensorModule.map (Complex.imLm.restrictScalars ℝ) LinearMap.id :
      ComplexCharacterParameter F P →ₗ[ℝ] RealCharacterParameter F P).comp
        (imaginaryParameter F P) = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.inductionOn with
    | tmul s χ => simp [imaginaryParameter]
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x y hxy
  have hx := LinearMap.congr_fun hleft x
  have hy := LinearMap.congr_fun hleft y
  rw [LinearMap.comp_apply, LinearMap.id_apply] at hx hy
  rw [← hx, ← hy, hxy]

variable {P M Q M' R M'' : GroupScheme (Spec (CommRingCat.of F))}

omit [NumberField F] in
/-- The real forms of the maps `λ ↦ wλ` compose as the complex maps do. -/
theorem realWeylParameter_eq_comp_of_weylParameter {l : M ⟶ P} {c : M'' ⟶ M} {π'' : R ⟶ M''}
    {l' : M' ⟶ Q} {c' : M'' ⟶ M'} {c₀ : M' ⟶ M} {π' : Q ⟶ M'}
    (h : weylParameter l c π'' = (weylParameter l' c' π'').comp (weylParameter l c₀ π')) :
    realWeylParameter l c π'' = (realWeylParameter l' c' π'').comp (realWeylParameter l c₀ π') := by
  refine LinearMap.ext fun mu => imaginaryParameter_injective R ?_
  rw [LinearMap.comp_apply, ← weylParameter_imaginaryParameter, ← weylParameter_imaginaryParameter,
    ← weylParameter_imaginaryParameter, h, LinearMap.comp_apply]

end Parameters

section Smooth

variable {F : Type} [Field F] [NumberField F] {P : GroupScheme (Spec (CommRingCat.of F))}

omit [NumberField F] in
/-- A scalar function meromorphic in coordinates on a domain containing the imaginary axis is
smooth along the imaginary axis, read in real coordinates `e`. -/
theorem contDiff_comp_imaginaryParameter {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) {coeff : ComplexCharacterParameter F P → ℂ}
    {D : Set (ComplexCharacterParameter F P)} (hc : IsMeromorphicInCoordinatesOn coeff D)
    (hD : Set.range (imaginaryParameter F P) ⊆ D) :
    ContDiff ℝ (⊤ : ℕ∞) fun x => coeff (imaginaryParameter F P (e x)) := by
  obtain ⟨hfin, hmero⟩ := hc
  set m := Module.finrank ℂ (ComplexCharacterParameter F P)
  let eC : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P :=
    (Module.finBasis ℂ (ComplexCharacterParameter F P)).equivFun.symm
  obtain ⟨hopen, -, hholo, -⟩ := hmero m eC
  have hdiff : DifferentiableOn ℂ (coeff ∘ eC) (eC ⁻¹' D) := fun z hz =>
    (mdifferentiableWithinAt_iff_differentiableWithinAt.1
      (hholo (ContinuousLinearMap.id ℂ ℂ) z hz))
  let A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℂ) :=
    (eC.symm.toLinearMap.restrictScalars ℝ) ∘ₗ (imaginaryParameter F P) ∘ₗ e.toLinearMap
  have hA : ∀ x, LinearMap.toContinuousLinearMap A x ∈ eC ⁻¹' D := fun x => by
    simp only [Set.mem_preimage, LinearMap.coe_toContinuousLinearMap', A, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    exact hD ⟨e x, rfl⟩
  have := Langlands.Analysis.contDiff_comp_of_differentiableOn hopen hdiff
    (LinearMap.toContinuousLinearMap A) hA
  convert this using 2 with x
  simp [A]

end Smooth

section Symmetrization

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*} [∀ i, MeasurableSpace (X i)]
  (ν : ∀ i, Measure (X i)) {Hs : I → Type*} [∀ i, NormedAddCommGroup (Hs i)]
  [∀ i, InnerProductSpace ℂ (Hs i)] (nP : I → ℕ)

/-- The inner product with an element of the `i₀`-th factor of `PiLp`. -/
theorem piLp_inner_single (Θ : PiLp 2 fun i => Lp (Hs i) 2 (((nP i : ℝ≥0∞))⁻¹ • ν i)) (i₀ : I)
    (f : Lp (Hs i₀) 2 (((nP i₀ : ℝ≥0∞))⁻¹ • ν i₀)) :
    ⟪Θ, PiLp.single 2 i₀ f⟫_ℂ = ⟪Θ i₀, f⟫_ℂ := by
  rw [PiLp.inner_apply, Finset.sum_eq_single i₀]
  · rw [PiLp.single_eq_same]
  · intro i _ hi
    rw [PiLp.ofLp_single, Pi.single_eq_of_ne hi, inner_zero_right]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

omit [Fintype I] [DecidableEq I] in
/-- The `L²` inner product with the class of `x ↦ c(x) • h` for the measure `nP⁻¹ ν`. -/
theorem inner_eq_integral_smul {i : I}
    (Θ₀ : Lp (Hs i) 2 (((nP i : ℝ≥0∞))⁻¹ • ν i)) {c : X i → ℂ} {h : Hs i}
    {f : Lp (Hs i) 2 (((nP i : ℝ≥0∞))⁻¹ • ν i)}
    (hf : f =ᵐ[((nP i : ℝ≥0∞))⁻¹ • ν i] fun x => c x • h) :
    ⟪Θ₀, f⟫_ℂ = ((nP i : ℂ))⁻¹ * ∫ x, c x * ⟪Θ₀ x, h⟫_ℂ ∂(ν i) := by
  rw [L2.inner_def, integral_congr_ae (hf.mono fun x hx => by
    show ⟪Θ₀ x, f x⟫_ℂ = c x * ⟪Θ₀ x, h⟫_ℂ
    rw [hx, inner_smul_right]), integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]

omit [Fintype I] [DecidableEq I] in
/-- The inner product of a symmetric `Θ'` with the class of the transported function
`y ↦ c(τ⁻¹ y) • M(τ⁻¹ y) h`, for `M(x)` isometric and `Θ'(τ x) = M(x) Θ₀(x)`. -/
theorem inner_toLp_transport {i₀ i' : I} (τ : X i₀ ≃ᵐ X i')
    (hτ : MeasurePreserving τ (ν i₀) (ν i')) (Mx : X i₀ → Hs i₀ →L[ℂ] Hs i')
    (hiso : ∀ x a b, ⟪Mx x a, Mx x b⟫_ℂ = ⟪a, b⟫_ℂ)
    (Θ₀ : Lp (Hs i₀) 2 (((nP i₀ : ℝ≥0∞))⁻¹ • ν i₀))
    (Θ' : Lp (Hs i') 2 (((nP i' : ℝ≥0∞))⁻¹ • ν i'))
    (hsym : ∀ᵐ x ∂(ν i₀), Θ' (τ x) = Mx x (Θ₀ x)) (c : X i₀ → ℂ) (h : Hs i₀)
    (hG : MemLp (fun y => c (τ.symm y) • Mx (τ.symm y) h) 2 (((nP i' : ℝ≥0∞))⁻¹ • ν i')) :
    ⟪Θ', hG.toLp _⟫_ℂ = ((nP i' : ℂ))⁻¹ * ∫ x, c x * ⟪Θ₀ x, h⟫_ℂ ∂(ν i₀) := by
  rw [L2.inner_def, integral_congr_ae (hG.coeFn_toLp.mono fun y hy => by
    show ⟪Θ' y, hG.toLp _ y⟫_ℂ = ⟪Θ' y, c (τ.symm y) • Mx (τ.symm y) h⟫_ℂ
    rw [hy]), integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast,
    ← hτ.integral_comp' (fun y => ⟪Θ' y, c (τ.symm y) • Mx (τ.symm y) h⟫_ℂ)]
  congr 1
  refine integral_congr_ae (hsym.mono fun x hx => ?_)
  simp only [MeasurableEquiv.symm_apply_apply]
  rw [hx, inner_smul_right, hiso]

variable {T : I → I → Type*} [∀ i i', Fintype (T i i')] (τ : ∀ i i', T i i' → X i ≃ᵐ X i')
  (Mop : ∀ i i', T i i' → X i → Hs i →L[ℂ] Hs i')

/-- The symmetrization `SΨ_{i'} = nP(i₀)⁻¹ ∑_t [y ↦ c(τ_t⁻¹ y) • M_t(τ_t⁻¹ y) h]` of the generator
`single i₀ [c • h]` has the same inner products with symmetric families `Θ` as the generator,
when the operators are isometric and `∑_{i'} |T i₀ i'| / nP(i') = 1`. -/
theorem inner_symmetrized_eq (hτ : ∀ i i' t, MeasurePreserving (τ i i' t) (ν i) (ν i'))
    (hiso : ∀ i i' t x a b, ⟪Mop i i' t x a, Mop i i' t x b⟫_ℂ = ⟪a, b⟫_ℂ) (i₀ : I)
    (hcard : ∑ i', (Fintype.card (T i₀ i') : ℂ) / (nP i' : ℂ) = 1)
    (Θ : PiLp 2 fun i => Lp (Hs i) 2 (((nP i : ℝ≥0∞))⁻¹ • ν i))
    (hΘ : ∀ i i' t, ∀ᵐ x ∂(ν i), Θ i' (τ i i' t x) = Mop i i' t x (Θ i x))
    (c : X i₀ → ℂ) (h : Hs i₀)
    (hG : ∀ i' t, MemLp (fun y => c ((τ i₀ i' t).symm y) • Mop i₀ i' t ((τ i₀ i' t).symm y) h) 2
      (((nP i' : ℝ≥0∞))⁻¹ • ν i'))
    (f : Lp (Hs i₀) 2 (((nP i₀ : ℝ≥0∞))⁻¹ • ν i₀))
    (hf : f =ᵐ[((nP i₀ : ℝ≥0∞))⁻¹ • ν i₀] fun x => c x • h) :
    ⟪Θ, WithLp.toLp 2 (fun i' => ∑ t, ((nP i₀ : ℂ))⁻¹ • (hG i' t).toLp _)⟫_ℂ =
      ⟪Θ, PiLp.single 2 i₀ f⟫_ℂ := by
  set J := ∫ x, c x * ⟪Θ i₀ x, h⟫_ℂ ∂(ν i₀) with hJ
  have hterm : ∀ i' t, ⟪Θ i', (hG i' t).toLp _⟫_ℂ = ((nP i' : ℂ))⁻¹ * J := fun i' t =>
    inner_toLp_transport ν nP (τ i₀ i' t) (hτ i₀ i' t) (Mop i₀ i' t) (hiso i₀ i' t) (Θ i₀) (Θ i')
      (hΘ i₀ i' t) c h (hG i' t)
  rw [piLp_inner_single, inner_eq_integral_smul ν nP (Θ i₀) hf, PiLp.inner_apply]
  calc ∑ i', ⟪Θ i', (WithLp.toLp 2 (fun i' => ∑ t, ((nP i₀ : ℂ))⁻¹ • (hG i' t).toLp _)) i'⟫_ℂ
      = ∑ i', ∑ _t : T i₀ i', ((nP i₀ : ℂ))⁻¹ * (((nP i' : ℂ))⁻¹ * J) := by
        refine Finset.sum_congr rfl fun i' _ => ?_
        rw [PiLp.toLp_apply, inner_sum]
        exact Finset.sum_congr rfl fun t _ => by rw [inner_smul_right, hterm]
    _ = ∑ i', (Fintype.card (T i₀ i') : ℂ) / (nP i' : ℂ) * (((nP i₀ : ℂ))⁻¹ * J) := by
        refine Finset.sum_congr rfl fun i' _ => ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
    _ = ((nP i₀ : ℂ))⁻¹ * J := by rw [← Finset.sum_mul, hcard, one_mul]

omit [Fintype I] [DecidableEq I] in
/-- The symmetrization is symmetric, pointwise: if `φ : T i₀ i' ≃ T i₀ i''` composes with `r`
both on coordinates and on operators (the cocycle relation at `h`), then
`F_{i''}(τ_r y) = M_r(y) F_{i'}(y)`. -/
theorem symmetrized_apply_eq {i₀ i' i'' : I} (r : T i' i'') (c : X i₀ → ℂ) (h : Hs i₀) (a : ℂ)
    (φ : T i₀ i' ≃ T i₀ i'')
    (hτφ : ∀ s y, (τ i₀ i'' (φ s)).symm (τ i' i'' r y) = (τ i₀ i' s).symm y)
    (hMφ : ∀ s x, Mop i₀ i'' (φ s) x h = Mop i' i'' r (τ i₀ i' s x) (Mop i₀ i' s x h))
    (y : X i') :
    ∑ t, a • c ((τ i₀ i'' t).symm (τ i' i'' r y)) •
        Mop i₀ i'' t ((τ i₀ i'' t).symm (τ i' i'' r y)) h =
      Mop i' i'' r y (∑ s, a • c ((τ i₀ i' s).symm y) • Mop i₀ i' s ((τ i₀ i' s).symm y) h) := by
  rw [← φ.sum_comp, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hτφ, hMφ, MeasurableEquiv.apply_symm_apply, map_smul, map_smul]

omit [Fintype I] [DecidableEq I] in
private theorem ae_eq_sum_smul_toLp {j : I} {α : Type*} [Fintype α] (a : ℂ)
    {f : α → X j → Hs j} (hf : ∀ t, MemLp (f t) 2 (((nP j : ℝ≥0∞))⁻¹ • ν j)) :
    ⇑(∑ t, a • (hf t).toLp _ : Lp (Hs j) 2 (((nP j : ℝ≥0∞))⁻¹ • ν j))
      =ᵐ[ν j] fun y => ∑ t, a • f t y := by
  rw [← Measure.ae_ennreal_smul_measure_eq (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top (nP j)))
    (ν j)]
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  have hq : ∀ t ∈ (Finset.univ : Finset α),
      ⇑(a • (hf t).toLp _ : Lp (Hs j) 2 (((nP j : ℝ≥0∞))⁻¹ • ν j))
        =ᵐ[((nP j : ℝ≥0∞))⁻¹ • ν j] a • f t :=
    fun t _ => (Lp.coeFn_smul _ _).trans ((hf t).coeFn_toLp.const_smul a)
  refine (eventuallyEq_sum hq).trans (Filter.Eventually.of_forall fun y => ?_)
  simp [Finset.sum_apply]

omit [Fintype I] [DecidableEq I] in
/-- The classes `SΨ_{i'} = ∑_t a • [y ↦ c(τ_t⁻¹ y) • M_t(τ_t⁻¹ y) h]` satisfy the symmetry
condition almost everywhere. -/
theorem symmetrized_ae_symm (hτ : ∀ i i' t, MeasurePreserving (τ i i' t) (ν i) (ν i')) (i₀ : I)
    (c : X i₀ → ℂ) (h : Hs i₀) (a : ℂ)
    (hG : ∀ i' t, MemLp (fun y => c ((τ i₀ i' t).symm y) • Mop i₀ i' t ((τ i₀ i' t).symm y) h) 2
      (((nP i' : ℝ≥0∞))⁻¹ • ν i'))
    (hφ : ∀ i' i'' (r : T i' i''), ∃ φ : T i₀ i' ≃ T i₀ i'',
      (∀ s y, (τ i₀ i'' (φ s)).symm (τ i' i'' r y) = (τ i₀ i' s).symm y) ∧
      ∀ s x, Mop i₀ i'' (φ s) x h = Mop i' i'' r (τ i₀ i' s x) (Mop i₀ i' s x h))
    (i' i'' : I) (r : T i' i'') :
    ∀ᵐ y ∂(ν i'), (∑ t, a • (hG i'' t).toLp _ : Lp (Hs i'') 2 (((nP i'' : ℝ≥0∞))⁻¹ • ν i''))
        (τ i' i'' r y) =
      Mop i' i'' r y ((∑ t, a • (hG i' t).toLp _ : Lp (Hs i') 2 (((nP i' : ℝ≥0∞))⁻¹ • ν i')) y) := by
  have hF : ∀ j, ⇑(∑ t, a • (hG j t).toLp _ : Lp (Hs j) 2 (((nP j : ℝ≥0∞))⁻¹ • ν j))
      =ᵐ[ν j] fun y => ∑ t, a • c ((τ i₀ j t).symm y) • Mop i₀ j t ((τ i₀ j t).symm y) h :=
    fun j => ae_eq_sum_smul_toLp ν nP a (hG j)
  obtain ⟨φ, hτφ, hMφ⟩ := hφ i' i'' r
  filter_upwards [(hτ i' i'' r).quasiMeasurePreserving.tendsto_ae.eventually (hF i''), hF i']
    with y h1 h2
  rw [h1, h2]
  exact symmetrized_apply_eq τ Mop r c h a φ hτφ hMφ y

end Symmetrization

section Coordinates

/-- A linear map `ℝⁿ → ℝ^{n'}` preserving Lebesgue measure is a continuous linear equivalence
preserving `spectralMeasure`. -/
theorem exists_continuousLinearEquiv_of_measurePreserving {n n' : ℕ}
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n' → ℝ)) (hL : MeasurePreserving L volume volume) :
    ∃ τ : (Fin n → ℝ) ≃L[ℝ] (Fin n' → ℝ), (∀ x, τ x = L x) ∧
      MeasurePreserving τ (spectralMeasure n) (spectralMeasure n') := by
  obtain rfl : n = n' := Langlands.Analysis.eq_of_measurePreserving_linearMap L hL
  have hsurj := Langlands.Analysis.surjective_of_measurePreserving_linearMap L hL
  have hinj : Function.Injective L := LinearMap.injective_iff_surjective.2 hsurj
  refine ⟨(LinearEquiv.ofBijective L ⟨hinj, hsurj⟩).toContinuousLinearEquiv, fun x => rfl, ?_⟩
  exact measurePreserving_spectralMeasure_of_linearMap L hL

/-- `nP⁻¹ • spectralMeasure n` is finite on compact sets for `nP ≠ 0`. -/
theorem isFiniteMeasureOnCompacts_smul_spectralMeasure (n : ℕ) {nP : ℕ} (hnP : nP ≠ 0) :
    IsFiniteMeasureOnCompacts (((nP : ℝ≥0∞))⁻¹ • spectralMeasure n) := by
  have h1 : IsFiniteMeasureOnCompacts (spectralMeasure n) := by
    unfold spectralMeasure
    refine IsFiniteMeasureOnCompacts.smul _ (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 ?_))
    exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  exact IsFiniteMeasureOnCompacts.smul _ (ENNReal.inv_ne_top.2 (by exact_mod_cast hnP))

end Coordinates

section Weyl

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  {I : Type*} {P M : I → GroupScheme (Spec (CommRingCat.of F))}
  {p : ∀ i, P i ⟶ G} {l : ∀ i, M i ⟶ P i} {π : ∀ i, P i ⟶ M i}
  (hlπ : ∀ i, l i ≫ π i = 𝟙 (M i))
  (T : I → I → Type*) [∀ i i', Fintype (T i i')]
  (w : ∀ i i', T i i' → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
  (cw : ∀ i i', T i i' → (M i' ⟶ M i))
  (hW : ∀ i i' t, IsWeylConjugation (p i) (l i) (p i') (l i') (w i i' t) (cw i i' t))
  (hinj : ∀ i i', Function.Injective (fun t => weylParameter (l i) (cw i i' t) (π i')))
  (hsurj : ∀ i i', ∀ s ∈ weylParameterSet (p i) (l i) (p i') (l i') (π i'),
    ∃ t, weylParameter (l i) (cw i i' t) (π i') = s)

omit [NumberField F] [∀ i i', Fintype (T i i')] in
include hlπ hW hinj hsurj in
/-- Composition with `r ∈ Ω(P i', P i'')` is a bijection `Ω(P i₀, P i') → Ω(P i₀, P i'')`. -/
theorem exists_equiv_postcomp (i₀ : I) {i' i'' : I} (r : T i' i'') :
    ∃ φ : T i₀ i' ≃ T i₀ i'', ∀ s, weylParameter (l i₀) (cw i₀ i'' (φ s)) (π i'') =
      weylParameter (l i₀) (cw i' i'' r ≫ cw i₀ i' s) (π i'') := by
  obtain ⟨c', hr', hcr, hc'⟩ := (hW i' i'' r).exists_symm
  have hf (s : T i₀ i') := comp_mem_weylParameterSet_left (πb := π i'') (hW i' i'' r) (hlπ i')
    ⟨_, _, hW i₀ i' s, rfl⟩
  have hg (s : T i₀ i'') := comp_mem_weylParameterSet_left (πb := π i') hr' (hlπ i'')
    ⟨_, _, hW i₀ i'' s, rfl⟩
  choose f hf using fun s => hsurj i₀ i'' _ (hf s)
  choose g hg using fun s => hsurj i₀ i' _ (hg s)
  refine ⟨⟨f, g, ?_, ?_⟩, ?_⟩
  · intro s
    apply hinj i₀ i'
    simp only [hg, hf, weylParameter_comp _ _ _ _ _ _ (hlπ i''),
      weylParameter_comp _ _ _ _ _ _ (hlπ i')]
    rw [← Category.assoc, hc', Category.id_comp]
  · intro s
    apply hinj i₀ i''
    simp only [hf, hg, weylParameter_comp _ _ _ _ _ _ (hlπ i'),
      weylParameter_comp _ _ _ _ _ _ (hlπ i'')]
    rw [← Category.assoc, hcr, Category.id_comp]
  · intro s
    exact (hf s).trans (weylParameter_comp _ _ _ _ _ _ (hlπ i'))

omit [NumberField F] in
include hlπ hW hinj hsurj in
/-- The sum of the outgoing Weyl-set counts divided by the target weights is one, since the
weight is constant on the association class. -/
theorem sum_card_row_div_eq_one [Fintype I] (i₀ : I) :
    ∑ i', (Fintype.card (T i₀ i') : ℂ) / (∑ j, Fintype.card (T i' j) : ℕ) = 1 := by
  calc
    _ = ∑ i', (Fintype.card (T i' i₀) : ℂ) / (∑ j, Fintype.card (T i' j) : ℕ) := by
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [card_swap hlπ T w cw hW hinj hsurj i₀ i']
    _ = 1 := sum_card_div_card_eq_one hlπ T w cw hW hinj hsurj i₀

end Weyl

section SmoothSymmetrization

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {I : Type} [Fintype I] {P M U : I → GroupScheme (Spec (CommRingCat.of F))}
  {A : I → CommGroupScheme (Spec (CommRingCat.of F))}
  [∀ i, IsAffine (P i).X.left] [∀ i, LocallyOfFiniteType (P i).X.hom]
  [∀ i, IsAffine (M i).X.left] [∀ i, LocallyOfFiniteType (M i).X.hom] [∀ i, IsAffine (U i).X.left]
  {p : ∀ i, P i ⟶ G} [∀ i, IsClosedImmersion (p i).hom.hom.left]
  {iU : ∀ i, U i ⟶ P i} {l : ∀ i, M i ⟶ P i} [∀ i, IsClosedImmersion (iU i ≫ p i).hom.hom.left]
  {a : ∀ i, (A i).toGrp ⟶ M i} {r : ∀ i, ParabolicRootPresentation (p i) (l i) (a i)}
  [∀ i, Mono (r i).data.i.hom.hom.left] [∀ i, Fintype (relativeWeylGroup (r i).data.i)]
  [∀ i, Mono (CommGroupScheme.groupHom (r i).data.f).hom.hom.left]
  {hA : ∀ i, IsSplitTorus (A i).toGrp} {hT : ∀ i, IsSplitTorus (r i).data.T.toGrp}
  {π : ∀ i, P i ⟶ M i} {K : Subgroup (AdelicGroupPoints F G)}
  {hK : ∀ i, IsIwasawaCompact (p i) K} {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
  {hsmooth : SmoothOfRelativeDimension d G.X.hom} {hcalc : AdelicDifferentialCommutator F G hsmooth}
  {μM : ∀ i, Measure (AdelicGroupPoints F (M i))}
  {n : I → ℕ} {e : ∀ i, (Fin (n i) → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (P i)}
  {β : ∀ i, (Fin (n i) → ℝ) → ℝ} {T : I → I → Type} [∀ i i', Fintype (T i i')]
  {w : ∀ i i', T i i' → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)}
  {cw : ∀ i i', T i i' → (M i' ⟶ M i)}

local notation "Xₛ" => (fun i => Fin (n i) → ℝ)
local notation "Hₛ" => (fun i => inducedHilbertSpace K (IsIwasawaCompact.isCompact (hK i))
  rho hsmooth hcalc (p i) (iU i) (l i) (μM i) (e i) (β i))
local notation "μₕ" => (fun i => inducedL2Measure K (IsIwasawaCompact.isCompact (hK i))
  (l i) (μM i) (e i) (β i))
local notation "A₂" => (fun i => IsSquareIntegrableInducedForm K (IsIwasawaCompact.isCompact (hK i))
  rho hsmooth hcalc (p i) (iU i) (l i))
local notation "νₛ" => (fun i => spectralMeasure (n i))
local notation "nP" => (fun i => ∑ j, Fintype.card (T i j))
local notation "μₛ" => (fun i => (((nP i : ℝ≥0∞))⁻¹ • νₛ i))

private def transportedGenerator {X Y H H' : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup H'] [NormedSpace ℂ H']
    (τinv : Y → X) (M₀ : X → H →L[ℂ] H') (c : X → ℂ) (h : H) (y : Y) : H' :=
  c (τinv y) • M₀ (τinv y) h

private theorem memLp_sum_smul_const {X H α : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [NormedAddCommGroup H] [NormedSpace ℂ H] [Fintype α]
    (μx : Measure X) [IsFiniteMeasureOnCompacts μx] (C : α → X → ℂ) (b : α → H)
    (hc : ∀ q, Continuous (C q)) (hcc : ∀ q, HasCompactSupport (C q)) :
    MemLp (fun y => ∑ q, C q y • b q) 2 μx := by
  refine memLp_finsetSum (f := fun q y => C q y • b q) Finset.univ fun q _ => ?_
  have h₁ : Continuous (fun y => C q y • b q) := (hc q).smul continuous_const
  have h₂ : HasCompactSupport (fun y => C q y • b q) :=
    HasCompactSupport.smul_right (f' := fun _ => b q) (hcc q)
  exact h₁.memLp_of_hasCompactSupport h₂

set_option maxHeartbeats 2000000 in
/-- Every component of a symmetrized generator is represented by a finite smooth compactly
supported combination of square-integrable inducing forms. -/
private theorem exists_smooth_symmetrized_component
    (Mop : ∀ i i', T i i' → Xₛ i → (↥(Hₛ i) →L[ℂ] ↥(Hₛ i')))
    (hMop : ∀ i i' t, IsImaginaryIntertwiningOperator (hK i) (hK i') rho hsmooth hcalc (iU i) (l i)
      (a i) (r i) (hA i) (hT i) (iU i') (l i') (π i') (w i i' t) (cw i i' t) (μM i) (μM i')
      (e i) (e i') (β i) (β i') (Mop i i' t))
    (τ : ∀ i i', T i i' → (Xₛ i ≃L[ℝ] Xₛ i'))
    (hE : IntertwiningSquareIntegrableExpansionStatement) (hG : IsConnectedReductive G)
    (hUR : ∀ i, LeviSubgroup.IsGeometricUnipotentRadical (iU i))
    (hMul : ∀ i, IsIso (subgroupMultiplication (l i) (iU i))) (hπ : ∀ i, l i ≫ π i = 𝟙 (M i))
    (hKmax : IsMaximalCompactSubgroup F G K) (hrho : IsClosedSubgroup rho)
    (hW : ∀ i i' t, IsWeylConjugation (p i) (l i) (p i') (l i') (w i i' t) (cw i i' t))
    (hL' : ∀ i v, A₂ i v → MemLp (inducedRestriction K (p i) (l i) v) 2 (μₕ i))
    (i₀ i' : I) (hnP : nP i' ≠ 0) {v : AdelicGroupPoints F G → ℂ} (hv : A₂ i₀ v)
    (h : Hₛ i₀) (hh : ⇑(h : Lp ℂ 2 (μₕ i₀)) =ᵐ[μₕ i₀] inducedRestriction K (p i₀) (l i₀) v)
    {c : Xₛ i₀ → ℂ} (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c) :
    ∃ (hG₁ : ∀ t : T i₀ i', MemLp
        (transportedGenerator (X := Xₛ i₀) (Y := Xₛ i') (H := ↥(Hₛ i₀)) (H' := ↥(Hₛ i'))
          (τ i₀ i' t).symm (Mop i₀ i' t) c h) 2 (μₛ i')) (k : ℕ) (v' : Fin k → AdelicGroupPoints F G → ℂ) (c' : Fin k → Xₛ i' → ℂ),
      (∀ q, A₂ i' (v' q)) ∧ (∀ q, ContDiff ℝ (⊤ : ℕ∞) (c' q) ∧ HasCompactSupport (c' q)) ∧
      ∀ᵐ y ∂(νₛ i'),
        ⇑(((∑ t, (nP i₀ : ℂ)⁻¹ • (hG₁ t).toLp _ : Lp (Hₛ i') 2 (μₛ i')) y).1 : Lp ℂ 2 (μₕ i'))
          =ᵐ[μₕ i'] inducedRestriction K (p i') (l i') (fun g => ∑ q, c' q y * v' q g) := by
  classical
  have hEx (t : T i₀ i') := hE F G (P i₀) (M i₀) (U i₀) (P i') (M i') (U i') (A i₀) (A i')
    (p i₀) (iU i₀) (l i₀) (a i₀) (r i₀) (hA i₀) (hT i₀) (p i') (iU i') (l i') (a i')
    (r i') (π i') (w i₀ i' t) (cw i₀ i' t) hG (hUR i₀) (hUR i') (hMul i') (hπ i') (hW i₀ i' t)
    K (hK i₀) (hK i') rho hsmooth hcalc v hKmax hrho hv
  choose m ψ coeff D hψ hD hcoeff R₀ hR using hEx
  let hm (t : T i₀ i') (q : Fin (m t)) := hL' i' (ψ t q) (hψ t q)
  let b (t : T i₀ i') (q : Fin (m t)) : Hₛ i' :=
    ⟨(hm t q).toLp _, toLp_mem_inducedHilbertSpace K (hK i').isCompact rho hsmooth hcalc
      (p i') (iU i') (l i') (μM i') (e i') (β i') (hψ t q) (hm t q)⟩
  have hMap (t : T i₀ i') (x : Xₛ i₀) :
      Mop i₀ i' t x h = ∑ q, coeff t q (imaginaryParameter F (P i₀) (e i₀ x)) • b t q := by
    apply Subtype.ext
    change (Hₛ i').subtype (Mop i₀ i' t x h) = (Hₛ i').subtype _
    rw [map_sum]
    simp only [map_smul]
    exact map_eq_sum_smul_toLp_of_isImaginaryIntertwiningOperator (Mop i₀ i' t) (hMop i₀ i' t)
      hv (hψ t) (hD t) (hcoeff t) ⟨R₀ t, hR t⟩ (hm t) h hh x
  let C (t : T i₀ i') (q : Fin (m t)) (y : Xₛ i') : ℂ :=
    c ((τ i₀ i' t).symm y) * coeff t q (imaginaryParameter F (P i₀) (e i₀ ((τ i₀ i' t).symm y)))
  have hC (t : T i₀ i') (q : Fin (m t)) : ContDiff ℝ (⊤ : ℕ∞) (C t q) ∧ HasCompactSupport (C t q) := by
    have hτs : ContDiff ℝ (⊤ : ℕ∞) (τ i₀ i' t).symm :=
      (τ i₀ i' t).symm.toContinuousLinearMap.contDiff
    exact ⟨(hc.comp hτs).mul ((contDiff_comp_imaginaryParameter (e i₀) (hcoeff t q) (hD t)).comp hτs),
      (hcc.comp_homeomorph (τ i₀ i' t).symm.toHomeomorph).mul_right⟩
  have htransport (t : T i₀ i') (y : Xₛ i') :
      c ((τ i₀ i' t).symm y) • Mop i₀ i' t ((τ i₀ i' t).symm y) h = ∑ q, C t q y • b t q := by
    rw [hMap, Finset.smul_sum]
    simp only [smul_smul, C]
  let _ : IsFiniteMeasureOnCompacts (μₛ i') := isFiniteMeasureOnCompacts_smul_spectralMeasure (n i') hnP
  have hG₁ (t : T i₀ i') : MemLp
      (transportedGenerator (X := Xₛ i₀) (Y := Xₛ i') (H := ↥(Hₛ i₀)) (H' := ↥(Hₛ i'))
        (τ i₀ i' t).symm (Mop i₀ i' t) c h) 2 (μₛ i') := by
    have hsumLp := memLp_sum_smul_const (H := ↥(Hₛ i')) (μₛ i') (C t) (b t)
      (fun q => (hC t q).1.continuous) (fun q => (hC t q).2)
    exact MemLp.ae_eq (Filter.Eventually.of_forall fun y => (htransport t y).symm) hsumLp
  let J := Σ t : T i₀ i', Fin (m t)
  let E := Fintype.equivFin J
  let v' (q : Fin (Fintype.card J)) := ψ (E.symm q).1 (E.symm q).2
  let c' (q : Fin (Fintype.card J)) (y : Xₛ i') := (nP i₀ : ℂ)⁻¹ * C (E.symm q).1 (E.symm q).2 y
  refine ⟨hG₁, Fintype.card J, v', c', fun q => hψ (E.symm q).1 (E.symm q).2,
    fun q => ⟨contDiff_const.mul (hC (E.symm q).1 (E.symm q).2).1,
      (hC (E.symm q).1 (E.symm q).2).2.mul_left⟩, ?_⟩
  have hAE := ae_eq_sum_smul_toLp (X := Xₛ) (Hs := fun i => ↥(Hₛ i)) νₛ nP
    (j := i') (α := T i₀ i') (nP i₀ : ℂ)⁻¹ hG₁
  filter_upwards [hAE] with y hy
  have hsum : (∑ t : T i₀ i', (nP i₀ : ℂ)⁻¹ • ∑ q, C t q y • b t q) =
      ∑ q, c' q y • b (E.symm q).1 (E.symm q).2 := by
    let d (z : J) : Hₛ i' := ((nP i₀ : ℂ)⁻¹ * C z.1 z.2 y) • b z.1 z.2
    calc
      _ = ∑ z, d z := by
        simp only [Finset.smul_sum, smul_smul]
        exact (Fintype.sum_sigma' fun t q => ((nP i₀ : ℂ)⁻¹ * C t q y) • b t q).symm
      _ = _ := by
        rw [← E.sum_comp (fun q => c' q y • b (E.symm q).1 (E.symm q).2)]
        exact Finset.sum_congr rfl fun z _ => congrArg d (E.symm_apply_apply z).symm
  rw [hy]
  simp only [transportedGenerator, htransport]
  rw [hsum]
  change ⇑((Hₛ i').subtype _) =ᵐ[μₕ i'] _
  simp only [map_sum, map_smul]
  exact (sum_smul_toLp_mem_inducedHilbertSpace K (hK i').isCompact rho hsmooth hcalc (p i') (iU i')
    (l i') (μM i') (e i') (β i') (fun q => hψ (E.symm q).1 (E.symm q).2)
    (fun q => hm (E.symm q).1 (E.symm q).2) (fun q => c' q y)).2

end SmoothSymmetrization

/-- The smooth density input for the spectral transform follows from the Gram identities for
imaginary intertwining, the cocycle relation, square-integrable expansions and restrictions, and
independence of Weyl representatives. -/
def SymmetricFamilyDensityBridgeStatement : Prop :=
  IntertwiningImaginaryUnitarityStatement → IntertwiningCocycleStatement.{0} →
    IntertwiningSquareIntegrableExpansionStatement → InducedRestrictionMemLpStatement →
    IntertwiningRepresentativeIndependenceStatement → SymmetricFamilyDensityStatement

set_option maxHeartbeats 4000000 in
/-- Delorme's symmetrization argument on a spanning set of single-component generators. -/
theorem symmetricFamilyDensityBridge : SymmetricFamilyDensityBridgeStatement := by
  classical
  intro hU hC hE hL hI F _ _ G _ _ _ I _ P M U A _ _ _ _ p _ iU l _ a r _ _ _ hA hT π hG hUR hMul hπ
    K hK N d rho hsmooth hcalc hKmax hrho μM _ hμM n e β hβ T _ w cw hW hinj hsurj hw nP Mop hMop
  have : ∀ i, LocallyOfFiniteType (P i).X.hom := fun i =>
    IsClosedSubgroup.locallyOfFiniteType (j := p i)
      (inferInstance : IsClosedImmersion (p i).hom.hom.left)
  let Xs : I → Type := fun i => Fin (n i) → ℝ
  let Hs : I → Type := fun i => ↥(inducedHilbertSpace K (hK i).isCompact rho hsmooth hcalc
    (p i) (iU i) (l i) (μM i) (e i) (β i))
  let μh := fun i => inducedL2Measure K (hK i).isCompact (l i) (μM i) (e i) (β i)
  let A₂ := fun i => IsSquareIntegrableInducedForm K (hK i).isCompact rho hsmooth hcalc
    (p i) (iU i) (l i)
  let ν : ∀ i, Measure (Xs i) := fun i => spectralMeasure (n i)
  let μs : ∀ i, Measure (Xs i) := fun i => (nP i : ℝ≥0∞)⁻¹ • ν i
  have hL' : ∀ i v, A₂ i v → MemLp (inducedRestriction K (p i) (l i) v) 2 (μh i) :=
    fun i v hv => hL F G (P i) (M i) (U i) (A i) (p i) (iU i) (l i) (a i) (r i) (hA i) (hT i)
      (π i) hG (hUR i) (hMul i) (hπ i) K (hK i) rho hsmooth hcalc hKmax hrho (μM i) (hμM i)
      (e i) (β i) (hβ i).1 (hβ i).2.1 (hβ i).2.2.1 v hv
  have hnP (i : I) : nP i ≠ 0 := by
    have := nonempty_self T cw hsurj i
    exact (Finset.sum_pos' (fun _ _ => Nat.zero_le _)
      ⟨i, Finset.mem_univ _, Fintype.card_pos⟩).ne'
  have hτ₀ (i j : I) (t : T i j) := exists_continuousLinearEquiv_of_measurePreserving
    ((e j).symm.toLinearMap.comp ((realWeylParameter (l i) (cw i j t) (π j)).comp (e i).toLinearMap))
    (hw i j t)
  choose τ hτeq hτν using hτ₀
  let τm (i j : I) (t : T i j) : Xs i ≃ᵐ Xs j := (τ i j t).toHomeomorph.toMeasurableEquiv
  have hτm (i j : I) (t : T i j) : MeasurePreserving (τm i j t) (ν i) (ν j) := hτν i j t
  have hτ (i j : I) (t : T i j) (x : Xs i) :
      τ i j t x = (e j).symm (realWeylParameter (l i) (cw i j t) (π j) (e i x)) := hτeq i j t x
  have hiso (i j : I) (t : T i j) (x : Xs i) (f g : Hs i) :
      ⟪Mop i j t x f, Mop i j t x g⟫_ℂ = ⟪f, g⟫_ℂ :=
    inner_map_map_of_isImaginaryIntertwiningOperator (r' := r j) (hA' := hA j) (hT' := hT j)
      hU hL hE hG (hUR i) (hUR j) (hMul j) (hπ j) hKmax hrho (hμM i) (hμM j) (hβ i) (hβ j)
      (hW i j t) (hw i j t) (Mop i j t) (hMop i j t) x f g
  -- The elementary families of the ambient product span a dense subspace.
  let D₀ (i : I) : Set (Lp ℂ 2 (μh i)) := {f | ∃ v, A₂ i v ∧
    ⇑f =ᵐ[μh i] inducedRestriction K (p i) (l i) v}
  let D (i : I) : Set (Hs i) := {h | (h : Lp ℂ 2 (μh i)) ∈ D₀ i}
  let Q (i : I) : Set (Lp (Hs i) 2 (μs i)) := {f | ∃ (c : Xs i → ℂ) (h : Hs i),
    h ∈ D i ∧ HasCompactSupport c ∧ ContDiff ℝ (⊤ : ℕ∞) c ∧ f =ᵐ[μs i] fun x => c x • h}
  have hQ (i : I) : (Submodule.span ℂ (Q i)).topologicalClosure = ⊤ := by
    let _ : IsFiniteMeasureOnCompacts (μs i) := isFiniteMeasureOnCompacts_smul_spectralMeasure (n i) (hnP i)
    have hD : (Submodule.span ℂ (D i)).topologicalClosure = ⊤ :=
      Langlands.Analysis.Submodule.topologicalClosure_span_subtype_eq_top (D₀ i)
    exact Langlands.Analysis.topologicalClosure_span_smooth_smul_eq_top («μ» := μs i) (by norm_num) (D i) hD
  let _ (i : I) : CompleteSpace (Hs i) :=
    (Submodule.isClosed_topologicalClosure (Submodule.span ℂ (D₀ i))).completeSpace_coe
  let Xprod := spectralFamilySpace hK rho hsmooth hcalc iU l μM n e β nP
  let _ : CompleteSpace Xprod := by
    change CompleteSpace (PiLp 2 fun i => Lp (Hs i) 2 (μs i))
    infer_instance
  let Gen : Set Xprod := {g | ∃ i, ∃ f ∈ Q i, g = PiLp.single 2 i f}
  have hGen : (Submodule.span ℂ Gen).topologicalClosure = ⊤ :=
    Langlands.Analysis.PiLp.topologicalClosure_span_single_eq_top Q hQ
  let L : Submodule ℂ Xprod := symmetricFamilySpace hK rho hsmooth hcalc iU l μM n e β nP T cw π hw Mop
  let Smooth : Set L := {Ψ | ∃ k v c, IsSmoothCompactFamily hK rho hsmooth hcalc iU l μM n e β nP k v c Ψ.1}
  change (Submodule.span ℂ Smooth).topologicalClosure = ⊤
  refine Langlands.Analysis.Submodule.topologicalClosure_span_eq_top_of_subset_closure L Smooth ?_
  rw [← Submodule.topologicalClosure_coe]
  refine Langlands.Analysis.subset_topologicalClosure_span_of_inner_eq L (Subtype.val '' Smooth)
    (by rintro _ ⟨Ψ, _, rfl⟩; exact Ψ.2) Gen hGen ?_
  rintro _ ⟨i₀, f, ⟨c, h, ⟨v, hv, hh⟩, hcc, hc, hf⟩, rfl⟩
  have hex (j : I) := exists_smooth_symmetrized_component Mop hMop τ hE hG hUR hMul hπ hKmax
    hrho hW hL' i₀ j (hnP j) hv h hh hc hcc
  choose hG₁ k v' c' hkv hkc hAE using hex
  let Ψ : Xprod := WithLp.toLp 2 fun j => ∑ t, (nP i₀ : ℂ)⁻¹ • (hG₁ j t).toLp _
  have hcomp (i j : I) (t : T i j) : ∃ φ : T i₀ i ≃ T i₀ j,
      (∀ s y, (τm i₀ j (φ s)).symm (τm i j t y) = (τm i₀ i s).symm y) ∧
      ∀ s x, Mop i₀ j (φ s) x h = Mop i j t (τm i₀ i s x) (Mop i₀ i s x h) := by
    obtain ⟨φ, hφ⟩ := exists_equiv_postcomp hπ T w cw hW hinj hsurj i₀ t
    refine ⟨φ, ?_, ?_⟩
    · intro s y
      change (τ i₀ j (φ s)).symm (τ i j t y) = (τ i₀ i s).symm y
      have hreal := realWeylParameter_eq_comp_of_weylParameter <| (hφ s).trans
        (weylParameter_comp (l i₀) (cw i₀ i s) (π i) (l i) (cw i j t) (π j) (hπ i)).symm
      have hco (x : Xs i₀) : τ i₀ j (φ s) x = τ i j t (τ i₀ i s x) := by
        rw [hτ i₀ j (φ s), hreal, LinearMap.comp_apply, hτ i j t, hτ i₀ i s,
          LinearEquiv.apply_symm_apply]
      apply (τ i₀ j (φ s)).injective
      rw [ContinuousLinearEquiv.apply_symm_apply, hco, ContinuousLinearEquiv.apply_symm_apply]
    · intro s x
      change Mop i₀ j (φ s) x h = Mop i j t (τ i₀ i s x) (Mop i₀ i s x h)
      rw [hτ i₀ i s]
      exact map_comp_of_isImaginaryIntertwiningOperator (r := r i₀) (r' := r i) (r'' := r j)
        (hA := hA i₀) (hT := hT i₀) (hA' := hA i) (hT' := hT i) (hA'' := hA j) (hT'' := hT j)
        hE hC hI hL hG (hUR i₀) (hUR i) (hUR j) (hMul i₀) (hMul i) (hMul j) (hπ i) (hπ j) hKmax hrho (hμM i) (hμM j) (hβ i) (hβ j)
        (hW i₀ i s) (hW i j t) (hW i₀ j (φ s)) (hφ s) (Mop i₀ i s) (hMop i₀ i s) (Mop i j t)
        (hMop i j t) (Mop i₀ j (φ s)) (hMop i₀ j (φ s)) hv h hh x
  have hΨ : Ψ ∈ L := by
    intro i j t
    have hsym := symmetrized_ae_symm (X := Xs) (Hs := Hs) ν nP τm Mop hτm i₀ c h (nP i₀ : ℂ)⁻¹
      hG₁ hcomp i j t
    change ∀ᵐ x ∂(ν i), Ψ j ((e j).symm (realWeylParameter (l i) (cw i j t) (π j) (e i x))) =
      Mop i j t x (Ψ i x)
    simp only [← hτ i j t, Ψ]
    exact hsym
  have hΨsmooth : (⟨Ψ, hΨ⟩ : L) ∈ Smooth := ⟨k, v', c', hkv, hkc, hAE⟩
  refine ⟨Ψ, Submodule.subset_span ⟨⟨Ψ, hΨ⟩, hΨsmooth, rfl⟩, ?_⟩
  intro Θ hΘ
  have hΘ' (i j : I) (t : T i j) : ∀ᵐ x ∂(ν i), Θ j (τm i j t x) = Mop i j t x (Θ i x) := by
    change ∀ᵐ x ∂(ν i), Θ j (τ i j t x) = Mop i j t x (Θ i x)
    simp only [hτ i j t]
    exact hΘ i j t
  exact inner_symmetrized_eq (X := Xs) (Hs := Hs) ν nP τm Mop hτm hiso i₀
    (sum_card_row_div_eq_one hπ T w cw hW hinj hsurj i₀) Θ hΘ' c h hG₁ f hf

end Langlands.Global

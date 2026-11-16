import Langlands.Representation.Archimedean.PrincipalSeriesGKModule

/-!
# Families of functions in a finite-dimensional space of functions

Let `U` be a finite-dimensional space of complex functions on a set `X`. Every linear functional
on `U` is a finite linear combination of point evaluations (`exists_eval_sum`), so every element
of `U` is `∑ᵢ cᵢ(u) bᵢ` with fixed `bᵢ ∈ U` and coefficients `cᵢ(u)` that are finite linear
combinations of values of `u` (`exists_decomposition`).

Consequently, for a family `w k ∈ U`, the pointwise integral `x ↦ ∫ w k x dμ` lies in `U`
(`integral_mem`), and so does a pointwise derivative (`hasDerivAt_mem`); a linear map defined on
a space containing `U` commutes with both (`map_integral`, `map_hasDerivAt`).
-/

noncomputable section

open MeasureTheory

set_option autoImplicit false

namespace Langlands.Archimedean

namespace InductionStages

universe uX uY uK

variable {X : Type uX} {Y : Type uY}

/-- Every linear functional on a finite-dimensional space of functions is a finite linear
combination of point evaluations. -/
theorem exists_eval_sum (U : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ U] (ℓ : U →ₗ[ℂ] ℂ) :
    ∃ (m : ℕ) (p : Fin m → X) (c : Fin m → ℂ),
      ∀ u : U, ℓ u = ∑ i, c i * (u : X → ℂ) (p i) := by
  obtain ⟨m, p, c, h⟩ := exists_sum_of_separating
    (fun x => (LinearMap.proj x).comp U.subtype) (⊤ : Submodule ℂ U)
    (fun s _ hs => Subtype.ext (funext hs)) ℓ
  exact ⟨m, p, c, fun u => h u Submodule.mem_top⟩

/-- Every element `u` of a finite-dimensional space of functions `U` is `∑ᵢ cᵢ(u) bᵢ` with
`bᵢ ∈ U` and coefficients `cᵢ(u) = ∑ₗ aᵢₗ u(pᵢₗ)`. -/
theorem exists_decomposition (U : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ U] :
    ∃ (d : ℕ) (b : Fin d → X → ℂ) (m : Fin d → ℕ) (p : ∀ i, Fin (m i) → X)
      (a : ∀ i, Fin (m i) → ℂ), (∀ i, b i ∈ U) ∧
        ∀ u ∈ U, u = ∑ i, (∑ l, a i l * u (p i l)) • b i := by
  let B := Module.finBasis ℂ U
  have h := fun i => exists_eval_sum U (B.coord i)
  choose m p a ha using h
  refine ⟨_, fun i => (B i : X → ℂ), m, p, a, fun i => (B i).2, fun u hu => ?_⟩
  have hsum := B.sum_repr ⟨u, hu⟩
  have hval := congrArg (fun v : U => (v : X → ℂ)) hsum
  simp only [Submodule.coe_sum, Submodule.coe_smul] at hval
  conv_lhs => rw [← hval]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [← ha i ⟨u, hu⟩]
  rfl

section Integral

variable {K : Type uK} [MeasurableSpace K] (μ : Measure K)

/-- The pointwise integral of a family of functions in a finite-dimensional space `U` lies in
`U`. -/
theorem integral_mem (U : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ U] {w : K → X → ℂ}
    (hw : ∀ k, w k ∈ U) (hi : ∀ x, Integrable (fun k => w k x) μ) :
    (fun x => ∫ k, w k x ∂μ) ∈ U := by
  obtain ⟨d, b, m, p, a, hb, hdec⟩ := exists_decomposition U
  have hpt : ∀ k x, w k x = ∑ i, (∑ l, a i l * w k (p i l)) * b i x := fun k x => by
    conv_lhs => rw [hdec (w k) (hw k)]
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hint : ∀ i, Integrable (fun k => ∑ l, a i l * w k (p i l)) μ := fun i =>
    integrable_finsetSum _ fun l _ => (hi _).const_mul _
  have key : (fun x => ∫ k, w k x ∂μ) = ∑ i, (∫ k, ∑ l, a i l * w k (p i l) ∂μ) • b i := by
    funext x
    simp_rw [hpt _ x]
    rw [integral_finsetSum _ fun i _ => (hint i).mul_const _]
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, integral_mul_const]
  rw [key]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hb i)

variable {V : Submodule ℂ (X → ℂ)} {W : Submodule ℂ (Y → ℂ)}

/-- Values of a linear map on a finite-dimensional space `U ≤ V` of functions are finite linear
combinations of point values. -/
theorem exists_map_eval_sum (L : V →ₗ[ℂ] W) (U : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ U]
    (hUV : U ≤ V) (y : Y) :
    ∃ (m : ℕ) (p : Fin m → X) (c : Fin m → ℂ),
      ∀ u (hu : u ∈ U), (L ⟨u, hUV hu⟩ : Y → ℂ) y = ∑ i, c i * u (p i) := by
  obtain ⟨m, p, c, h⟩ := exists_eval_sum U
    ((LinearMap.proj y).comp (W.subtype.comp (L.comp (Submodule.inclusion hUV))))
  exact ⟨m, p, c, fun u hu => h ⟨u, hu⟩⟩

/-- The `y`-values of the image of a pointwise integrable family under a linear map are
integrable. -/
theorem integrable_map (L : V →ₗ[ℂ] W) (U : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ U]
    (hUV : U ≤ V) {w : K → X → ℂ} (hw : ∀ k, w k ∈ U) (hi : ∀ x, Integrable (fun k => w k x) μ)
    (y : Y) : Integrable (fun k => (L ⟨w k, hUV (hw k)⟩ : Y → ℂ) y) μ := by
  obtain ⟨m, p, c, h⟩ := exists_map_eval_sum L U hUV y
  simp_rw [fun k => h (w k) (hw k)]
  exact integrable_finsetSum _ fun i _ => (hi _).const_mul _

/-- A linear map defined on a space containing `U` commutes with pointwise integrals of
families in `U`. -/
theorem map_integral (L : V →ₗ[ℂ] W) (U : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ U]
    (hUV : U ≤ V) {w : K → X → ℂ} (hw : ∀ k, w k ∈ U) (hi : ∀ x, Integrable (fun k => w k x) μ)
    (y : Y) :
    (L ⟨fun x => ∫ k, w k x ∂μ, hUV (integral_mem μ U hw hi)⟩ : Y → ℂ) y =
      ∫ k, (L ⟨w k, hUV (hw k)⟩ : Y → ℂ) y ∂μ := by
  obtain ⟨m, p, c, h⟩ := exists_map_eval_sum L U hUV y
  rw [h _ (integral_mem μ U hw hi)]
  simp_rw [fun k => h (w k) (hw k)]
  rw [integral_finsetSum _ fun i _ => (hi _).const_mul _]
  simp [integral_const_mul]

end Integral

section Continuity

variable {K : Type uK} [TopologicalSpace K] {V : Submodule ℂ (X → ℂ)} {W : Submodule ℂ (Y → ℂ)}

/-- The `y`-values of the image of a pointwise continuous family under a linear map are
continuous. -/
theorem continuous_map (L : V →ₗ[ℂ] W) (U : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ U]
    (hUV : U ≤ V) {w : K → X → ℂ} (hw : ∀ k, w k ∈ U) (hc : ∀ x, Continuous fun k => w k x)
    (y : Y) : Continuous fun k => (L ⟨w k, hUV (hw k)⟩ : Y → ℂ) y := by
  obtain ⟨m, p, c, h⟩ := exists_map_eval_sum L U hUV y
  simp_rw [fun k => h (w k) (hw k)]
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (hc _)

end Continuity

section Derivative

variable {V : Submodule ℂ (X → ℂ)} {W : Submodule ℂ (Y → ℂ)}

/-- A pointwise derivative of a family of functions in a finite-dimensional space `U` lies in
`U`. -/
theorem hasDerivAt_mem (U : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ U] {w : ℝ → X → ℂ}
    (hw : ∀ t, w t ∈ U) {w' : X → ℂ} {t₀ : ℝ}
    (hd : ∀ x, HasDerivAt (fun t => w t x) (w' x) t₀) : w' ∈ U := by
  obtain ⟨d, b, m, p, a, hb, hdec⟩ := exists_decomposition U
  have hpt : ∀ t x, w t x = ∑ i, (∑ l, a i l * w t (p i l)) * b i x := fun t x => by
    conv_lhs => rw [hdec (w t) (hw t)]
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have key : w' = ∑ i, (∑ l, a i l * w' (p i l)) • b i := by
    funext x
    have h1 : HasDerivAt (fun t => w t x)
        (∑ i, (∑ l, a i l * w' (p i l)) * b i x) t₀ := by
      have h2 : HasDerivAt (fun t => ∑ i, (∑ l, a i l * w t (p i l)) * b i x)
          (∑ i, (∑ l, a i l * w' (p i l)) * b i x) t₀ :=
        HasDerivAt.fun_sum fun i _ =>
          (HasDerivAt.fun_sum fun l _ => (hd (p i l)).const_mul (a i l)).mul_const (b i x)
      exact h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hpt t x)
    rw [(hd x).unique h1]
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [key]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hb i)

/-- A linear map defined on a space containing `U` commutes with pointwise derivatives of
families in `U`. -/
theorem map_hasDerivAt (L : V →ₗ[ℂ] W) (U : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ U]
    (hUV : U ≤ V) {w : ℝ → X → ℂ} (hw : ∀ t, w t ∈ U) {w' : X → ℂ} {t₀ : ℝ}
    (hd : ∀ x, HasDerivAt (fun t => w t x) (w' x) t₀) (y : Y) :
    HasDerivAt (fun t => (L ⟨w t, hUV (hw t)⟩ : Y → ℂ) y)
      ((L ⟨w', hUV (hasDerivAt_mem U hw hd)⟩ : Y → ℂ) y) t₀ := by
  obtain ⟨m, p, c, h⟩ := exists_map_eval_sum L U hUV y
  rw [h _ (hasDerivAt_mem U hw hd)]
  simp_rw [fun t => h (w t) (hw t)]
  exact HasDerivAt.fun_sum fun i _ => (hd (p i)).const_mul (c i)

end Derivative

section Subspace

/-! ### Families in a finite-dimensional subspace of a space of functions

The same statements for families `w : K → V` of elements of a submodule `V` of `X → ℂ` taking
values in a finite-dimensional submodule `S` of `V`. -/

variable {K : Type uK} {V : Submodule ℂ (X → ℂ)} {W : Submodule ℂ (Y → ℂ)}

theorem coe_mem_map_subtype {S : Submodule ℂ V} {v : V} (hv : v ∈ S) :
    (v : X → ℂ) ∈ S.map V.subtype :=
  ⟨v, hv, rfl⟩

/-- If a family in `S ⊓ M` is pointwise integrable and `v` is its pointwise integral, then
`v ∈ M`. -/
theorem mem_of_integral [MeasurableSpace K] (μ : Measure K) (M S : Submodule ℂ V)
    [FiniteDimensional ℂ S] {w : K → V} (hw : ∀ k, w k ∈ S ⊓ M)
    (hi : ∀ x, Integrable (fun k => (w k : X → ℂ) x) μ) {v : V}
    (hv : ∀ x, (v : X → ℂ) x = ∫ k, (w k : X → ℂ) x ∂μ) : v ∈ M := by
  have h := integral_mem μ ((S ⊓ M).map V.subtype) (fun k => coe_mem_map_subtype (hw k)) hi
  have hv' : (fun x => ∫ k, (w k : X → ℂ) x ∂μ) = (v : X → ℂ) := funext fun x => (hv x).symm
  rw [hv'] at h
  obtain ⟨s, hs, hsv⟩ := h
  have hsv' : s = v := Subtype.ext hsv
  rw [← hsv']
  exact (Submodule.mem_inf.mp hs).2

/-- A linear map commutes with pointwise integrals of families in a finite-dimensional
subspace `S`. -/
theorem map_integral_of_mem [MeasurableSpace K] (μ : Measure K) (L : V →ₗ[ℂ] W)
    (S : Submodule ℂ V) [FiniteDimensional ℂ S] {w : K → V} (hw : ∀ k, w k ∈ S)
    (hi : ∀ x, Integrable (fun k => (w k : X → ℂ) x) μ) {v : V}
    (hv : ∀ x, (v : X → ℂ) x = ∫ k, (w k : X → ℂ) x ∂μ) (y : Y) :
    (L v : Y → ℂ) y = ∫ k, (L (w k) : Y → ℂ) y ∂μ := by
  have h := map_integral μ L (S.map V.subtype) (Submodule.map_subtype_le _ _)
    (fun k => coe_mem_map_subtype (hw k)) hi y
  have hv' : v = ⟨fun x => ∫ k, (w k : X → ℂ) x ∂μ,
      Submodule.map_subtype_le _ _ (integral_mem μ _ (fun k => coe_mem_map_subtype (hw k)) hi)⟩ :=
    Subtype.ext (funext hv)
  rw [hv', h]

/-- Pointwise continuity passes through a linear map for families in a finite-dimensional
subspace `S`. -/
theorem continuous_map_of_mem [TopologicalSpace K] (L : V →ₗ[ℂ] W) (S : Submodule ℂ V)
    [FiniteDimensional ℂ S] {w : K → V} (hw : ∀ k, w k ∈ S)
    (hc : ∀ x, Continuous fun k => (w k : X → ℂ) x) (y : Y) :
    Continuous fun k => (L (w k) : Y → ℂ) y :=
  continuous_map L (S.map V.subtype) (Submodule.map_subtype_le _ _)
    (fun k => coe_mem_map_subtype (hw k)) hc y

/-- A linear map commutes with pointwise derivatives of families in a finite-dimensional
subspace `S`. -/
theorem map_hasDerivAt_of_mem (L : V →ₗ[ℂ] W) (S : Submodule ℂ V) [FiniteDimensional ℂ S]
    {w : ℝ → V} (hw : ∀ t, w t ∈ S) {v : V} {t₀ : ℝ}
    (hd : ∀ x, HasDerivAt (fun t => (w t : X → ℂ) x) ((v : X → ℂ) x) t₀) (y : Y) :
    HasDerivAt (fun t => (L (w t) : Y → ℂ) y) ((L v : Y → ℂ) y) t₀ :=
  map_hasDerivAt L (S.map V.subtype) (Submodule.map_subtype_le _ _)
    (fun t => coe_mem_map_subtype (hw t)) hd y

/-- A pointwise derivative of a family in a finite-dimensional subspace `S` lies in `S`. -/
theorem hasDerivAt_mem_of_mem (S : Submodule ℂ V) [FiniteDimensional ℂ S] {w : ℝ → V}
    (hw : ∀ t, w t ∈ S) {v : V} {t₀ : ℝ}
    (hd : ∀ x, HasDerivAt (fun t => (w t : X → ℂ) x) ((v : X → ℂ) x) t₀) : v ∈ S := by
  obtain ⟨s, hs, hsv⟩ := hasDerivAt_mem (S.map V.subtype) (fun t => coe_mem_map_subtype (hw t)) hd
  have hsv' : s = v := Subtype.ext hsv
  rwa [← hsv']

end Subspace

section Joint

variable {K : Type uK} [TopologicalSpace K] [TopologicalSpace X]

/-- A family in a finite-dimensional space of continuous functions that is pointwise
continuous in the parameter is jointly continuous. -/
theorem continuous_uncurry_of_mem (U : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ U]
    (hU : ∀ u ∈ U, Continuous u) {w : K → X → ℂ} (hw : ∀ k, w k ∈ U)
    (hc : ∀ x, Continuous fun k => w k x) : Continuous fun p : K × X => w p.1 p.2 := by
  obtain ⟨d, b, m, p, a, hb, hdec⟩ := exists_decomposition U
  have hpt : (fun q : K × X => w q.1 q.2) =
      fun q => ∑ i, (∑ l, a i l * w q.1 (p i l)) * b i q.2 := funext fun q => by
    conv_lhs => rw [hdec (w q.1) (hw q.1)]
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hpt]
  exact continuous_finsetSum _ fun i _ =>
    (continuous_finsetSum _ fun l _ => continuous_const.mul ((hc _).comp continuous_fst)).mul
      ((hU _ (hb i)).comp continuous_snd)

end Joint

end InductionStages

end Langlands.Archimedean

import Langlands.Geometry.Analytic.DrinfeldBuildingCovering
import Langlands.Geometry.Analytic.InvariantAnalyticDomains

/-! # Harris's domains `U(f)` are open, and the action of their stabilizers -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Filter Topology CategoryTheory
open scoped ENNReal

/-! ## Continuity of ultrametric norms on `F^n` -/

namespace VectorNorm

variable {F : Type v} [NormedField F]

section

variable {V : Type w} [AddCommGroup V] [Module F V] (ν : VectorNorm F V)

theorem apply_neg (a : V) : ν (-a) = ν a := by
  rw [← neg_one_smul F a, ν.map_smul, norm_neg, norm_one, one_mul]

theorem sub_le_apply_sub (a b : V) : ν a - ν b ≤ ν (a - b) := by
  have h := ν.add_le_max b (a - b)
  have hab : b + (a - b) = a := by abel
  rw [hab] at h
  have h1 := ν.nonneg b
  have h2 := ν.nonneg (a - b)
  rcases le_total (ν b) (ν (a - b)) with h' | h'
  · rw [max_eq_right h'] at h
    linarith
  · rw [max_eq_left h'] at h
    linarith

/-- `|ν a - ν b| ≤ ν (a - b)`. -/
theorem abs_sub_le (a b : V) : |ν a - ν b| ≤ ν (a - b) := by
  rw [abs_le]
  constructor
  · have h := ν.sub_le_apply_sub b a
    rw [← neg_sub a b, ν.apply_neg] at h
    linarith
  · exact ν.sub_le_apply_sub a b

theorem add_le_add (a b : V) : ν (a + b) ≤ ν a + ν b :=
  (ν.add_le_max a b).trans (max_le_add_of_nonneg (ν.nonneg a) (ν.nonneg b))

end

variable {n : ℕ} (ν : VectorNorm F (Fin n → F))

/-- An ultrametric norm on `F^n` is bounded by a multiple of the sup norm. -/
theorem le_mul_norm (a : Fin n → F) : ν a ≤ (∑ i, ν (Pi.single i 1)) * ‖a‖ := by
  have ha : ∑ i, a i • (Pi.single i (1 : F) : Fin n → F) = a := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  calc ν a = ν (∑ i, a i • (Pi.single i (1 : F) : Fin n → F)) := by rw [ha]
    _ ≤ ∑ i, ν (a i • (Pi.single i (1 : F) : Fin n → F)) :=
        Finset.le_sum_of_subadditive (fun x => ν x) ν.map_zero.le (fun x y => ν.add_le_add x y)
          _ _
    _ = ∑ i, ‖a i‖ * ν (Pi.single i 1) := Finset.sum_congr rfl fun i _ => ν.map_smul _ _
    _ ≤ ∑ i, ‖a‖ * ν (Pi.single i 1) := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (norm_le_pi_norm a i) (ν.nonneg _)
    _ = (∑ i, ν (Pi.single i 1)) * ‖a‖ := by rw [← Finset.mul_sum, mul_comm]

/-- An ultrametric norm on `F^n` is continuous for the product topology. -/
theorem continuous : Continuous (ν : (Fin n → F) → ℝ) := by
  have hC : 0 ≤ ∑ i, ν (Pi.single i 1) := Finset.sum_nonneg fun i _ => ν.nonneg _
  refine (LipschitzWith.of_dist_le_mul (K := ⟨_, hC⟩) fun a b => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm]
  exact (ν.abs_sub_le a b).trans (ν.le_mul_norm (a - b))

end VectorNorm

namespace DrinfeldUpperHalfSpace

open AnalyticAffineSpace

variable {F : Type v} [NontriviallyNormedField F]
  (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra F K] {d : ℕ}

/-! ## Continuity of the reduction data -/

/-- `(z, a) ↦ |ℓ_a(z)|` is jointly continuous on `Ω × F^{d+1}`. -/
theorem continuous_omegaNorm_apply :
    Continuous fun p : Omega F K d × (Fin (d + 1) → F) => omegaNorm K p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨z₀, a₀⟩
  obtain ⟨m, s, hs⟩ := exists_chart K d z₀.val
  have hnhds : range (chart K d (m + 1)) ∈ 𝓝 z₀.val := range_chart_mem_nhds K d ⟨s, hs⟩
  have hev : ∀ᶠ p : Omega F K d × (Fin (d + 1) → F) in 𝓝 (z₀, a₀),
      p.1.val ∈ range (chart K d (m + 1)) :=
    (continuous_subtype_val.comp continuous_fst).continuousAt.preimage_mem_nhds hnhds
  have hbound : ∀ᶠ p : Omega F K d × (Fin (d + 1) → F) in 𝓝 (z₀, a₀),
      ‖omegaNorm K p.1 p.2 - omegaNorm K p.1 a₀‖ ≤
        (d + 1) * radius K (m + 1) * ‖p.2 - a₀‖ := by
    filter_upwards [hev] with p hp
    obtain ⟨t, ht⟩ := hp
    rw [Real.norm_eq_abs]
    calc |omegaNorm K p.1 p.2 - omegaNorm K p.1 a₀| ≤ omegaNorm K p.1 (p.2 - a₀) :=
          (omegaNorm K p.1).abs_sub_le _ _
      _ = t (linearForm K d (m + 1) (coefficients F K d (p.2 - a₀))) := by
          rw [omegaNorm_apply, ← ht, linearNorm_chart]
      _ ≤ (d + 1) * ‖p.2 - a₀‖ * radius K (m + 1) :=
          linearForm_le K d (m + 1) t _ (norm_nonneg _) fun i => by
            rw [norm_algebraMap']
            exact norm_le_pi_norm (p.2 - a₀) i
      _ = (d + 1) * radius K (m + 1) * ‖p.2 - a₀‖ := by ring
  have h₁ : Tendsto (fun p : Omega F K d × (Fin (d + 1) → F) => omegaNorm K p.1 a₀)
      (𝓝 (z₀, a₀)) (𝓝 (omegaNorm K z₀ a₀)) :=
    ((continuous_linearNorm K d _).comp (continuous_subtype_val.comp continuous_fst)).tendsto _
  have hc : Continuous fun p : Omega F K d × (Fin (d + 1) → F) =>
      (d + 1) * radius K (m + 1) * ‖p.2 - a₀‖ :=
    continuous_const.mul (continuous_snd.sub continuous_const).norm
  have h₂ : Tendsto (fun p : Omega F K d × (Fin (d + 1) → F) =>
      (d + 1) * radius K (m + 1) * ‖p.2 - a₀‖) (𝓝 (z₀, a₀)) (𝓝 0) := by
    simpa using hc.tendsto (z₀, a₀)
  have h₃ := h₁.add (squeeze_zero_norm' hbound h₂)
  exact (by simpa using h₃ : Tendsto (fun p : Omega F K d × (Fin (d + 1) → F) =>
    omegaNorm K p.1 p.2) (𝓝 (z₀, a₀)) (𝓝 (omegaNorm K z₀ a₀)))

theorem IsFacet.finite {S : Set (NormClass F (Fin (d + 1) → F))} (hS : NormClass.IsFacet S) :
    S.Finite := by
  obtain ⟨k, ν, -, rfl⟩ := hS
  exact finite_range _

variable {K}

theorem one_mem_shell {c : F} (hc : 1 < ‖c‖) : (fun _ => (1 : F)) ∈ shell F d c := by
  refine ⟨mem_closedBall_zero_iff.2 ((pi_norm_const (1 : F)).trans_le norm_one.le), fun h => ?_⟩
  rw [mem_ball_zero_iff, pi_norm_const, norm_one] at h
  exact absurd h (not_lt.2 (inv_le_one_of_one_le₀ hc.le))

theorem ratio_smul (ν μ : VectorNorm F (Fin (d + 1) → F)) {t : F} (ht : t ≠ 0)
    (x : Fin (d + 1) → F) : ν (t • x) / μ (t • x) = ν x / μ x := by
  rw [ν.map_smul, μ.map_smul, mul_div_mul_left _ _ (norm_ne_zero_iff.2 ht)]

/-- The supremum of `ν / μ` over all nonzero vectors is its maximum over a compact shell. -/
theorem ratioSup_eq_sSup {c : F} (hc : 1 < ‖c‖) [ProperSpace F]
    (ν μ : VectorNorm F (Fin (d + 1) → F)) :
    VectorNorm.ratioSup ν μ =
      ENNReal.ofReal (sSup (range fun a : shell F d c => ν a / μ a)) := by
  have hcont : Continuous fun a : shell F d c => ν a / μ a :=
    (ν.continuous.comp continuous_subtype_val).div (μ.continuous.comp continuous_subtype_val)
      fun a => (μ.pos (ne_zero_of_mem_shell F d hc a.2)).ne'
  have : CompactSpace (shell F d c) := isCompact_iff_compactSpace.mp (isCompact_shell F d c)
  have : Nonempty (shell F d c) := ⟨⟨_, one_mem_shell hc⟩⟩
  have hbdd : BddAbove (range fun a : shell F d c => ν a / μ a) :=
    (isCompact_range hcont).bddAbove
  obtain ⟨a₀, ha₀⟩ := (isCompact_range hcont).sSup_mem (range_nonempty _)
  unfold VectorNorm.ratioSup
  apply le_antisymm
  · refine iSup_le fun x => ?_
    by_cases hx : x = 0
    · rw [hx, VectorNorm.map_zero, zero_div, ENNReal.ofReal_zero]
      exact bot_le
    · obtain ⟨t, ht, hts⟩ := exists_smul_mem_shell F d hc hx
      rw [← ratio_smul ν μ ht x]
      exact ENNReal.ofReal_le_ofReal (le_csSup hbdd ⟨⟨t • x, hts⟩, rfl⟩)
  · calc ENNReal.ofReal (sSup (range fun a : shell F d c => ν a / μ a))
        = ENNReal.ofReal (ν a₀ / μ a₀) := by rw [← ha₀]
      _ ≤ ⨆ x, ENNReal.ofReal (ν x / μ x) :=
        le_iSup (fun x : Fin (d + 1) → F => ENNReal.ofReal (ν x / μ x)) a₀.val

variable [ProperSpace F]

/-- `z ↦ sup_{a ∈ shell} |ℓ_a(z)| / μ(a)` is continuous on `Ω`. -/
theorem continuous_sSup_omegaNorm_div {c : F} (hc : 1 < ‖c‖) (μ : VectorNorm F (Fin (d + 1) → F)) :
    Continuous fun z : Omega F K d =>
      sSup (range fun a : shell F d c => omegaNorm K z a / μ a) := by
  have : CompactSpace (shell F d c) := isCompact_iff_compactSpace.mp (isCompact_shell F d c)
  have h₁ : Continuous fun p : Omega F K d × shell F d c => μ p.2 :=
    μ.continuous.comp (continuous_subtype_val.comp continuous_snd)
  have h₂ : Continuous fun p : Omega F K d × shell F d c => omegaNorm K p.1 p.2 :=
    Continuous.comp (g := fun q : Omega F K d × (Fin (d + 1) → F) => omegaNorm K q.1 q.2)
      (f := fun p : Omega F K d × shell F d c => (p.1, (p.2 : Fin (d + 1) → F)))
      (continuous_omegaNorm_apply K)
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hf : Continuous fun p : Omega F K d × shell F d c => omegaNorm K p.1 p.2 / μ p.2 :=
    h₂.div h₁ fun p => (μ.pos (ne_zero_of_mem_shell F d hc p.2.2)).ne'
  have h := IsCompact.continuous_sSup
    (f := fun (z : Omega F K d) (a : shell F d c) => omegaNorm K z a / μ a) isCompact_univ hf
  simpa only [image_univ] using h

/-- `z ↦ sup_{a ∈ shell} μ(a) / |ℓ_a(z)|` is continuous on `Ω`. -/
theorem continuous_sSup_div_omegaNorm {c : F} (hc : 1 < ‖c‖) (μ : VectorNorm F (Fin (d + 1) → F)) :
    Continuous fun z : Omega F K d =>
      sSup (range fun a : shell F d c => μ a / omegaNorm K z a) := by
  have : CompactSpace (shell F d c) := isCompact_iff_compactSpace.mp (isCompact_shell F d c)
  have h₁ : Continuous fun p : Omega F K d × shell F d c => μ p.2 :=
    μ.continuous.comp (continuous_subtype_val.comp continuous_snd)
  have h₂ : Continuous fun p : Omega F K d × shell F d c => omegaNorm K p.1 p.2 :=
    Continuous.comp (g := fun q : Omega F K d × (Fin (d + 1) → F) => omegaNorm K q.1 q.2)
      (f := fun p : Omega F K d × shell F d c => (p.1, (p.2 : Fin (d + 1) → F)))
      (continuous_omegaNorm_apply K)
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hf : Continuous fun p : Omega F K d × shell F d c => μ p.2 / omegaNorm K p.1 p.2 :=
    h₁.div h₂ fun p => ((omegaNorm K p.1).pos (ne_zero_of_mem_shell F d hc p.2.2)).ne'
  have h := IsCompact.continuous_sSup
    (f := fun (z : Omega F K d) (a : shell F d c) => μ a / omegaNorm K z a) isCompact_univ hf
  simpa only [image_univ] using h

/-- For a fixed point `y` of the building, `{z ∈ Ω | d(Res z, y) < r}` is open. -/
theorem isOpen_setOf_distRatio_reduction_lt (y : NormClass F (Fin (d + 1) → F)) {r : ℝ}
    (hr : 0 < r) :
    IsOpen {z : Omega F K d | NormClass.distRatio (reduction K z) y < ENNReal.ofReal r} := by
  obtain ⟨μ, rfl⟩ := Quotient.exists_rep y
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm F
  have heq : ∀ z : Omega F K d, NormClass.distRatio (reduction K z) ⟦μ⟧ =
      ENNReal.ofReal (sSup (range fun a : shell F d c => omegaNorm K z a / μ a) *
        sSup (range fun a : shell F d c => μ a / omegaNorm K z a)) := fun z => by
    have h0 : 0 ≤ sSup (range fun a : shell F d c => omegaNorm K z a / μ a) :=
      Real.sSup_nonneg fun _ ⟨a, ha⟩ => ha ▸ div_nonneg ((omegaNorm K z).nonneg _) (μ.nonneg _)
    rw [reduction, NormClass.distRatio_mk, VectorNorm.distRatio, ratioSup_eq_sSup hc,
      ratioSup_eq_sSup hc, ENNReal.ofReal_mul h0]
  have hset : {z : Omega F K d | NormClass.distRatio (reduction K z) ⟦μ⟧ < ENNReal.ofReal r} =
      (fun z : Omega F K d => sSup (range fun a : shell F d c => omegaNorm K z a / μ a) *
        sSup (range fun a : shell F d c => μ a / omegaNorm K z a)) ⁻¹' Iio r := by
    ext z
    rw [mem_ofPred_eq, heq, ENNReal.ofReal_lt_ofReal_iff hr]
    rfl
  rw [hset]
  exact isOpen_Iio.preimage
    ((continuous_sSup_omegaNorm_div hc μ).mul (continuous_sSup_div_omegaNorm hc μ))

/-- The preimage under `Res` of Harris's `B(e, ε)` is open. -/
theorem isOpen_reduction_preimage_vertexNbhd (e : NormClass F (Fin (d + 1) → F)) (ε : ℝ) :
    IsOpen (reduction K ⁻¹' NormClass.vertexNbhd e ε) := by
  have h : reduction K ⁻¹' NormClass.vertexNbhd e ε =
      ⋃ y ∈ NormClass.vertexStar e, {z : Omega F K d |
        NormClass.distRatio (reduction K z) y < ENNReal.ofReal (Real.exp ε)} := by
    ext z
    simp only [mem_preimage, NormClass.vertexNbhd, mem_ofPred_eq, mem_iUnion, exists_prop]
  rw [h]
  exact isOpen_biUnion fun y _ => isOpen_setOf_distRatio_reduction_lt y (Real.exp_pos ε)

/-- Harris's `U(f) = Res⁻¹(B(f, ε))` is open for every finite set of vertices `f`, in
particular for every facet. -/
theorem isOpen_facetDomain {S : Set (NormClass F (Fin (d + 1) → F))} (hS : S.Finite) (ε : ℝ) :
    IsOpen (facetDomain K S ε) := by
  rw [facetDomain, NormClass.facetNbhd, preimage_iInter₂]
  exact hS.isOpen_biInter fun e _ => isOpen_reduction_preimage_vertexNbhd e ε

/-! ## The action of the stabilizer on `U(f)` -/

section FacetActions

variable (K) [NeZero d]

/-- Harris's `U(f)`, for a finite set of vertices `f`, as an analytic domain of `Ω`: an open
subset. -/
def facetAnalyticDomain {S : Set (NormClass F (Fin (d + 1) → F))} (hS : S.Finite) (ε : ℝ) :
    (SaturatedAtlasPresentation.presentationOf (omegaAction F K d).V).AnalyticDomain :=
  SaturatedAtlasPresentation.openDomain _ (facetDomain K S ε) (isOpen_facetDomain hS ε)

@[simp]
theorem facetAnalyticDomain_carrier {S : Set (NormClass F (Fin (d + 1) → F))} (hS : S.Finite)
    (ε : ℝ) : (facetAnalyticDomain K hS ε).carrier = facetDomain K S ε :=
  rfl

/-- Every subgroup `H` of the stabilizer `S(f)` maps `U(f)` into itself. -/
theorem isInvariantDomain_facetAnalyticDomain {S : Set (NormClass F (Fin (d + 1) → F))}
    (hS : S.Finite) (ε : ℝ) (H : Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F))
    (hH : H ≤ facetStabilizer S) :
    SaturatedAtlasPresentation.IsInvariantDomain
      ((Action.res _ H.subtype).obj (omegaAction F K d)) (facetAnalyticDomain K hS ε) := by
  intro g x hx
  have hg : SaturatedAtlasPresentation.localizedSpaceFunctor.map
      ((omegaAction F K d).ρ (g : Matrix.GeneralLinearGroup (Fin (d + 1)) F)) x =
        actionMap K (g : Matrix.GeneralLinearGroup (Fin (d + 1)) F) x := by
    rw [localizedSpaceFunctor_map_omegaAction]
    rfl
  exact (congrArg (· ∈ facetDomain K S ε) hg).mpr
    ((actionMap_mem_facetDomain_of_mem_stabilizer K (hH g.2) ε x).2 hx)

/-- The action of a subgroup `H` of the stabilizer `S(f)` on Harris's `U(f)`: the restriction
of the action of `GL_{d+1}(F)` on `Ω`. -/
def facetAction {S : Set (NormClass F (Fin (d + 1) → F))} (hS : S.Finite) (ε : ℝ)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F)) (hH : H ≤ facetStabilizer S) :
    Action (SaturatedAtlasPresentation.LocalizedCategory.{u, u, u} (K := K)) H :=
  SaturatedAtlasPresentation.invariantDomainAction
    ((Action.res _ H.subtype).obj (omegaAction F K d)) (facetAnalyticDomain K hS ε)
    (isInvariantDomain_facetAnalyticDomain K hS ε H hH)

/-- The inclusion `U(f) → Ω` is `H`-equivariant. -/
def facetInclusion {S : Set (NormClass F (Fin (d + 1) → F))} (hS : S.Finite) (ε : ℝ)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F)) (hH : H ≤ facetStabilizer S) :
    facetAction K hS ε H hH ⟶ (Action.res _ H.subtype).obj (omegaAction F K d) :=
  SaturatedAtlasPresentation.invariantDomainInclusion
    ((Action.res _ H.subtype).obj (omegaAction F K d)) (facetAnalyticDomain K hS ε)
    (isInvariantDomain_facetAnalyticDomain K hS ε H hH)

/-- The underlying map of the inclusion `U(f) → Ω` is the inclusion of the subset. -/
theorem localizedSpaceFunctor_map_facetInclusion {S : Set (NormClass F (Fin (d + 1) → F))}
    (hS : S.Finite) (ε : ℝ) (H : Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F))
    (hH : H ≤ facetStabilizer S)
    (x : SaturatedAtlasPresentation.localizedSpaceFunctor.obj (facetAction K hS ε H hH).V) :
    SaturatedAtlasPresentation.localizedSpaceFunctor.map (facetInclusion K hS ε H hH).hom x =
      Subtype.val (p := (· ∈ facetDomain K S ε)) x :=
  SaturatedAtlasPresentation.domainι_apply (X := (omegaAction F K d).V)
    (facetAnalyticDomain K hS ε) x

/-- The action of the full stabilizer `S(f)` of a facet `f` on `U(f)`. -/
abbrev facetStabilizerAction {S : Set (NormClass F (Fin (d + 1) → F))} (hS : NormClass.IsFacet S)
    (ε : ℝ) : Action (SaturatedAtlasPresentation.LocalizedCategory.{u, u, u} (K := K))
      (facetStabilizer S) :=
  facetAction K (IsFacet.finite hS) ε (facetStabilizer S) le_rfl

end FacetActions

end DrinfeldUpperHalfSpace

end Langlands.Analytic

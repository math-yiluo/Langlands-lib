import Langlands.Global.AdelicSpectralTransformInputs
import Langlands.Global.AdelicHaarUnimodularityProof

/-! # Reduction of the unitary spectral transform to its inputs -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct Filter Topology
open scoped CategoryTheory.MonObj TensorProduct ENNReal

set_option autoImplicit false

namespace Langlands.Global

section Hilbert

variable {S V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A family `W s` in a Hilbert space with the Gram matrix of a family `φ s` spanning a dense
subspace of `V` is the image of `φ` under a linear isometry `V → H`. -/
theorem exists_linearIsometry_of_inner_eq [CompleteSpace H] (φ : S → V) (W : S → H)
    (hW : ∀ s s', inner ℂ (W s) (W s') = inner ℂ (φ s) (φ s'))
    (hd : (Submodule.span ℂ (Set.range φ)).topologicalClosure = ⊤) :
    ∃ Ebar : V →ₗᵢ[ℂ] H, ∀ s, Ebar (φ s) = W s := by
  classical
  let eφ : (S →₀ ℂ) →ₗ[ℂ] V := Finsupp.linearCombination ℂ φ
  let fW : (S →₀ ℂ) →ₗ[ℂ] H := Finsupp.linearCombination ℂ W
  have hinner : ∀ a b : S →₀ ℂ, inner ℂ (fW a) (fW b) = inner ℂ (eφ a) (eφ b) := by
    intro a b
    simp only [fW, eφ, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, hW]
  have hnorm : ∀ a, ‖fW a‖ = ‖eφ a‖ := by
    intro a
    rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hinner]
  have hdense : DenseRange eφ := by
    have h := (Submodule.dense_iff_topologicalClosure_eq_top
      (s := LinearMap.range eφ)).2 (by rw [Finsupp.range_linearCombination]; exact hd)
    simpa [DenseRange, LinearMap.coe_range] using h
  refine ⟨fW.extendOfIsometry hdense hnorm, fun s => ?_⟩
  have h1 : eφ (Finsupp.single s 1) = φ s := by simp [eφ]
  have h2 : fW (Finsupp.single s 1) = W s := by simp [fW]
  rw [← h1, LinearMap.extendOfIsometry_eq, h2]

/-- The range of a linear isometry out of a complete space is closed. -/
theorem isClosed_range_linearIsometry [CompleteSpace V] (Ebar : V →ₗᵢ[ℂ] H) :
    IsClosed (LinearMap.range Ebar.toLinearMap : Set H) := by
  rw [LinearMap.coe_range]
  exact Ebar.isometry.isUniformInducing.isComplete_range.isClosed

/-- If a bounded operator `R` maps each `Ebar (φ s)` into the closure of the range of `Ebar`
and the `φ s` span a dense subspace, then `R` preserves the range of `Ebar`, provided that
range is closed. -/
theorem range_invariant_of_generators (φ : S → V) (Ebar : V →ₗᵢ[ℂ] H)
    (hd : (Submodule.span ℂ (Set.range φ)).topologicalClosure = ⊤)
    (hc : IsClosed (LinearMap.range Ebar.toLinearMap : Set H)) (R : H →L[ℂ] H)
    (hR : ∀ s, R (Ebar (φ s)) ∈ closure (LinearMap.range Ebar.toLinearMap : Set H)) :
    ∀ f ∈ LinearMap.range Ebar.toLinearMap, R f ∈ LinearMap.range Ebar.toLinearMap := by
  rintro f ⟨x, rfl⟩
  let Q : Submodule ℂ V :=
    ((LinearMap.range Ebar.toLinearMap).comap (R : H →ₗ[ℂ] H)).comap Ebar.toLinearMap
  have hQ : IsClosed (Q : Set V) := by
    have : (Q : Set V) = (fun y => R (Ebar y)) ⁻¹' (LinearMap.range Ebar.toLinearMap : Set H) := by
      ext y; simp [Q]
    rw [this]
    exact hc.preimage (R.continuous.comp Ebar.continuous)
  have hspan : Submodule.span ℂ (Set.range φ) ≤ Q := by
    rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    have := hR s
    rw [hc.closure_eq] at this
    simpa [Q] using this
  have hx : x ∈ Q := by
    have := Submodule.topologicalClosure_minimal _ hspan hQ
    rw [hd] at this
    exact this Submodule.mem_top
  simpa [Q] using hx

end Hilbert

section Intertwined

variable {α β E E' : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {ma ma1 : Measure α} {nb : Measure β} {τ : α → β} {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- The pairs `(f, f')` with `f'(τ x) = A x (f x)` for almost every `x` form a closed set. -/
theorem isClosed_setOf_ae_intertwined (A : α → E →L[ℂ] E')
    (hτ : Tendsto τ (ae ma) (ae nb)) (h₁ : ae ma ≤ ae ma1) :
    IsClosed {fg : Lp E q ma1 × Lp E' q nb | ∀ᵐ x ∂ma, fg.2 (τ x) = A x (fg.1 x)} := by
  refine IsSeqClosed.isClosed fun {u} {g} hu hlim => ?_
  have h1 : Tendsto (fun k => (u k).1) atTop (𝓝 g.1) := (continuous_fst.tendsto g).comp hlim
  have h2 : Tendsto (fun k => (u k).2) atTop (𝓝 g.2) := (continuous_snd.tendsto g).comp hlim
  obtain ⟨ns, hns, hns1⟩ := (tendstoInMeasure_of_tendsto_Lp h1).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hms2⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (h2.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂ma, ∀ k, (u k).2 (τ x) = A x ((u k).1 x) := ae_all_iff.2 hu
  filter_upwards [hall, h₁ hns1, hτ.eventually hms2] with x hx hx1 hx2
  have hA : Tendsto (fun k => A x ((u (ns (ms k))).1 x)) atTop (𝓝 (A x (g.1 x))) :=
    ((A x).continuous.tendsto _).comp (hx1.comp hms.tendsto_atTop)
  have hB : Tendsto (fun k => A x ((u (ns (ms k))).1 x)) atTop (𝓝 (g.2 (τ x))) := by
    simp_rw [← hx]
    exact hx2
  exact tendsto_nhds_unique hB hA

end Intertwined

section IntertwinedFamily

variable {Z J : Type*} [TopologicalSpace Z] {T : J → J → Type*} {α : J → Type*}
  [∀ i, MeasurableSpace (α i)] {E : J → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℂ (E i)] {m m₀ : ∀ i, Measure (α i)} {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- Given continuous maps `ev i : Z → L^q(α i, m i; E i)`, the points `Φ` with
`(ev i' Φ)(τ i i' t x) = A i i' t x ((ev i Φ) x)` for `m₀ i`-almost every `x`, for all `i, i', t`,
form a closed set. -/
theorem isClosed_setOf_forall_ae_intertwined (ev : ∀ i, Z → Lp (E i) q (m i))
    (hev : ∀ i, Continuous (ev i)) (τ : ∀ i i', T i i' → α i → α i')
    (A : ∀ i i', T i i' → α i → E i →L[ℂ] E i')
    (hτ : ∀ i i' t, Tendsto (τ i i' t) (ae (m₀ i)) (ae (m i'))) (h₁ : ∀ i, ae (m₀ i) ≤ ae (m i)) :
    IsClosed {Φ : Z | ∀ i i' t, ∀ᵐ x ∂(m₀ i), ev i' Φ (τ i i' t x) = A i i' t x (ev i Φ x)} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun i' => isClosed_iInter fun t =>
    (isClosed_setOf_ae_intertwined (A i i' t) (hτ i i' t) (h₁ i)).preimage
      ((hev i).prodMk (hev i'))

end IntertwinedFamily

section Assembly

variable {V X Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [MeasurableSpace X] {m : Measure X}

/-- Hilbert space assembly of the spectral transform. Let `D` be a subset of a Hilbert space `V`
spanning a dense subspace, and `Rel Φ f` a relation between vectors and functions on `X` such
that every `Φ ∈ D` is related to some `f`, related functions are square integrable with the
Gram matrix of the related vectors, and for measure preserving maps `τ y` of `X`, each
`f ∘ τ y` with `Rel Φ f` is an `L²`-limit of related functions. Then there is a linear isometry
`Ē : V → L²(X, m)` with `Ē Φ = f` whenever `Rel Φ f`, whose range is closed and invariant under
`g ↦ g ∘ τ y`. -/
theorem exists_linearIsometry_of_wavePackets (D : Set V)
    (hd : (Submodule.span ℂ D).topologicalClosure = ⊤) (Rel : V → (X → ℂ) → Prop)
    (hex : ∀ Φ ∈ D, ∃ f, Rel Φ f)
    (hgram : ∀ Φ f Φ' f', Rel Φ f → Rel Φ' f' → MemLp f 2 m ∧
      ∫ x, (starRingEnd ℂ) (f x) * f' x ∂m = inner ℂ Φ Φ')
    (τ : Y → X → X) (hτ : ∀ y, MeasurePreserving (τ y) m m)
    (htrans : ∀ Φ f, Rel Φ f → ∀ y (ε : ℝ), 0 < ε → ∃ Φ' f', Rel Φ' f' ∧
      eLpNorm (fun x => f (τ y x) - f' x) 2 m < ENNReal.ofReal ε) :
    ∃ Ebar : V →ₗᵢ[ℂ] Lp ℂ 2 m, (∀ Φ f, Rel Φ f → ⇑(Ebar Φ) =ᵐ[m] f) ∧
      IsClosed (LinearMap.range Ebar.toLinearMap : Set (Lp ℂ 2 m)) ∧
      ∀ g ∈ LinearMap.range Ebar.toLinearMap, ∀ y, ∃ g' ∈ LinearMap.range Ebar.toLinearMap,
        g' =ᵐ[m] fun x => g (τ y x) := by
  have hmem : ∀ Φ f, Rel Φ f → MemLp f 2 m := fun Φ f h => (hgram Φ f Φ f h h).1
  let φ : {q : V × (X → ℂ) // Rel q.1 q.2} → V := fun s => s.1.1
  let W : {q : V × (X → ℂ) // Rel q.1 q.2} → Lp ℂ 2 m := fun s => (hmem _ _ s.2).toLp s.1.2
  have hW : ∀ s s', inner ℂ (W s) (W s') = inner ℂ (φ s) (φ s') := by
    intro s s'
    rw [← (hgram _ _ _ _ s.2 s'.2).2, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(hmem _ _ s.2).coeFn_toLp, (hmem _ _ s'.2).coeFn_toLp] with x hx hx'
    rw [hx, hx', RCLike.inner_apply']
  have hdense : (Submodule.span ℂ (Set.range φ)).topologicalClosure = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← hd]
    refine Submodule.topologicalClosure_mono (Submodule.span_mono ?_)
    intro Φ hΦ
    obtain ⟨f, hf⟩ := hex Φ hΦ
    exact ⟨⟨(Φ, f), hf⟩, rfl⟩
  obtain ⟨Ebar, hEbar⟩ := exists_linearIsometry_of_inner_eq φ W hW hdense
  have hform : ∀ Φ f, Rel Φ f → ⇑(Ebar Φ) =ᵐ[m] f := by
    intro Φ f h
    have h1 : Ebar Φ = W ⟨(Φ, f), h⟩ := hEbar ⟨(Φ, f), h⟩
    rw [h1]
    exact (hmem _ _ h).coeFn_toLp
  have hclosed := isClosed_range_linearIsometry Ebar
  refine ⟨Ebar, hform, hclosed, ?_⟩
  rintro g ⟨x, rfl⟩ y
  let R : Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m :=
    (Lp.compMeasurePreservingₗᵢ ℂ (τ y) (hτ y)).toContinuousLinearMap
  have hRf : ∀ g : Lp ℂ 2 m, ⇑(R g) =ᵐ[m] fun x => g (τ y x) := fun g =>
    Lp.coeFn_compMeasurePreserving g (hτ y)
  have hR : ∀ s, R (Ebar (φ s)) ∈
      closure (LinearMap.range Ebar.toLinearMap : Set (Lp ℂ 2 m)) := by
    rintro ⟨⟨Φ, f⟩, h⟩
    change R (Ebar Φ) ∈ _
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨Φ', f', h', hlt⟩ := htrans Φ f h y ε hε
    refine ⟨Ebar Φ', ⟨Φ', rfl⟩, ?_⟩
    rw [dist_eq_norm, Lp.norm_def]
    have heq : eLpNorm (⇑(R (Ebar Φ) - Ebar Φ')) 2 m =
        eLpNorm (fun x => f (τ y x) - f' x) 2 m := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (R (Ebar Φ)) (Ebar Φ'), hRf (Ebar Φ), hform Φ' f' h',
        (hτ y).quasiMeasurePreserving.ae_eq_comp (hform Φ f h)] with x h1 h2 h3 h4
      simp only [Function.comp_apply] at h4
      rw [h1, Pi.sub_apply, h2, h3, h4]
    rw [heq]
    exact ENNReal.toReal_lt_of_lt_ofReal hlt
  exact ⟨R (Ebar x), range_invariant_of_generators φ Ebar hdense hclosed R hR (Ebar x) ⟨x, rfl⟩,
    hRf (Ebar x)⟩

end Assembly

section AssemblySubmodule

variable {E X Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [MeasurableSpace X]
  {m : Measure X}

/-- `exists_linearIsometry_of_wavePackets` for a complete subspace `V` of an inner product space
`E`, with the Gram matrix computed in `E`. -/
theorem exists_linearIsometry_of_wavePackets_submodule (V : Submodule ℂ E) [CompleteSpace V]
    (D : Set V) (hd : (Submodule.span ℂ D).topologicalClosure = ⊤) (Rel : V → (X → ℂ) → Prop)
    (hex : ∀ Φ ∈ D, ∃ f, Rel Φ f)
    (hgram : ∀ Φ f Φ' f', Rel Φ f → Rel Φ' f' → MemLp f 2 m ∧
      ∫ x, (starRingEnd ℂ) (f x) * f' x ∂m = inner ℂ (Φ : E) Φ')
    (τ : Y → X → X) (hτ : ∀ y, MeasurePreserving (τ y) m m)
    (htrans : ∀ Φ f, Rel Φ f → ∀ y (ε : ℝ), 0 < ε → ∃ Φ' f', Rel Φ' f' ∧
      eLpNorm (fun x => f (τ y x) - f' x) 2 m < ENNReal.ofReal ε) :
    ∃ Ebar : V →ₗᵢ[ℂ] Lp ℂ 2 m, (∀ Φ f, Rel Φ f → ⇑(Ebar Φ) =ᵐ[m] f) ∧
      IsClosed (LinearMap.range Ebar.toLinearMap : Set (Lp ℂ 2 m)) ∧
      ∀ g ∈ LinearMap.range Ebar.toLinearMap, ∀ y, ∃ g' ∈ LinearMap.range Ebar.toLinearMap,
        g' =ᵐ[m] fun x => g (τ y x) :=
  exists_linearIsometry_of_wavePackets D hd Rel hex hgram τ hτ htrans

end AssemblySubmodule

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

section Families

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {I : Type} [Fintype I] {P M U : I → GroupScheme (Spec (CommRingCat.of F))}
  [∀ i, IsAffine (P i).X.left] [∀ i, LocallyOfFiniteType (P i).X.hom]
  [∀ i, IsAffine (M i).X.left] [∀ i, LocallyOfFiniteType (M i).X.hom]
  [∀ i, IsAffine (U i).X.left]
  {p : ∀ i, P i ⟶ G} [∀ i, IsClosedImmersion (p i).hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)}

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Fintype I] [∀ i, IsAffine (U i).X.left]
  [∀ i, IsClosedImmersion (p i).hom.hom.left] in
set_option synthInstance.maxHeartbeats 400000 in
/-- Arthur's space `L̂` is closed in the Hilbert space of families. -/
theorem isClosed_symmetricFamilySpace (hK : ∀ i, IsIwasawaCompact (p i) K) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (iU : ∀ i, U i ⟶ P i)
    (l : ∀ i, M i ⟶ P i) (μM : ∀ i, Measure (AdelicGroupPoints F (M i))) (n : I → ℕ)
    (e : ∀ i, (Fin (n i) → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (P i))
    (β : ∀ i, (Fin (n i) → ℝ) → ℝ) (nP : I → ℕ) (T : I → I → Type)
    (cw : ∀ i i', T i i' → (M i' ⟶ M i)) (π : ∀ i, P i ⟶ M i)
    (hw : ∀ i i' t, MeasurePreserving
      (fun x => (e i').symm (realWeylParameter (l i) (cw i i' t) (π i') (e i x)))
      volume volume)
    (Mop : ∀ i i', T i i' → (Fin (n i) → ℝ) →
      inducedHilbertSpace K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i) (μM i) (e i)
          (β i) →L[ℂ]
        inducedHilbertSpace K (hK i').isCompact rho hsmooth hcalc (p i') (iU i') (l i')
          (μM i') (e i') (β i')) :
    IsClosed (symmetricFamilySpace hK rho hsmooth hcalc iU l μM n e β nP T cw π hw Mop :
      Set (spectralFamilySpace hK rho hsmooth hcalc iU l μM n e β nP)) := by
  have hc : ∀ j, ((nP j : ℝ≥0∞))⁻¹ ≠ 0 := fun j =>
    ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)
  exact isClosed_setOf_forall_ae_intertwined
    (fun i (Φ : spectralFamilySpace hK rho hsmooth hcalc iU l μM n e β nP) => Φ i)
    (fun i => PiLp.continuous_apply 2 _ i)
    (fun i i' t x => (e i').symm (realWeylParameter (l i) (cw i i' t) (π i') (e i x))) Mop
    (fun i i' t => by
      rw [ae_spectralMeasure_eq, ae_smul_spectralMeasure_eq _ (hc i')]
      exact (hw i i' t).quasiMeasurePreserving.tendsto_ae)
    (fun i => by rw [ae_spectralMeasure_eq, ae_smul_spectralMeasure_eq _ (hc i)])

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Fintype I] [∀ i, IsAffine (U i).X.left]
  [∀ i, IsClosedImmersion (p i).hom.hom.left] in
set_option synthInstance.maxHeartbeats 400000 in
/-- Arthur's space `L̂` is complete. -/
theorem completeSpace_symmetricFamilySpace (hK : ∀ i, IsIwasawaCompact (p i) K) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (iU : ∀ i, U i ⟶ P i)
    (l : ∀ i, M i ⟶ P i) (μM : ∀ i, Measure (AdelicGroupPoints F (M i))) (n : I → ℕ)
    (e : ∀ i, (Fin (n i) → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (P i))
    (β : ∀ i, (Fin (n i) → ℝ) → ℝ) (nP : I → ℕ) (T : I → I → Type)
    (cw : ∀ i i', T i i' → (M i' ⟶ M i)) (π : ∀ i, P i ⟶ M i)
    (hw : ∀ i i' t, MeasurePreserving
      (fun x => (e i').symm (realWeylParameter (l i) (cw i i' t) (π i') (e i x)))
      volume volume)
    (Mop : ∀ i i', T i i' → (Fin (n i) → ℝ) →
      inducedHilbertSpace K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i) (μM i) (e i)
          (β i) →L[ℂ]
        inducedHilbertSpace K (hK i').isCompact rho hsmooth hcalc (p i') (iU i') (l i')
          (μM i') (e i') (β i')) :
    CompleteSpace (symmetricFamilySpace hK rho hsmooth hcalc iU l μM n e β nP T cw π hw Mop) := by
  have : ∀ i, CompleteSpace (inducedHilbertSpace K (hK i).isCompact rho hsmooth hcalc (p i)
      (iU i) (l i) (μM i) (e i) (β i)) := fun i => by
    unfold inducedHilbertSpace
    infer_instance
  exact (isClosed_symmetricFamilySpace hK rho hsmooth hcalc iU l μM n e β nP T cw π hw
    Mop).completeSpace_coe

end Families

/-- `SpectralTransformStatement` follows from the five inputs of
`Langlands.Global.AdelicSpectralTransformInputs`: the existence of the operators `M(w, λ)` on the
imaginary axis, the density of smooth compactly supported families in `L̂`, the existence of
Eisenstein continuations holomorphic near the imaginary axis, the Gram identity for wave
packets, and the approximation of right translates of wave packets by wave packets. -/
def SpectralTransformReductionStatement : Prop :=
  ImaginaryIntertwiningExistenceStatement → SymmetricFamilyDensityStatement →
    EisensteinImaginaryContinuationStatement → SymmetricFamilyGramStatement →
    WavePacketTranslationStatement → SpectralTransformStatement

set_option synthInstance.maxHeartbeats 400000 in
/-- Proof of `SpectralTransformReductionStatement`. -/
theorem spectralTransformReduction : SpectralTransformReductionStatement := by
  intro S1 S2 S3' S3 S4 F _ _ G _ _ _ I _ P M U A _ _ _ _ p _ iU l _ a r _ _ _ hA hT π hG hU
    hLevi hπ K hK N d rho hsmooth hcalc hKmax hrho μM _ hμM n e β hβ T _ w cw hwc hinj hsurj hw
    nP μG
  have : ∀ i, LocallyOfFiniteType (P i).X.hom := fun i =>
    IsClosedSubgroup.locallyOfFiniteType (j := p i)
      (inferInstance : IsClosedImmersion (p i).hom.hom.left)
  refine ⟨?_, fun Mop hMop => ?_⟩
  · choose Mop hMop using fun i i' (t : T i i') => S1 F G (P i) (M i) (U i) (P i') (M i')
      (U i') (A i) (A i') (p i) (iU i) (l i) (a i) (r i) (hA i) (hT i) (π i) (p i') (iU i')
      (l i') (a i') (r i') (hA i') (hT i') (π i') hG (hU i) (hU i') (hLevi i) (hLevi i')
      (hπ i) (hπ i') K (hK i) (hK i') rho hsmooth hcalc hKmax hrho (μM i) (μM i') (hμM i)
      (hμM i') (e i) (e i') (β i) (β i') (hβ i) (hβ i') (w i i' t) (cw i i' t) (hwc i i' t)
      (hw i i' t)
    exact ⟨Mop, hMop⟩
  have := completeSpace_symmetricFamilySpace hK rho hsmooth hcalc iU l μM n e β nP T cw π hw Mop
  have hτ : ∀ y : AdelicGroupPoints F G, MeasurePreserving
      (fun x : RationalQuotient F G => LeftCosetSpace.mk (rationalSubgroup F G) (x.out * y))
      μG μG := by
    intro y
    have hz : (fun x : RationalQuotient F G =>
        LeftCosetSpace.mk (rationalSubgroup F G) (x.out * y)) =
        LeftCosetSpace.rightTranslate (rationalSubgroup F G) y := by
      funext z
      rw [← LeftCosetSpace.rightTranslate_mk]
      congr 1
      exact Quotient.out_eq z
    rw [hz]
    have := (adelicHaarUnimodularity.{0}).2 F G hG
    exact LeftCosetSpace.measurePreserving_rightTranslate_discrete _ _ _ y
  have hdensity := S2 F G I P M U A p iU l a r hA hT π hG hU hLevi hπ K hK rho hsmooth hcalc
    hKmax hrho μM hμM n e β hβ T w cw hwc hinj hsurj hw Mop hMop
  refine (exists_linearIsometry_of_wavePackets_submodule (m := μG)
    (E := spectralFamilySpace hK rho hsmooth hcalc iU l μM n e β nP)
    (symmetricFamilySpace hK rho hsmooth hcalc iU l μM n e β nP T cw π hw Mop) _ hdensity
    (fun Φ f => ∃ (k : I → ℕ) (v : ∀ i, Fin (k i) → AdelicGroupPoints F G → ℂ)
      (c : ∀ i, Fin (k i) → (Fin (n i) → ℝ) → ℂ)
      (E : ∀ i, Fin (k i) → ComplexCharacterParameter F (P i) → AdelicGroupPoints F G → ℂ)
      (D : ∀ i, Set (ComplexCharacterParameter F (P i))),
      IsSmoothCompactFamily hK rho hsmooth hcalc iU l μM n e β nP k v c Φ.1 ∧
      (∀ i, IsEisensteinContinuation (hK i) (r i) (hA i) (hT i) (v i) (E i) (D i)) ∧
      f = wavePacketSum e nP c E) ?_ ?_ _ hτ ?_).elim ?_
  · rintro Φ ⟨k, v, c, hΦ⟩
    choose E D hED using fun i => S3' F G (P i) (M i) (U i) (A i) (p i) (iU i) (l i) (a i)
      (r i) (hA i) (hT i) hG (hU i) K (hK i) rho hsmooth hcalc hKmax hrho (k i) (v i)
      (fun j => hΦ.1 i j)
    exact ⟨_, k, v, c, E, D, hΦ, hED, rfl⟩
  · rintro Φ f Φ' f' ⟨k, v, c, E, D, hΦ, hE, rfl⟩ ⟨k', v', c', E', D', hΦ', hE', rfl⟩
    exact S3 F G I P M U A p iU l a r hA hT π hG hU hLevi hπ K hK rho hsmooth hcalc hKmax
      hrho μM hμM n e β hβ T w cw hwc hinj hsurj hw Mop hMop Φ Φ' k v c E D k' v' c' E' D' hΦ
      hE hΦ' hE'
  · rintro Φ f ⟨k, v, c, E, D, hΦ, hE, rfl⟩ y ε hε
    have h4 := S4 F G I P M U A p iU l a r hA hT π hG hU hLevi hπ K hK rho hsmooth hcalc hKmax
      hrho μM hμM n e β hβ T w cw hwc hinj hsurj hw Mop hMop
    have h5 := h4 Φ k v c E D hΦ hE
    have h6 := h5 y ε hε
    obtain ⟨Φ', k', v', c', E', D', hΦ', hE', hlt⟩ := h6
    exact ⟨Φ', _, ⟨k', v', c', E', D', hΦ', hE', rfl⟩, hlt⟩
  · rintro Ebar ⟨hf, hc, ht⟩
    exact ⟨Ebar, hdensity, fun Φ k v c hΦ E D hD hmer hreg =>
      hf Φ _ ⟨k, v, c, E, D, hΦ, fun i => ⟨hD i, hmer i, hreg i⟩, rfl⟩, hc, ht⟩

end Langlands.Global

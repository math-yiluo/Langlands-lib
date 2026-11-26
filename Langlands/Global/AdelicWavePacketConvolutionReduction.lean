import Langlands.Global.AdelicEisensteinContinuationLocalFrechet
import Langlands.Global.AdelicInducedConvolutionFiniteSpanStatement
import Langlands.Global.AdelicWavePacketLeftInvariance
import Langlands.Global.AdelicEisensteinConvergenceProof
import Langlands.Global.AdelicSymmetricFamilyDensity

/-! # Reduction of the convolution stability of wave packets

`WavePacketConvolutionStatement` follows from the meromorphic continuation of Eisenstein series
(`EisensteinMeromorphicContinuationStatement`), their holomorphy on the imaginary axis
(`EisensteinImaginaryAxisHolomorphyStatement`) and the finite span of the integrated induced
action (`InducedConvolutionFiniteSpanStatement`). -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set Topology
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-! ## Entire functions -/

/-- Functions holomorphic in linear coordinates on the whole space are meromorphic in
coordinates with domain the whole space. -/
theorem isMeromorphicInCoordinatesOn_univ_of_isHolomorphicInCoordinatesOn {X : Type*}
    [AddCommGroup X] [Module ℂ X] {b : X → ℂ} (hb : IsHolomorphicInCoordinatesOn b univ) :
    IsMeromorphicInCoordinatesOn b univ := by
  have := hb.1
  refine isMeromorphicInCoordinatesOn_univ fun n e => ?_
  have h := differentiableOn_of_isHolomorphicOn (hb.2 n e)
  rw [preimage_univ] at h
  exact differentiableOn_univ.mp h

section Key

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {iU : U ⟶ P} {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

/-- Given the meromorphic continuation of Eisenstein series, a pointwise continuation `E` of
the Eisenstein series of an automorphic form on `U(𝔸) M(F) \ G(𝔸)` is jointly continuous in
the parameter and the point of `G(𝔸)` near every parameter of its domain of holomorphy. -/
theorem exists_continuousOn_eisensteinContinuation
    (hMero : EisensteinMeromorphicContinuationStatement.{0}) (hG : IsConnectedReductive G)
    (hUR : LeviSubgroup.IsGeometricUnipotentRadical iU) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (hKmax : IsMaximalCompactSubgroup F G K)
    {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho φ)
    {E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ}
    {D : Set (ComplexCharacterParameter F P)}
    (hE : ∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D)
    (hreg : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hK.eisensteinSeries φ lam)
    {m : ℕ} (e₀ : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P)
    {lam₀ : ComplexCharacterParameter F P} (hlam₀ : lam₀ ∈ D) :
    ∃ T : Set (Fin m → ℂ), IsOpen T ∧ e₀.symm lam₀ ∈ T ∧ T ⊆ e₀ ⁻¹' D ∧
      ContinuousOn (fun q : (Fin m → ℂ) × AdelicGroupPoints F G => E (e₀ q.1) q.2)
        (T ×ˢ univ) := by
  obtain ⟨W, hs₀, R, L, f, Df, hf, hfD⟩ :=
    exists_local_frechet_of_eisensteinContinuation r hA hT hK hMero hG hUR rho hN hrho hsmooth
      hcalc hKmax hφ hE hreg e₀ (e₀.symm lam₀)
  have hO : IsOpen (e₀ ⁻¹' D) := ((hE 1).2 m e₀).1
  have hΦ : ∀ g, DifferentiableOn ℂ (fun s => E (e₀ s) g) (e₀ ⁻¹' D) := fun g =>
    differentiableOn_of_isHolomorphicOn ((hE g).2 m e₀).2.2.1
  exact continuousOn_of_local_frechet hf hfD hO hΦ hs₀ (by simpa using hlam₀)

/-- **Continuation of the convolution identity.** Suppose `I(λ, φ) v = ∑ i, b i λ • w i` for all
`λ`, with `b i` entire and `w i` automorphic on `U(𝔸) M(F) \ G(𝔸)`. Then, given the meromorphic
continuation of Eisenstein series, for continuations `E` of `E(v, ·)` and `E' i` of `E(w i, ·)`,
`R(φ)(E λ) = ∑ i, b i λ • E' i λ` at every `λ` where `E` and all `E' i` are holomorphic. -/
theorem rightConvolution_eisensteinContinuation_eq
    (hMero : EisensteinMeromorphicContinuationStatement.{0}) (hG : IsConnectedReductive G)
    (hUR : LeviSubgroup.IsGeometricUnipotentRadical iU) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (hKmax : IsMaximalCompactSubgroup F G K)
    {v : AdelicGroupPoints F G → ℂ}
    (hv : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho v)
    {E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ}
    {D : Set (ComplexCharacterParameter F P)}
    (hE : ∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D)
    (hreg : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hK.eisensteinSeries v lam)
    {φ : AdelicGroupPoints F G → ℂ} (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    {m' : ℕ} {w : Fin m' → AdelicGroupPoints F G → ℂ}
    (hw : ∀ i, IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho (w i))
    {E' : Fin m' → ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ}
    {D' : Set (ComplexCharacterParameter F P)}
    (hE' : ∀ i g, IsMeromorphicInCoordinatesOn (fun lam => E' i lam g) D')
    (hreg' : ∀ i, ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
      E' i lam = hK.eisensteinSeries (w i) lam)
    {b : Fin m' → ComplexCharacterParameter F P → ℂ}
    (hb : ∀ i, IsHolomorphicInCoordinatesOn (b i) univ)
    (hspan : ∀ lam, hK.inducedConvolution lam φ v = fun x => ∑ i, b i lam * w i x)
    {lam₀ : ComplexCharacterParameter F P} (h₀ : lam₀ ∈ D ∩ D') (g : AdelicGroupPoints F G) :
    rightConvolution F G φ (E lam₀) g = ∑ i, b i lam₀ * E' i lam₀ g := by
  classical
  have := finiteDimensional_complexCharacterParameter r hG
  let m := Module.finrank ℂ (ComplexCharacterParameter F P)
  let e₀ : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P :=
    (Module.finBasis ℂ (ComplexCharacterParameter F P)).equivFun.symm
  -- meromorphy of the left side
  obtain ⟨U₀, hU₀⟩ := exists_isMeromorphicOn_rightConvolution (Φ := fun s => E (e₀ s))
    (fun s₀ => exists_local_frechet_of_eisensteinContinuation r hA hT hK hMero hG hUR rho hN hrho
      hsmooth hcalc hKmax hv hE hreg e₀ s₀) hφc hφs
  have hLm : IsMeromorphicInCoordinatesOn (fun lam => rightConvolution F G φ (E lam) g)
      (e₀ '' U₀) :=
    isMeromorphicInCoordinatesOn_of_coordinates e₀ (by
      rw [e₀.injective.preimage_image]
      exact hU₀ g)
  -- meromorphy of the right side
  have hbm : ∀ i, IsMeromorphicInCoordinatesOn (b i) univ := fun i =>
    isMeromorphicInCoordinatesOn_univ_of_isHolomorphicInCoordinatesOn (hb i)
  have hprod : ∀ i, IsMeromorphicInCoordinatesOn (fun lam => b i lam * E' i lam g) (univ ∩ D') :=
    fun i => (hbm i).mul (hE' i g)
  set S : Set (ComplexCharacterParameter F P) := ⋂ _j : Fin m', univ ∩ D' with hSdef
  have hS : IsOpenDenseInCoordinates S := isOpenDenseInCoordinates_iInter fun j => by
    rw [univ_inter]
    exact (hE' j g).isOpenDenseInCoordinates
  have hRm : IsMeromorphicInCoordinatesOn (fun lam => ∑ i, b i lam * E' i lam g) S := by
    have h := IsMeromorphicInCoordinatesOn.sum Finset.univ hS
      (fun i _ => (hprod i).congr_mono hS (iInter_subset _ i) fun _ _ => rfl)
    convert h using 1
    funext lam
    simp only [Finset.sum_apply]
  -- joint continuity of `E` near `λ₀`
  obtain ⟨T, hTo, hs₀T, -, hTc⟩ := exists_continuousOn_eisensteinContinuation r hA hT hK hMero hG
    hUR rho hN hrho hsmooth hcalc hKmax hv hE hreg e₀ h₀.1
  -- agreement on a regular region
  obtain ⟨RE, hRE⟩ := hreg
  choose R' hR' using hreg'
  obtain ⟨Rv, hRv⟩ := eisensteinAbsoluteConvergence F G P M U A p iU l a r hA hT hG hUR K hK rho
    hsmooth hcalc v hKmax hrho hv
  choose Rw hRw using fun i => eisensteinAbsoluteConvergence F G P M U A p iU l a r hA hT hG hUR
    K hK rho hsmooth hcalc (w i) hKmax hrho (hw i)
  set Rs := max (max RE Rv) (max (∑ j, |R' j|) (∑ j, |Rw j|))
  have hle : ∀ (f : Fin m' → ℝ) i, f i ≤ ∑ j, |f j| := fun f i =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |f j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i))
  have hagree : ∀ lam, r.IsRegularParameter hA hT Rs lam →
      rightConvolution F G φ (E lam) g = ∑ i, b i lam * E' i lam g := by
    intro lam hlam
    have hreg_of : ∀ {R'' : ℝ}, R'' ≤ Rs → r.IsRegularParameter hA hT R'' lam :=
      fun h => isRegularParameter_mono r hA hT h hlam
    rw [hRE lam (hreg_of ((le_max_left _ _).trans (le_max_left _ _)))]
    obtain ⟨bv, hbv, hbvb⟩ := hRv ((fun h => g * h) '' tsupport φ)
      (hφs.isCompact.image (continuous_const.mul continuous_id)) m e₀ {e₀.symm lam}
      isCompact_singleton (fun s hs => by
        rw [mem_singleton_iff.mp hs, LinearEquiv.apply_symm_apply]
        exact hreg_of ((le_max_right _ _).trans (le_max_left _ _)))
    rw [hK.rightConvolution_eisensteinSeries_eq_inducedConvolution hφc hφs hv.2.1.1 lam g hbv
      (fun c h hh => by simpa using hbvb c (g * h) ⟨h, hh, rfl⟩ (e₀.symm lam) rfl), hspan lam]
    refine (hK.eisensteinSeries_sum_mul w (fun i => b i lam) lam g (fun i => ?_)).trans ?_
    · obtain ⟨bw, hbw, hbwb⟩ := hRw i {g} isCompact_singleton m e₀ {e₀.symm lam}
        isCompact_singleton (fun s hs => by
          rw [mem_singleton_iff.mp hs, LinearEquiv.apply_symm_apply]
          exact hreg_of ((hle Rw i).trans ((le_max_right _ _).trans (le_max_right _ _))))
      exact Summable.of_norm_bounded hbw fun c => by simpa using hbwb c g rfl (e₀.symm lam) rfl
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [hR' i lam (hreg_of ((hle R' i).trans ((le_max_left _ _).trans (le_max_right _ _))))]
  have heqOn := r.eqOn_of_regularParameter hA hT hG hLm hRm Rs hagree
  -- continuity of both sides near `λ₀` and density of the common domain
  have hLc : ContinuousOn (fun s => rightConvolution F G φ (E (e₀ s)) g) T := by
    have hc : ContinuousOn (fun q : (Fin m → ℂ) × AdelicGroupPoints F G =>
        φ q.2 * E (e₀ q.1) (g * q.2)) (T ×ˢ univ) := by
      refine (hφc.comp continuous_snd).continuousOn.mul ?_
      exact hTc.comp (continuous_fst.prodMk (continuous_const.mul continuous_snd)).continuousOn
        fun q hq => ⟨hq.1, mem_univ _⟩
    show ContinuousOn (fun s => ∫ h, φ h * E (e₀ s) (g * h)
      ∂(Measure.haar : Measure (AdelicGroupPoints F G))) T
    exact continuousOn_integral_of_compact_support
      (f := fun s h => φ h * E (e₀ s) (g * h)) hφs.isCompact hc
      fun s h _ hh => by simp [image_eq_zero_of_notMem_tsupport hh]
  have hRc : ContinuousOn (fun s => ∑ i, b i (e₀ s) * E' i (e₀ s) g) (e₀ ⁻¹' S) := by
    refine continuousOn_finsetSum _ fun i _ => ?_
    have hbc : Continuous fun s => b i (e₀ s) := by
      have h := differentiableOn_of_isHolomorphicOn ((hb i).2 m e₀)
      rw [preimage_univ] at h
      exact (differentiableOn_univ.mp h).continuous
    have hEc := (differentiableOn_of_isHolomorphicOn ((hE' i g).2 m e₀).2.2.1).continuousOn
    exact hbc.continuousOn.mul
      (hEc.mono (preimage_mono ((iInter_subset _ i).trans inter_subset_right)))
  have hO := (hLm.isOpenDenseInCoordinates.inter hS) m e₀
  have hdense : T ∩ e₀ ⁻¹' S ⊆ closure (T ∩ e₀ ⁻¹' S ∩ e₀ ⁻¹' (e₀ '' U₀ ∩ S)) := by
    intro s hs
    exact (hTo.inter (hS m e₀).1).inter_closure ⟨hs, hO.2 s⟩
  have hs₀S : e₀.symm lam₀ ∈ e₀ ⁻¹' S := by
    simp only [mem_preimage, LinearEquiv.apply_symm_apply, hSdef, mem_iInter]
    exact fun _ => ⟨mem_univ _, h₀.2⟩
  have key := EqOn.of_subset_closure (f := fun s => rightConvolution F G φ (E (e₀ s)) g)
    (g := fun s => ∑ i, b i (e₀ s) * E' i (e₀ s) g) (fun s hs => heqOn hs.2)
    (hLc.mono inter_subset_left) (hRc.mono inter_subset_right) inter_subset_left hdense
    ⟨hs₀T, hs₀S⟩
  simpa using key

/-- Given the meromorphic continuation of Eisenstein series, a pointwise continuation `E` whose
domain of holomorphy contains the imaginary axis is jointly continuous on
`i(X^*(P) ⊗ ℝ) × G(𝔸)`, read in real coordinates `e`. -/
theorem continuous_eisensteinContinuation_imaginary
    (hMero : EisensteinMeromorphicContinuationStatement.{0}) (hG : IsConnectedReductive G)
    (hUR : LeviSubgroup.IsGeometricUnipotentRadical iU) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (hKmax : IsMaximalCompactSubgroup F G K)
    {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho φ)
    {E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ}
    {D : Set (ComplexCharacterParameter F P)}
    (hE : ∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D)
    (hreg : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hK.eisensteinSeries φ lam)
    (hD : range (imaginaryParameter F P) ⊆ D) {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) :
    Continuous (fun q : (Fin n → ℝ) × AdelicGroupPoints F G =>
      E (imaginaryParameter F P (e q.1)) q.2) := by
  have := finiteDimensional_complexCharacterParameter r hG
  let m := Module.finrank ℂ (ComplexCharacterParameter F P)
  let e₀ : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P :=
    (Module.finBasis ℂ (ComplexCharacterParameter F P)).equivFun.symm
  let Aℝ : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℂ) :=
    (e₀.symm.toLinearMap.restrictScalars ℝ) ∘ₗ (imaginaryParameter F P) ∘ₗ e.toLinearMap
  have hAc : Continuous Aℝ := LinearMap.continuous_of_finiteDimensional Aℝ
  have hAe : ∀ x, e₀ (Aℝ x) = imaginaryParameter F P (e x) := fun x => by
    simp only [Aℝ, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, y₀⟩
  obtain ⟨T, hTo, hT₀, -, hTc⟩ := exists_continuousOn_eisensteinContinuation r hA hT hK hMero hG
    hUR rho hN hrho hsmooth hcalc hKmax hφ hE hreg e₀ (hD ⟨e x₀, rfl⟩)
  have hx₀ : Aℝ x₀ ∈ T := by
    rw [show Aℝ x₀ = e₀.symm (imaginaryParameter F P (e x₀)) by
      rw [← hAe x₀, LinearEquiv.symm_apply_apply]]
    exact hT₀
  have hca : ContinuousAt (fun q : (Fin m → ℂ) × AdelicGroupPoints F G => E (e₀ q.1) q.2)
      (Aℝ x₀, y₀) :=
    hTc.continuousAt (prod_mem_nhds (hTo.mem_nhds hx₀) Filter.univ_mem)
  have hf : Continuous fun q : (Fin n → ℝ) × AdelicGroupPoints F G => (Aℝ q.1, q.2) :=
    (hAc.comp continuous_fst).prodMk continuous_snd
  have h2 : ContinuousAt (fun q : (Fin n → ℝ) × AdelicGroupPoints F G => E (e₀ (Aℝ q.1)) q.2)
      (x₀, y₀) :=
    ContinuousAt.comp (g := fun q : (Fin m → ℂ) × AdelicGroupPoints F G => E (e₀ q.1) q.2)
      (f := fun q : (Fin n → ℝ) × AdelicGroupPoints F G => (Aℝ q.1, q.2)) hca hf.continuousAt
  have h3 : (fun q : (Fin n → ℝ) × AdelicGroupPoints F G =>
      E (imaginaryParameter F P (e q.1)) q.2) =
      fun q : (Fin n → ℝ) × AdelicGroupPoints F G => E (e₀ (Aℝ q.1)) q.2 :=
    funext fun q => by rw [hAe]
  rw [h3]
  exact h2

end Key

section Packets

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- Right convolution by a continuous compactly supported `φ` passes under a packet integral
`y ↦ ∫ ∑ j, c j x * Φ j x y dν(x)` with continuous compactly supported coefficients and jointly
continuous `Φ j` (Fubini's theorem for continuous functions with compact support). -/
theorem rightConvolution_packet_eq {n k : ℕ} {ν : Measure (Fin n → ℝ)}
    [IsFiniteMeasureOnCompacts ν] {φ : AdelicGroupPoints F G → ℂ} (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) {c : Fin k → (Fin n → ℝ) → ℂ} (hcc : ∀ j, Continuous (c j))
    (hcs : ∀ j, HasCompactSupport (c j)) {Φ : Fin k → (Fin n → ℝ) → AdelicGroupPoints F G → ℂ}
    (hΦ : ∀ j, Continuous (fun q : (Fin n → ℝ) × AdelicGroupPoints F G => Φ j q.1 q.2))
    (g : AdelicGroupPoints F G) :
    rightConvolution F G φ (fun y => ∫ x, ∑ j, c j x * Φ j x y ∂ν) g =
      ∫ x, ∑ j, c j x * rightConvolution F G φ (Φ j x) g ∂ν := by
  have hcont : Continuous (Function.uncurry fun (h : AdelicGroupPoints F G) (x : Fin n → ℝ) =>
      φ h * ∑ j, c j x * Φ j x (g * h)) := by
    refine (hφc.comp continuous_fst).mul (continuous_finsetSum _ fun j _ => ?_)
    exact ((hcc j).comp continuous_snd).mul
      ((hΦ j).comp (continuous_snd.prodMk (continuous_const.mul continuous_fst)))
  have hsupp : HasCompactSupport (Function.uncurry fun (h : AdelicGroupPoints F G)
      (x : Fin n → ℝ) => φ h * ∑ j, c j x * Φ j x (g * h)) := by
    refine HasCompactSupport.intro (hφs.isCompact.prod
      (isCompact_iUnion fun j => (hcs j).isCompact)) fun q hq => ?_
    change φ q.1 * ∑ j, c j q.2 * Φ j q.2 (g * q.1) = 0
    by_cases h1 : q.1 ∈ tsupport φ
    · have h2 : q.2 ∉ ⋃ j, tsupport (c j) := fun h2 => hq ⟨h1, h2⟩
      rw [Finset.sum_eq_zero fun j _ => by
        rw [image_eq_zero_of_notMem_tsupport fun h => h2 (mem_iUnion.mpr ⟨j, h⟩), zero_mul],
        mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul]
  calc rightConvolution F G φ (fun y => ∫ x, ∑ j, c j x * Φ j x y ∂ν) g
      = ∫ h, ∫ x, φ h * ∑ j, c j x * Φ j x (g * h) ∂ν
          ∂(Measure.haar : Measure (AdelicGroupPoints F G)) := by
        unfold rightConvolution
        refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
        exact (integral_const_mul _ _).symm
    _ = ∫ x, ∫ h, φ h * ∑ j, c j x * Φ j x (g * h)
          ∂(Measure.haar : Measure (AdelicGroupPoints F G)) ∂ν :=
        integral_integral_swap_of_hasCompactSupport hcont hsupp
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        have hint : ∀ j, Integrable (fun h => c j x * (φ h * Φ j x (g * h)))
            (Measure.haar : Measure (AdelicGroupPoints F G)) := fun j =>
          ((continuous_const.mul (hφc.mul ((hΦ j).comp ((continuous_const.prodMk
            (continuous_const.mul continuous_id))))))).integrable_of_hasCompactSupport
            hφs.mul_right.mul_left
        simp only [Finset.mul_sum, mul_left_comm (φ _)]
        rw [integral_finsetSum _ fun j _ => hint j]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul]
        rfl

end Packets

section Assembly

/-- **Convolution stability of wave packets, conditionally.** Given the meromorphic continuation
of Eisenstein series, their holomorphy on the imaginary axis and the finite span of the
integrated induced action, the right convolution of a wave packet by a test function of
`IsLeftFiniteTestFunction` is a wave packet. -/
theorem isWavePacket_rightConvolution_of_premises
    (hMero : EisensteinMeromorphicContinuationStatement.{0})
    (hHolo : EisensteinImaginaryAxisHolomorphyStatement)
    (hSpan : InducedConvolutionFiniteSpanStatement)
    {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G) {K : Subgroup (AdelicGroupPoints F G)} {N d : ℕ}
    {rho : MatrixRepresentation G (Fin N)} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {hcalc : AdelicDifferentialCommutator F G hsmooth}
    (hKmax : IsMaximalCompactSubgroup F G K) (hrho : IsClosedSubgroup rho)
    (hP₀ : ∃ (P₀ : GroupScheme (Spec (CommRingCat.of F))) (_ : IsAffine P₀.X.left)
      (p₀ : P₀ ⟶ G) (_ : IsClosedImmersion p₀.hom.hom.left),
      IsMinimalParabolicSubgroup p₀ ∧ IsIwasawaCompact p₀ K)
    {Θ : AdelicGroupPoints F G → ℂ} (hΘ : IsWavePacket F G K rho hsmooth hcalc Θ)
    {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftFiniteTestFunction F G (K.comap (ofInfinite F G).toMonoidHom) φ) :
    IsWavePacket F G K rho hsmooth hcalc (rightConvolution F G φ Θ) := by
  classical
  have hφc : Continuous φ := hφ.1
  have hφs : HasCompactSupport φ := hφ.2.1
  obtain ⟨P, M, U, A, iPa, iMa, iMl, iUa, p, ip, iU, l, iUp, a, r, i1, i2, i3, hA, hT, hU, hK, n,
    e, k, v, c, E, D, hv, hc, himag, hE, hreg, rfl⟩ := hΘ
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- `N = 0`: `G(𝔸)` is trivial and `R(φ)` is multiplication by `∫ φ`
    have := subsingleton_adelicGroupPoints_of_rank_zero rho hrho
    set c₀ : ℂ := ∫ h, φ h ∂(Measure.haar : Measure (AdelicGroupPoints F G))
    refine ⟨P, M, U, A, iPa, iMa, iMl, iUa, p, ip, iU, l, iUp, a, r, i1, i2, i3, hA, hT, hU, hK,
      n, e, k, v, fun j x => c₀ * c j x, E, D, hv,
      fun j => ⟨contDiff_const.mul (hc j).1, (hc j).2.mul_left⟩, himag, hE, hreg, ?_⟩
    funext g
    have h1 : ∀ h : AdelicGroupPoints F G, g * h = g := fun h => Subsingleton.elim _ _
    simp only [rightConvolution, h1]
    rw [integral_mul_const, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Finset.mul_sum, mul_assoc]
    rfl
  · -- finite spans of the convolved inducing data
    choose mj wj bj hwj hbj hspanj using fun j => hSpan F G P M U A p iU l a r hA hT hG hU K hK
      rho hsmooth hcalc hKmax hrho hP₀ (v j) (hv j) φ hφ
    let σeq : (Σ j : Fin k, Fin (mj j)) ≃ Fin (∑ j, mj j) := finSigmaFinEquiv
    let vσ : (Σ j : Fin k, Fin (mj j)) → AdelicGroupPoints F G → ℂ := fun σ => wj σ.1 σ.2
    let v' : Fin (∑ j, mj j) → AdelicGroupPoints F G → ℂ := fun i => vσ (σeq.symm i)
    have hv' : ∀ i, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (v' i) :=
      fun i => hwj _ _
    -- continuations of the new Eisenstein series, holomorphic on the imaginary axis
    obtain ⟨E', D', himag', hE', hreg'⟩ := eisensteinImaginaryContinuationBridge hMero hHolo
      eisensteinAbsoluteConvergence F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc
      hKmax hrho _ v' hv'
    have hbm : ∀ j i, IsMeromorphicInCoordinatesOn (bj j i) univ := fun j i =>
      isMeromorphicInCoordinatesOn_univ_of_isHolomorphicInCoordinatesOn (hbj j i)
    let cσ : (Σ j : Fin k, Fin (mj j)) → (Fin n → ℝ) → ℂ := fun σ x =>
      c σ.1 x * bj σ.1 σ.2 (imaginaryParameter F P (e x))
    let c' : Fin (∑ j, mj j) → (Fin n → ℝ) → ℂ := fun i => cσ (σeq.symm i)
    refine ⟨P, M, U, A, iPa, iMa, iMl, iUa, p, ip, iU, l, iUp, a, r, i1, i2, i3, hA, hT, hU, hK,
      n, e, _, v', c', E', D', hv', fun i => ⟨?_, ?_⟩, himag', hE', hreg', ?_⟩
    · exact (hc _).1.mul (contDiff_comp_imaginaryParameter e (hbm _ _) (subset_univ _))
    · exact (hc _).2.mul_right
    · -- the continued convolution identity on the imaginary axis
      have hkey : ∀ j x g, rightConvolution F G φ (E j (imaginaryParameter F P (e x))) g =
          ∑ i : Fin (mj j), bj j i (imaginaryParameter F P (e x)) *
            E' (σeq ⟨j, i⟩) (imaginaryParameter F P (e x)) g := fun j x g =>
        rightConvolution_eisensteinContinuation_eq r hA hT hK hMero hG hU rho hN hrho hsmooth
          hcalc hKmax (hv j).1 (hE j) (hreg j) hφc hφs (w := fun i => wj j i)
          (fun i => (hwj j i).1) (E' := fun i => E' (σeq ⟨j, i⟩)) (fun i g => hE' _ g)
          (fun i => by
            obtain ⟨R, hR⟩ := hreg' (σeq ⟨j, i⟩)
            refine ⟨R, fun lam hlam => ?_⟩
            rw [hR lam hlam]
            show hK.eisensteinSeries (vσ (σeq.symm (σeq ⟨j, i⟩))) lam = _
            rw [Equiv.symm_apply_apply])
          (hbj j) (hspanj j) ⟨himag ⟨e x, rfl⟩, himag' ⟨e x, rfl⟩⟩ g
      have hfin : IsFiniteMeasureOnCompacts (spectralMeasure n) := by
        unfold spectralMeasure
        refine IsFiniteMeasureOnCompacts.smul _ (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 ?_))
        exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
      funext g
      rw [rightConvolution_packet_eq hφc hφs (fun j => (hc j).1.continuous) (fun j => (hc j).2)
        (fun j => continuous_eisensteinContinuation_imaginary r hA hT hK hMero hG hU rho hN hrho
          hsmooth hcalc hKmax (hv j).1 (hE j) (hreg j) himag e) g]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      have hc' : ∀ σ, c' (σeq σ) = cσ σ := fun σ => by
        show cσ (σeq.symm (σeq σ)) = cσ σ
        rw [Equiv.symm_apply_apply]
      dsimp only
      rw [← σeq.sum_comp]
      simp only [hc']
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hkey j x g, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [cσ]
      ring

/-- The meromorphic continuation of Eisenstein series (Bernstein–Lapid, Theorem 2.3 (1), in the
Fréchet form of their Corollary 8.6), their holomorphy on the imaginary axis (Lapid 2011,
Proposition 6) and the finite span of the integrated induced action (Mœglin–Waldspurger I.2.17
and IV.1.7 (*)) imply `WavePacketConvolutionStatement`. -/
def WavePacketConvolutionReductionStatement : Prop :=
  EisensteinMeromorphicContinuationStatement.{0} → EisensteinImaginaryAxisHolomorphyStatement →
    InducedConvolutionFiniteSpanStatement → WavePacketConvolutionStatement

theorem wavePacketConvolutionReduction : WavePacketConvolutionReductionStatement := by
  intro hMero hHolo hSpan F _ _ G _ _ _ hG K N d rho hsmooth hcalc hKmax hrho hP₀ Θ hΘ
  exact ⟨wavePacketLeftRationalInvariance F G hG K rho hsmooth hcalc Θ hΘ, fun φ hφ =>
    isWavePacket_rightConvolution_of_premises hMero hHolo hSpan hG hKmax hrho hP₀ hΘ hφ⟩

end Assembly

end Langlands.Global
